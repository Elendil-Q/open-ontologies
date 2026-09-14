//! What a change to the reasoner's budgets costs, measured rather than asserted.
//!
//! `src/tableaux.rs` carries a cost measurement in a doc comment — "a
//! 20-ontology corpus went from 67s to over 600s" — and until this file there
//! was no way to reproduce it. A number in a comment that nobody can re-run is a
//! number that goes stale silently, and the budget it justifies is exactly the
//! kind of setting that gets changed by someone who cannot check what it costs.
//!
//! The corpus is fixed and is in the repository: every `*.ttl` under a
//! `case-studies/**/ontology/` directory, plus the two core ontologies that live
//! one level up, minus `occupational-map.ttl`, which is 5.7 MB and is already
//! excluded from the certificate corpus for the same reason. That is twenty
//! files.
//!
//! IGNORED by default, because it takes minutes and measures wall clock, which
//! is not a thing an assertion should be built on. Run it deliberately:
//!
//! ```text
//! cargo test --release --test reasoner_budget_corpus_bench -- --ignored --nocapture
//! ```
//!
//! It prints per-ontology wall time, the phases that ran out of budget, and the
//! total. Compare two totals; do not compare a total against a number in a
//! comment written on a different machine.
//!
//! MEASURED, 14 September 2026, `cargo test` debug profile, this machine,
//! running the two builds back to back so they share whatever load the machine
//! was under — which matters more than it sounds: an earlier pair of runs
//! differed by a factor of four purely because a release build was competing
//! with one of them. The change under test is `phase_deadline_within`, which
//! puts every phase under the `classify_timeout_ms` ceiling, plus the widening
//! of definition realization to untyped individuals.
//!
//! | corpus | before | after |
//! |---|---|---|
//! | twenty case-study ontologies, none reaching a budget | 0.10s | 0.10s |
//! | ten that do, two of them exhausting one | 64.53s | 63.84s |
//!
//! Unchanged, and it has to be: at the shipped settings
//! `min(now + 10 000 ms, now + 180 000 ms)` is the same instant the phase
//! budget alone produced, so the intersection is arithmetic and not work. The
//! difference shows up only when `classify_timeout_ms` is set below five times
//! `tableaux_test_timeout_ms`, which is when it is meant to.

mod common;

use std::sync::Arc;
use std::time::Instant;

use open_ontologies::graph::GraphStore;
use open_ontologies::reason::Reasoner;

/// The ontologies in this repository that actually exhaust a reasoner budget.
///
/// The case-study corpus below is broad and EASY: measured here it runs in under
/// three seconds and not one of the twenty hits a cap, so a change to the budget
/// logic is invisible in it. A cost measurement over a corpus that never reaches
/// the thing being measured is the shape of number this project exists to
/// refuse, so this second list exists and is the one that answers the question.
/// `nominals_blowup.ttl` is in `benchmark/reasoner/regressions/` for exactly this
/// reason: `owl:hasValue` is approximated by an atomic concept named after the
/// individual, and a class defined by one per department is what makes the
/// tableau branch.
const HARD: &[&str] = &[
    "benchmark/reasoner/regressions/nominals_blowup.ttl",
    "benchmark/generated/pizza-ai.ttl",
    "benchmark/generated/boro-building-ai.ttl",
    "benchmark/generated/ies-building-extension.ttl",
    "benchmark/reference/ies4.ttl",
    "benchmark/reference/ies-core.ttl",
    "benchmark/reference/ies-top.ttl",
    "benchmark/reference/boro-building-handcrafted.ttl",
    "benchmark/epc/iris-building.ttl",
    "benchmark/mushroom/mushroom-ontology.ttl",
];

const CORPUS: &[&str] = &[
    "case-studies/foundry-owl-crosswalk/ontology/foundry-crosswalk.ttl",
    "case-studies/heritage-aerial/extensions/commerce/ontology/naph-commerce-shapes.ttl",
    "case-studies/heritage-aerial/extensions/commerce/ontology/naph-commerce.ttl",
    "case-studies/heritage-aerial/ontology/naph-core.ttl",
    "case-studies/heritage-aerial/ontology/naph-ric-o-crosswalk.ttl",
    "case-studies/heritage-aerial/ontology/naph-shapes.ttl",
    "case-studies/insurance-register-ontology/iro-core.ttl",
    "case-studies/investment-fund-ontology/ifo-core.ttl",
    "case-studies/modip-plastics-kg/ontology/colours.ttl",
    "case-studies/modip-plastics-kg/ontology/domains.ttl",
    "case-studies/modip-plastics-kg/ontology/facets.ttl",
    "case-studies/modip-plastics-kg/ontology/materials.ttl",
    "case-studies/modip-plastics-kg/ontology/objectnames.ttl",
    "case-studies/modip-plastics-kg/ontology/processes.ttl",
    "case-studies/nature-governance-graph/ontology/ngg.ttl",
    "case-studies/robot-safety-security-crosswalk/ontology/rssc.ttl",
    "case-studies/skills-england-occupational-maps/ontology/seom-vocabulary.ttl",
    "case-studies/skills-england-occupational-maps/ontology/shapes.ttl",
    "case-studies/skills-mobility/ontology/skills-mobility-scheme.ttl",
    "case-studies/zero-emission-aviation/ontology/zef.ttl",
];

fn sweep(label: &str, files: &[&str]) {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let present = files.iter().all(|rel| root.join(rel).is_file());
    if common::skip_unless(
        present,
        label,
        "it is tracked in this repository; run from a full checkout.",
    ) {
        return;
    }

    println!("── {label} ──");
    let mut total = std::time::Duration::ZERO;
    let mut capped = 0usize;
    for rel in files {
        let path = root.join(rel);
        let ttl = std::fs::read_to_string(&path).expect("corpus file must read");
        let store = Arc::new(GraphStore::new());
        if store.load_turtle(&ttl, None).is_err() {
            println!("{rel:>78}  DID NOT PARSE");
            continue;
        }
        let start = Instant::now();
        let out = Reasoner::run(&store, "owl-dl", false).expect("owl-dl must run");
        let took = start.elapsed();
        total += took;
        let v: serde_json::Value = serde_json::from_str(&out).unwrap();
        let phases = v["budget_exhausted_in"].to_string();
        if phases != "[]" {
            capped += 1;
        }
        println!(
            "{:>78}  {:>8.2}s  exhausted={} bound={}",
            rel,
            took.as_secs_f64(),
            phases,
            v["budget"]["binding_bound"]
        );
    }
    println!(
        "TOTAL {:.2}s over {} ontologies, {} of them hit a budget\n",
        total.as_secs_f64(),
        files.len(),
        capped
    );
}

#[test]
#[ignore = "wall-clock measurement over thirty ontologies; run it deliberately"]
fn owl_dl_over_the_shipped_corpora() {
    println!(
        "phase budget (tableaux_test_timeout_ms): {:?}",
        open_ontologies::runtime::tableaux_test_timeout_ms()
    );
    println!(
        "global budget (classify_timeout_ms):     {:?}\n",
        open_ontologies::runtime::classify_timeout_ms()
    );
    sweep("the twenty case-study ontologies", CORPUS);
    sweep("the ten that exhaust a budget", HARD);
}
