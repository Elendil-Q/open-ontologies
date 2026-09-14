//! The producer for `oo-refute/1`, end to end.
//!
//! `lean/OOCert/Refute.lean` has checked refutations since the day it landed,
//! and until now nothing in `src/` wrote one: a checker with no producer, which
//! is the same shape of defect as a gate that cannot fail. `Reasoner::run_full`
//! now looks for a contradiction in the closure it reached and writes
//! `refutation.tsv` beside `asserted.tsv` and `derivations.tsv`.
//!
//! # The three things this file exists to protect
//!
//! **A produced refutation must actually check.** The format is defined by the
//! Lean parser and the hand-written fixtures in `tests/fixtures/refute`, not by
//! this producer, so the round trip is the only thing that settles whether the
//! two agree. `the_produced_refutation_is_accepted_by_the_checker` runs
//! `oo-refute` on the engine's own output.
//!
//! **An uncertified inconsistency must never look certified.** Seventeen rules
//! of OWL 2 RL conclude `false`; `OOCert.RefuteConditions` carries a semantic
//! condition for exactly one of them, `cax-dw`. The engine detects ten and can
//! write a refutation for one. For the other nine it says it found a clash and
//! says nothing else, because a file naming a rule the checker has no condition
//! for is refused with exit 2 and would be a certificate-shaped object that
//! certifies nothing. `the_engine_never_states_the_checkers_verdict` is the
//! laundering guard, written to the pattern
//! `tests/lean_horn_certificate_test.rs` set for the Horn layer.
//!
//! **A consistent ontology must never be refutable.** A refutation checker that
//! can be made to accept a refutation of a consistent ontology is worse than no
//! checker at all, and a producer that writes one is how that would happen.
//! `a_consistent_ontology_is_not_refuted` is that test, and
//! `a_forged_refutation_is_rejected` closes the other end by checking a valid
//! refutation of one graph against a different graph's asserted triples.
//!
//! # The limit, which is real and is not a bug
//!
//! `cax-dw` needs an INDIVIDUAL in two disjoint classes. A TBox that is
//! unsatisfiable with no individual asserted is invisible to the rule-based
//! route entirely. `the_tbox_only_case_is_invisible_here_and_the_tableau_sees_it`
//! computes that boundary rather than asserting it in a docstring: the same
//! ontology yields no clash under `owl-rl` and an unsatisfiable class under
//! `owl-dl`. The tableau's finding carries no certificate of its own, which is
//! what its report already says, so the more valuable half of this layer is
//! still missing and is named rather than hidden.

mod common;

use open_ontologies::graph::GraphStore;
use open_ontologies::reason::{InferenceTarget, Reasoner};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, OnceLock};

fn repo() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn lean_dir() -> PathBuf {
    repo().join("lean")
}

fn lake_available() -> bool {
    // `.current_dir(lean_dir())`: elan resolves the toolchain from the working
    // directory, and the crate root has no `lean-toolchain` in its ancestry.
    Command::new("lake")
        .arg("--version")
        .current_dir(lean_dir())
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn skip() -> bool {
    common::skip_unless(
        lake_available(),
        "lake (the Lean 4 build tool)",
        "install elan from https://github.com/leanprover/elan; lean/lean-toolchain pins the version",
    )
}

/// Build once per test binary. `oo-refute` is NOT in the lakefile's
/// `defaultTargets`, so naming it here is what puts `OOCert/Refute.lean` and
/// `OOCert/RefuteWitness.lean`, and the `#guard_msgs` axiom tripwires in them,
/// in front of a compiler.
fn refute_bin() -> &'static Path {
    static BUILT: OnceLock<PathBuf> = OnceLock::new();
    BUILT.get_or_init(|| {
        let out = Command::new("lake")
            .arg("build")
            .arg("oo-refute")
            .current_dir(lean_dir())
            .output()
            .expect("run lake build oo-refute");
        assert!(
            out.status.success(),
            "lake build oo-refute failed:\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let exe = lean_dir().join(".lake").join("build").join("bin").join("oo-refute");
        assert!(exe.exists(), "binary missing at {}", exe.display());
        exe
    })
}

/// Returns (exit code, stdout, stderr).
fn run_refute(args: &[&Path]) -> (i32, String, String) {
    let mut cmd = Command::new(refute_bin());
    for a in args {
        cmd.arg(a);
    }
    let out = cmd.output().expect("run oo-refute");
    (
        out.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&out.stdout).to_string(),
        String::from_utf8_lossy(&out.stderr).to_string(),
    )
}

fn check_refutation(asserted: &Path, refutation: &Path) -> (i32, String, String) {
    run_refute(&[Path::new("check"), asserted, refutation])
}

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("oo-refute-prod-{}-{}", name, std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Load Turtle, reason with a certificate, return the response. `materialize`
/// is false so the store is never written back into and `asserted.tsv` is the
/// file, not the file plus a previous run's conclusions.
fn reason(ttl: &str, profile: &str, dir: Option<&Path>) -> serde_json::Value {
    let store = Arc::new(GraphStore::new());
    store.load_turtle(ttl, None).unwrap();
    let out =
        Reasoner::run_full(&store, profile, false, InferenceTarget::DefaultGraph, dir).unwrap();
    serde_json::from_str(&out).unwrap()
}

const PREFIXES: &str = "@prefix : <http://ex.org/> .\n\
    @prefix owl: <http://www.w3.org/2002/07/owl#> .\n\
    @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .\n";

/// `leo` is a Lion, Lions are BigCats, BigCats are Carnivores, and `leo` is
/// also a Herbivore. The clash is two `rdfs9` hops away from what is asserted,
/// so a refutation over it CANNOT be written without a derivation prefix, which
/// is the half of the format a producer is most likely to get wrong.
const INCONSISTENT: &str = ":Herbivore owl:disjointWith :Carnivore .\n\
    :Lion rdfs:subClassOf :BigCat . :BigCat rdfs:subClassOf :Carnivore .\n\
    :leo a :Lion ; a :Herbivore .\n";

/// The same schema with the one assertion that clashes removed. Every other
/// triple, and the whole disjointness axiom, is still there.
const CONSISTENT: &str = ":Herbivore owl:disjointWith :Carnivore .\n\
    :Lion rdfs:subClassOf :BigCat . :BigCat rdfs:subClassOf :Carnivore .\n\
    :leo a :Lion .\n";

/// `:Lion` is an unsatisfiable CLASS and no individual is asserted. The
/// ontology is consistent, `:Lion` is not, and `cax-dw` has nothing to fire on
/// because it needs an individual.
const TBOX_ONLY: &str = ":Herbivore owl:disjointWith :Carnivore .\n\
    :Lion rdfs:subClassOf :Carnivore . :Lion rdfs:subClassOf :Herbivore .\n";

/// Contradictions of three rules the Lean checker has no semantic condition
/// for. Each is a real inconsistency and none of them can be certified here.
const UNCERTIFIABLE: &str = ":parentOf a owl:IrreflexiveProperty . :bob :parentOf :bob .\n\
    :alice owl:sameAs :bob . :alice owl:differentFrom :bob .\n\
    :ghost a owl:Nothing .\n";

fn ontology(body: &str) -> String {
    format!("{PREFIXES}{body}")
}

/// Every string value anywhere in a JSON document, so a verdict cannot hide in
/// a nested object.
fn string_values(v: &serde_json::Value, out: &mut Vec<String>) {
    match v {
        serde_json::Value::String(s) => out.push(s.clone()),
        serde_json::Value::Array(a) => a.iter().for_each(|x| string_values(x, out)),
        serde_json::Value::Object(o) => o.values().for_each(|x| string_values(x, out)),
        _ => {}
    }
}

#[test]
fn the_produced_refutation_is_accepted_by_the_checker() {
    if skip() {
        return;
    }
    let dir = scratch("accepted");
    let r = reason(&ontology(INCONSISTENT), "owl-rl", Some(&dir));

    assert_eq!(r["inconsistency"]["found"], true, "{r}");
    assert_eq!(r["inconsistency"]["refutation"]["written"], true, "{r}");
    assert_eq!(r["inconsistency"]["refutation"]["rule"], "cax-dw", "{r}");
    // The clash is not in the asserted triples. If the prefix were empty the
    // producer would have cited a premise it never derived.
    assert!(
        r["inconsistency"]["refutation"]["prefix"].as_u64().unwrap() >= 1,
        "the refutation must carry the derivation that reached the clash: {r}"
    );

    let (code, out, err) = check_refutation(&dir.join("asserted.tsv"), &dir.join("refutation.tsv"));
    assert_eq!(code, 0, "the checker rejected the engine's own refutation:\n{out}{err}");
    assert!(out.contains("\"ok\":true"), "{out}");
    assert!(out.contains("\"verdict\":\"unsatisfiable_under_disjointness\""), "{out}");
    assert!(out.contains("\"theorem\":\"OOCert.refutation_fast_sound\""), "{out}");
    println!("ACCEPTED: {out}");
}

#[test]
fn the_guard_refuses_the_derivation_certificate_over_the_graph_the_engine_refuted() {
    // The trap `oo-refute guard` exists for. The derivation certificate from
    // the same run still checks, and `oo-cert` would accept it and be telling
    // the truth; over a refuted graph it carries no information, which is
    // `OOCert.a_certificate_adds_nothing_when_the_graph_is_refuted`.
    if skip() {
        return;
    }
    let dir = scratch("guard");
    let r = reason(&ontology(INCONSISTENT), "owl-rl", Some(&dir));
    // The engine's own certificate block must carry the warning, or a consumer
    // reads `by_rule` counts off a graph where every triple is entailed.
    assert_eq!(r["certificate"]["graph_has_a_clash"], true, "{r}");

    let (code, out, err) = run_refute(&[
        Path::new("guard"),
        &dir.join("asserted.tsv"),
        &dir.join("derivations.tsv"),
        &dir.join("refutation.tsv"),
    ]);
    assert_eq!(code, 1, "the guard must refuse: {out}{err}");
    assert!(out.contains("\"certificate_ok\":true"), "{out}");
    assert!(out.contains("\"refuted\":true"), "{out}");
    assert!(
        out.contains("\"verdict\":\"certificate_refused_graph_is_unsatisfiable\""),
        "{out}"
    );
    println!("GUARD: {out}");
}

#[test]
fn a_consistent_ontology_is_not_refuted() {
    // THE test. A producer that writes a refutation for a consistent ontology
    // turns a verified checker into a machine for laundering a false claim, and
    // it is worse than having no checker at all.
    let dir = scratch("consistent");
    let r = reason(&ontology(CONSISTENT), "owl-rl", Some(&dir));

    assert!(
        r.get("inconsistency").is_none(),
        "a consistent ontology must report no clash at all: {r}"
    );
    assert!(
        !dir.join("refutation.tsv").exists(),
        "no refutation file may be written for a consistent ontology"
    );
    assert!(dir.join("derivations.tsv").exists(), "the ordinary certificate is still written");
    // And the certificate over it carries no clash warning, because there is
    // nothing to warn about.
    assert!(r["certificate"]["graph_has_a_clash"].is_null(), "{r}");

    if skip() {
        return;
    }
    // The checker must also reject a refutation built by hand over this graph.
    // `OOCert.feed_is_not_refuted` proves that rejection is correct rather than
    // a gap: the consistent graph really does have a model satisfying both
    // `Model` and `RefuteConditions`.
    let ex = "<http://ex.org/";
    let ty = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>";
    let sc = "<http://www.w3.org/2000/01/rdf-schema#subClassOf>";
    let dw = "<http://www.w3.org/2002/07/owl#disjointWith>";
    let attempt = format!(
        "oo-refute/1\n\
         rdfs9\t{ex}leo>\t{ty}\t{ex}Carnivore>\t{ex}leo>\t{ty}\t{ex}Lion>\t{ex}Lion>\t{sc}\t{ex}Carnivore>\n\
         refute\tcax-dw\t{ex}Herbivore>\t{dw}\t{ex}Carnivore>\t{ex}leo>\t{ty}\t{ex}Herbivore>\t\
         {ex}leo>\t{ty}\t{ex}Carnivore>\n"
    );
    let path = dir.join("hand_written_attempt.tsv");
    std::fs::write(&path, attempt).unwrap();
    let (code, out, err) = check_refutation(&dir.join("asserted.tsv"), &path);
    assert_eq!(code, 1, "a consistent graph must not be refutable: {out}{err}");
    assert!(out.contains("\"ok\":false"), "{out}");
    println!("CONSISTENT ONTOLOGY, REFUTATION REJECTED: {out}");
}

#[test]
fn a_forged_refutation_is_rejected() {
    // Three ways to lie about a graph the engine really can refute. Each has to
    // be caught on its own, and the honest refutation from the same run has to
    // pass first, or the test would be green because nothing works.
    if skip() {
        return;
    }
    let dir = scratch("forgery");
    reason(&ontology(INCONSISTENT), "owl-rl", Some(&dir));
    let asserted = dir.join("asserted.tsv");
    let honest = std::fs::read_to_string(dir.join("refutation.tsv")).unwrap();
    let (code, _, _) = check_refutation(&asserted, &dir.join("refutation.tsv"));
    assert_eq!(code, 0, "the honest refutation must be accepted first");

    let ex = "<http://ex.org/";
    let ty = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>";
    let sc = "<http://www.w3.org/2000/01/rdf-schema#subClassOf>";

    // 1. Premises that do not yield a contradiction. All three triples are
    //    ASSERTED, so nothing is missing from the graph and nothing is missing
    //    from the prefix; `:Lion rdfs:subClassOf :BigCat` is simply not a
    //    disjointness axiom, so no contradiction follows from the three.
    let mut lines: Vec<&str> = honest.lines().collect();
    let no_contradiction = format!(
        "refute\tcax-dw\t{ex}Lion>\t{sc}\t{ex}BigCat>\t{ex}leo>\t{ty}\t{ex}Lion>\t\
         {ex}leo>\t{ty}\t{ex}Herbivore>"
    );
    lines.pop();
    let mut forged = lines.join("\n");
    forged.push('\n');
    forged.push_str(&no_contradiction);
    forged.push('\n');

    // 2. A premise no step ever concluded. The prefix is dropped, so
    //    `:leo a :Carnivore` is neither asserted nor derived by this file.
    let refute_line = honest.lines().next_back().unwrap();
    let missing_step = format!("oo-refute/1\n{refute_line}\n");

    let cases = [
        (
            "premises that do not yield a contradiction",
            forged,
            "the first premise is a subClassOf triple, so cax-dw's shape does not match",
        ),
        (
            "a premise no derivation step concluded",
            missing_step,
            "the derivation prefix that reached the clash was removed",
        ),
    ];
    for (name, content, why) in cases {
        let path = dir.join("forged.tsv");
        std::fs::write(&path, &content).unwrap();
        let (code, out, err) = check_refutation(&asserted, &path);
        assert_eq!(code, 1, "{name} must be rejected because {why}: {out}{err}");
        assert!(out.contains("\"ok\":false"), "{name}: {out}");
        assert!(
            out.contains("not a proof of consistency"),
            "{name}: a rejection says nothing about consistency and the report must say so: {out}"
        );
        println!("REJECTED ({name}): {out}");
    }

    // 3. A refutation for a DIFFERENT graph: the honest one, checked against
    //    the consistent ontology's asserted triples.
    let other = scratch("forgery-other");
    reason(&ontology(CONSISTENT), "owl-rl", Some(&other));
    let (code, out, err) =
        check_refutation(&other.join("asserted.tsv"), &dir.join("refutation.tsv"));
    assert_eq!(
        code, 1,
        "a refutation of one graph must not check against another: {out}{err}"
    );
    assert!(out.contains("\"ok\":false"), "{out}");
    println!("REJECTED (a refutation of a different graph): {out}");
}

#[test]
fn an_uncertifiable_clash_is_never_written_as_a_refutation() {
    // `OOCert.RefuteConditions` carries one field, for `cax-dw`. A refutation
    // naming any other clash rule is refused by `oo-refute` with exit 2, which
    // is a file that could not be judged rather than a graph that could not be
    // refuted. The engine must therefore say it found a clash and write
    // nothing, and the two outcomes must not share a word.
    let dir = scratch("uncertifiable");
    let r = reason(&ontology(UNCERTIFIABLE), "owl-rl", Some(&dir));

    assert_eq!(r["inconsistency"]["found"], true, "{r}");
    let by_rule = r["inconsistency"]["by_rule"].as_object().unwrap();
    for rule in ["prp-irp", "eq-diff1", "cls-nothing2"] {
        assert!(by_rule.contains_key(rule), "{rule} must be detected: {r}");
    }
    assert!(
        !by_rule.contains_key("cax-dw"),
        "this ontology has no disjointness clash: {r}"
    );
    for c in r["inconsistency"]["clashes"].as_array().unwrap() {
        assert_eq!(c["certifiable"], false, "no clash here is certifiable: {r}");
    }
    assert_eq!(r["inconsistency"]["refutation"]["written"], false, "{r}");
    assert!(
        !dir.join("refutation.tsv").exists(),
        "no refutation file may be written for a clash the checker cannot judge"
    );
    let why = r["inconsistency"]["refutation"]["why"].as_str().unwrap();
    assert!(why.contains("cax-dw"), "the reason must name the one rule that IS judged: {why}");
    println!("UNCERTIFIABLE CLASH: {}", r["inconsistency"]["by_rule"]);
}

#[test]
fn the_engine_never_states_the_checkers_verdict() {
    // The laundering guard, in the pattern
    // `tests/lean_horn_certificate_test.rs::a_user_rule_never_earns_the_absolute_verdict`
    // set for the Horn layer. `unsatisfiable_under_disjointness` is what
    // `oo-refute` prints when it has ACCEPTED a refutation, and
    // `OOCert.refutation_fast_sound` is the theorem behind it. Neither may be a
    // verdict this engine states about its own findings: an engine opinion and
    // a machine-checked result must never share a string, or a consumer cannot
    // tell them apart.
    for (name, ttl) in [("cax-dw", INCONSISTENT), ("uncertifiable", UNCERTIFIABLE)] {
        let dir = scratch(&format!("laundering-{name}"));
        let r = reason(&ontology(ttl), "owl-rl", Some(&dir));

        assert_eq!(r["inconsistency"]["verdict"], "clash_found_by_this_engine", "{r}");
        assert_eq!(r["inconsistency"]["checked_by_lean"], false, "{r}");

        let mut values = Vec::new();
        string_values(&r, &mut values);
        for v in &values {
            assert_ne!(
                v, "unsatisfiable_under_disjointness",
                "{name}: that verdict is the CHECKER's, earned by an accepted refutation, and \
                 this engine must not state it: {r}"
            );
            assert!(
                !v.contains("OOCert.refutation_fast_sound"),
                "{name}: naming the soundness theorem is claiming its conclusion: {r}"
            );
        }
    }
    // And the word the engine does use for a written refutation says plainly
    // that nothing has checked it.
    let dir = scratch("laundering-word");
    let r = reason(&ontology(INCONSISTENT), "owl-rl", Some(&dir));
    assert_eq!(
        r["inconsistency"]["refutation"]["verdict"],
        "refutation_written_not_yet_checked",
        "{r}"
    );
}

#[test]
fn the_tbox_only_case_is_invisible_here_and_the_tableau_sees_it() {
    // The documented boundary, computed rather than asserted. `cax-dw` needs an
    // individual in two disjoint classes. `:Lion` is unsatisfiable and nothing
    // is an instance of it, so the rule-based route sees nothing at all, and
    // the report must not pretend otherwise by staying silent about the limit
    // elsewhere. The SHIQ tableau does see it, and its finding carries no
    // certificate: that is the more valuable half of this layer and it is not
    // built.
    let dir = scratch("tbox-only");
    let rl = reason(&ontology(TBOX_ONLY), "owl-rl", Some(&dir));
    assert!(
        rl.get("inconsistency").is_none(),
        "an unsatisfiable class with no instance is invisible to cax-dw: {rl}"
    );
    assert!(!dir.join("refutation.tsv").exists());

    let store = Arc::new(GraphStore::new());
    store.load_turtle(&ontology(TBOX_ONLY), None).unwrap();
    let dl: serde_json::Value = serde_json::from_str(
        &Reasoner::run_full(&store, "owl-dl", false, InferenceTarget::DefaultGraph, None).unwrap(),
    )
    .unwrap();
    let unsat = dl["unsatisfiable_classes"].as_array().unwrap();
    assert!(
        unsat.iter().any(|c| c.as_str() == Some("<http://ex.org/Lion>")),
        "the tableau must see the case the rules cannot: {dl}"
    );
    // And it says, itself, that it certifies nothing when it answers this way.
    println!("owl-rl: no clash. owl-dl: unsatisfiable_classes = {unsat:?}, with no certificate.");

    // Add ONE individual and the same ontology becomes visible to cax-dw, which
    // is exactly what the boundary is.
    let dir2 = scratch("tbox-plus-one");
    let with_instance = reason(
        &ontology(&format!("{TBOX_ONLY}:leo a :Lion .\n")),
        "owl-rl",
        Some(&dir2),
    );
    assert_eq!(with_instance["inconsistency"]["refutation"]["written"], true, "{with_instance}");
}

#[test]
fn a_run_without_a_certificate_directory_reports_the_clash_and_writes_nothing() {
    // The finding is not conditional on being asked for a certificate, or an
    // ontology reasoned over without `--certificate` would be silently
    // contradictory. What IS conditional is the file, and the report says so
    // rather than leaving the caller to wonder where it went.
    let r = reason(&ontology(INCONSISTENT), "owl-rl", None);
    assert_eq!(r["inconsistency"]["found"], true, "{r}");
    assert_eq!(r["inconsistency"]["refutation"]["written"], false, "{r}");
    let why = r["inconsistency"]["refutation"]["why"].as_str().unwrap();
    assert!(why.contains("certificate"), "the report must say how to get one: {why}");
}

#[test]
fn a_stale_refutation_does_not_survive_a_run_that_finds_nothing() {
    // A refutation left in the directory by an earlier run would be checked
    // against THIS run's asserted.tsv, which is a different graph. It would
    // almost certainly be rejected, and "almost certainly" is not the standard:
    // a consumer reading the directory must not find a file describing a graph
    // that is no longer there.
    let dir = scratch("stale");
    reason(&ontology(INCONSISTENT), "owl-rl", Some(&dir));
    assert!(dir.join("refutation.tsv").exists(), "the first run must write one");

    reason(&ontology(CONSISTENT), "owl-rl", Some(&dir));
    assert!(
        !dir.join("refutation.tsv").exists(),
        "a run that finds no clash must leave no refutation behind it"
    );
}

#[test]
fn two_runs_reach_the_same_contradiction() {
    // The closure lives in a HashSet, so without an explicit order the CHOSEN
    // CLASH would depend on hash iteration and two runs over one ontology could
    // report different contradictions. `find_clashes` sorts on the N-Triples
    // spelling, so the `refute` line is the same every time.
    //
    // THE PREFIX IS NOT PINNED HERE, and the reason is not this producer's.
    // `:leo a :Carnivore` has two derivations in this ontology, one through
    // `:BigCat` and one through the `rdfs11` transitive subclass triple, and
    // which one the fixpoint records first depends on the same hash iteration
    // order that already decides the line order of `derivations.tsv`. Either is
    // a valid prefix and the checker accepts either. Claiming byte-for-byte
    // stability for the whole file would be claiming a property the engine's
    // derivation log does not have.
    let a = scratch("determinism-a");
    let b = scratch("determinism-b");
    reason(&ontology(INCONSISTENT), "owl-rl", Some(&a));
    reason(&ontology(INCONSISTENT), "owl-rl", Some(&b));
    let last = |d: &Path| {
        std::fs::read_to_string(d.join("refutation.tsv"))
            .unwrap()
            .lines()
            .next_back()
            .unwrap()
            .to_string()
    };
    assert_eq!(
        last(&a),
        last(&b),
        "two runs over one ontology must reach one contradiction"
    );
}
