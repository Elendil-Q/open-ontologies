//! The Lean certificate layer, end to end.
//!
//! `reason --certificate DIR` writes what the reasoner started from and, for
//! every triple it inferred, the rule and premises it used. `lean/` holds a
//! checker for that certificate whose soundness is a machine-checked theorem
//! (`OOCert.certificate_sound`): a certificate it accepts contains only
//! triples entailed by the asserted graph. These tests close the loop.
//!
//!   1. Every ontology this repository ships certifies. The list is walked,
//!      not hand-picked, and anything excluded is named with the reason.
//!   2. Every rule the reasoner has appears in a certificate the checker
//!      accepts, so the emitter and the checker agree on all twenty premise
//!      orders, not just the common ones.
//!   3. The checker can say no. A forged conclusion, a premise outside the
//!      graph, and the exact derivation `cls-svf1` used to make before it was
//!      found unsound are each rejected. A gate that cannot fail is not a gate.
//!
//! The checker needs a Lean toolchain (`lake`). Without one these tests skip
//! loudly through `common::skip_unless`; the CI job that installs Lean runs
//! them with `OO_REQUIRE_FIXTURES=1`, which turns that skip into a failure.

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
    Command::new("lake")
        .arg("--version")
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

/// Build the checker once per test binary. The proofs are part of the build,
/// so a failure here is a failure, never a skip.
fn checker() -> &'static Path {
    static BUILT: OnceLock<PathBuf> = OnceLock::new();
    BUILT.get_or_init(|| {
        let out = Command::new("lake")
            .arg("build")
            .current_dir(lean_dir())
            .output()
            .expect("run lake build");
        assert!(
            out.status.success(),
            "lake build failed:\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let exe = lean_dir().join(".lake").join("build").join("bin").join("oo-cert");
        assert!(exe.exists(), "checker binary missing at {}", exe.display());
        exe
    })
}

/// Run the checker on a certificate directory. Returns (accepted, output).
fn check(dir: &Path) -> (bool, String) {
    let out = Command::new(checker())
        .arg(dir.join("asserted.tsv"))
        .arg(dir.join("derivations.tsv"))
        .output()
        .expect("run oo-cert");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (out.status.success(), text)
}

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("oo-cert-{}-{}", name, std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn certify_turtle(ttl: &str, profile: &str, dir: &Path) -> serde_json::Value {
    let store = Arc::new(GraphStore::new());
    store.load_turtle(ttl, None).unwrap();
    let out = Reasoner::run_full(&store, profile, false, InferenceTarget::DefaultGraph, Some(dir)).unwrap();
    serde_json::from_str(&out).unwrap()
}

const PREFIXES: &str = r#"
    @prefix : <http://ex.org/> .
    @prefix owl: <http://www.w3.org/2002/07/owl#> .
    @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
"#;

/// One ontology that fires all twenty rules.
const EVERY_RULE: &str = r#"
    :A rdfs:subClassOf :B . :B rdfs:subClassOf :C . :a a :A .
    :p rdfs:domain :Dom ; rdfs:range :Rng . :s :p :o .
    :q rdfs:subPropertyOf :r . :r rdfs:subPropertyOf :t . :s :q :o .
    :anc a owl:TransitiveProperty . :x :anc :y . :y :anc :z .
    :near a owl:SymmetricProperty . :x :near :y .
    :parent owl:inverseOf :child . :m :parent :n . :u :child :v .
    :a owl:sameAs :a2 .
    :E1 owl:equivalentClass :E2 . :pe1 owl:equivalentProperty :pe2 .
    :R1 a owl:Restriction ; owl:onProperty :has ; owl:someValuesFrom :F . :w :has :f . :f a :F .
    :R2 a owl:Restriction ; owl:onProperty :col ; owl:hasValue :red .
    :K rdfs:subClassOf :R2 . :k a :K . :j :col :red .
    :I owl:intersectionOf ( :M1 :M2 ) . :i a :M1 , :M2 .
    :U owl:unionOf ( :N1 :N2 ) . :n a :N2 .
"#;

const ALL_RULES: [&str; 20] = [
    "rdfs2", "rdfs3", "rdfs5", "rdfs7", "rdfs9", "rdfs11",
    "prp-trp", "prp-symp", "prp-inv1", "prp-inv2", "eq-sym",
    "scm-eqc1", "scm-eqc2", "scm-eqp1", "scm-eqp2",
    "cls-svf1", "cls-hv1", "cls-hv2", "cls-int1", "cls-uni",
];

#[test]
fn every_rule_family_appears_in_an_accepted_certificate() {
    if skip() {
        return;
    }
    let dir = scratch("every-rule");
    let r = certify_turtle(&format!("{PREFIXES}{EVERY_RULE}"), "owl-rl-ext", &dir);
    let by_rule = r["certificate"]["by_rule"].as_object().expect("by_rule in the response");
    let missing: Vec<&str> = ALL_RULES.iter().copied().filter(|k| !by_rule.contains_key(*k)).collect();
    assert!(missing.is_empty(), "rules that never fired on the all-rules ontology: {missing:?}\n{r}");
    assert_eq!(
        r["certificate"]["derivations"], r["inferred_count"],
        "one certificate line per inferred triple: {r}"
    );
    let (ok, out) = check(&dir);
    assert!(ok, "the checker rejected the all-rules certificate:\n{out}");
    assert!(out.contains("\"ok\":true"), "{out}");
}

#[test]
fn a_forged_conclusion_is_rejected() {
    if skip() {
        return;
    }
    let dir = scratch("forged");
    certify_turtle(&format!("{PREFIXES}{EVERY_RULE}"), "owl-rl-ext", &dir);
    let (ok, _) = check(&dir);
    assert!(ok, "the honest certificate must pass first");

    // rdfs9 with premises that do not support the conclusion.
    let forged = "rdfs9\t<http://ex.org/a>\t<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>\t<http://ex.org/Z>\t\
                  <http://ex.org/a>\t<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>\t<http://ex.org/A>\t\
                  <http://ex.org/A>\t<http://www.w3.org/2000/01/rdf-schema#subClassOf>\t<http://ex.org/B>\n";
    let path = dir.join("derivations.tsv");
    let mut content = std::fs::read_to_string(&path).unwrap();
    content.push_str(forged);
    std::fs::write(&path, content).unwrap();

    let (ok, out) = check(&dir);
    assert!(!ok, "a conclusion the premises do not support must be rejected:\n{out}");
    assert!(out.contains("\"ok\":false") && out.contains("first_rejected"), "{out}");
}

#[test]
fn a_premise_outside_the_graph_is_rejected() {
    if skip() {
        return;
    }
    let dir = scratch("outside");
    certify_turtle(&format!("{PREFIXES}{EVERY_RULE}"), "owl-rl-ext", &dir);

    // Well-formed rdfs9 whose subClassOf premise nobody asserted or derived.
    let forged = "rdfs9\t<http://ex.org/a>\t<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>\t<http://ex.org/Ghost>\t\
                  <http://ex.org/a>\t<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>\t<http://ex.org/A>\t\
                  <http://ex.org/A>\t<http://www.w3.org/2000/01/rdf-schema#subClassOf>\t<http://ex.org/Ghost>\n";
    let path = dir.join("derivations.tsv");
    let mut content = std::fs::read_to_string(&path).unwrap();
    content.push_str(forged);
    std::fs::write(&path, content).unwrap();

    let (ok, out) = check(&dir);
    assert!(!ok, "a premise that is neither asserted nor derived must be rejected:\n{out}");
}

#[test]
fn the_derivation_the_old_svf_rule_made_is_rejected() {
    if skip() {
        return;
    }
    // The ontology from tests/reason_rl_ext_soundness_test.rs, and the line
    // the reasoner used to emit for it: x ∈ C from C ⊑ ∃p.D and x ∈ ∃p.D.
    let dir = scratch("old-svf");
    let ttl = format!(
        "{PREFIXES}
        :C rdfs:subClassOf :R .
        :R a owl:Restriction ; owl:onProperty :p ; owl:someValuesFrom :D .
        :x :p :y . :y a :D ."
    );
    let r = certify_turtle(&ttl, "owl-rl-ext", &dir);
    let (ok, out) = check(&dir);
    assert!(ok, "the sound derivations must pass: {out}\n{r}");

    let forged = "cls-svf1\t<http://ex.org/x>\t<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>\t<http://ex.org/C>\t\
                  <http://ex.org/R>\t<http://www.w3.org/2002/07/owl#onProperty>\t<http://ex.org/p>\t\
                  <http://ex.org/R>\t<http://www.w3.org/2002/07/owl#someValuesFrom>\t<http://ex.org/D>\t\
                  <http://ex.org/x>\t<http://ex.org/p>\t<http://ex.org/y>\t\
                  <http://ex.org/y>\t<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>\t<http://ex.org/D>\n";
    let path = dir.join("derivations.tsv");
    let mut content = std::fs::read_to_string(&path).unwrap();
    content.push_str(forged);
    std::fs::write(&path, content).unwrap();

    let (ok, out) = check(&dir);
    assert!(!ok, "the converse of a subclass axiom has no rule; the checker must reject it:\n{out}");
    assert!(out.contains("cls-svf1"), "the rejection names the step: {out}");
}

#[test]
fn owl_dl_refuses_to_pretend_it_has_a_certificate() {
    let store = Arc::new(GraphStore::new());
    store.load_turtle(&format!("{PREFIXES} :A rdfs:subClassOf :B ."), None).unwrap();
    let dir = scratch("owl-dl");
    let err = Reasoner::run_full(&store, "owl-dl", false, InferenceTarget::DefaultGraph, Some(&dir))
        .expect_err("owl-dl has no rule trace and must say so");
    assert!(err.to_string().contains("no derivation certificate"), "{err}");
}

/// Everything under these roots that parses as RDF, up to the size cap.
const ROOTS: [&str; 5] = ["case-studies", "demo", "tests/fixtures", "data", "examples"];
const SIZE_CAP: u64 = 4 * 1024 * 1024;

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().to_string();
        if path.is_dir() {
            // Tooling trees that live beside the corpus locally but are not
            // part of it: a Python venv drops pyshacl's own shacl.ttl under
            // site-packages, and it certified happily, but it is not ours.
            if matches!(
                name.as_str(),
                "node_modules" | "target" | ".lake" | ".git" | ".venv" | "venv" | "site-packages" | "__pycache__"
            ) {
                continue;
            }
            walk(&path, out);
        } else if matches!(
            path.extension().and_then(|e| e.to_str()),
            Some("ttl" | "owl" | "rdf" | "nt")
        ) {
            out.push(path);
        }
    }
}

#[test]
fn every_shipped_ontology_certifies() {
    if skip() {
        return;
    }
    let mut files = Vec::new();
    for root in ROOTS {
        walk(&repo().join(root), &mut files);
    }
    files.sort();
    assert!(files.len() >= 40, "expected the shipped corpus, found {} files", files.len());

    let mut excluded: Vec<(String, String)> = Vec::new();
    let mut failures: Vec<(String, String)> = Vec::new();
    let mut certified = 0usize;
    let mut total_derivations = 0u64;

    for path in &files {
        let rel = path.strip_prefix(repo()).unwrap().display().to_string();
        let size = std::fs::metadata(path).unwrap().len();
        if size > SIZE_CAP {
            excluded.push((rel, format!("{} bytes, over the {} byte cap", size, SIZE_CAP)));
            continue;
        }
        let store = Arc::new(GraphStore::new());
        if let Err(e) = store.load_file(&path.display().to_string()) {
            excluded.push((rel, format!("does not parse: {}", e.to_string().lines().next().unwrap_or(""))));
            continue;
        }
        let dir = scratch(&format!("corpus-{}", certified));
        let out = match Reasoner::run_full(&store, "owl-rl-ext", false, InferenceTarget::DefaultGraph, Some(&dir)) {
            Ok(o) => o,
            Err(e) => {
                failures.push((rel, format!("reasoner error: {e}")));
                continue;
            }
        };
        let r: serde_json::Value = serde_json::from_str(&out).unwrap();
        if r["certificate"]["derivations"] != r["inferred_count"] {
            failures.push((rel.clone(), format!("certificate has {} lines for {} inferred triples", r["certificate"]["derivations"], r["inferred_count"])));
        }
        let (ok, text) = check(&dir);
        if ok {
            certified += 1;
            total_derivations += r["inferred_count"].as_u64().unwrap_or(0);
            eprintln!("CERTIFIED {rel}: {} asserted, {} derived", r["initial_triples"], r["inferred_count"]);
        } else {
            failures.push((rel, text));
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    eprintln!("certified {certified} files, {total_derivations} derivations checked");
    for (f, why) in &excluded {
        eprintln!("EXCLUDED {f}: {why}");
    }
    assert!(certified >= 30, "too few files certified ({certified}); excluded: {excluded:?}");
    assert!(total_derivations > 0, "the corpus produced no inferences at all, so nothing was checked");
    assert!(
        failures.is_empty(),
        "{} certificate(s) rejected or malformed:\n{}",
        failures.len(),
        failures.iter().map(|(f, t)| format!("--- {f}\n{t}")).collect::<Vec<_>>().join("\n")
    );
}
