//! Two proof assistants, one certificate format, and the question of whether the two
//! formalisations actually say the same thing.
//!
//! `lean/OOCert/Horn.lean` and `isabelle/OO_Check.thy` are independent formalisations of
//! the same Horn-certificate checker. The Isabelle one was written from the W3C primary
//! sources and the fixture DATA, with nothing under `lean/` read; a transliteration would
//! have been worthless, because a shared definitional bug survives translation untouched.
//! This file runs both over the same bytes and requires them to agree.
//!
//! # What agreement here is, and is not
//!
//! Checking a Horn certificate is PURELY SYNTACTIC. Neither checker consults its own
//! semantics: no interpretation, no domain, no truth. Two checkers built on contradictory
//! model theories agree on every certificate and on every forgery. So agreement in this
//! file is evidence about the FILE FORMAT and the CHECKING DISCIPLINE — how a binding is
//! read, whether premise order is part of the contract, what an out-of-range index is —
//! and it is not a proof of anything. It does not show the two semantics agree, it does
//! not add a theorem to either side, and it must never be reported as if it did.
//!
//! The evidence that the DEFINITIONS agree lives elsewhere: in which rule arms each side
//! can discharge and from which conditions (`isabelle/OO_Builtin_Sound.thy`,
//! `lean/OOCert/HornBuiltin.lean`), and in whether the conditions describe anything at
//! all (`isabelle/OO_NonVacuity.thy`, `lean/OOCert/HornWitness.lean`).
//!
//! What agreement here DOES buy is real and worth having: wherever the two checkers
//! accept and reject the same files, the certificate format has one meaning rather than
//! two. Where they do not, it has two, and that is the interesting part.
//!
//! # The disagreements
//!
//! Four were found, in two classes, and none is papered over. They are pinned by
//! `divergence_d1_*`, `divergence_d2_*`, `divergence_d2b_*` and `divergence_d2c_*` below,
//! their certificates are committed under `isabelle/fixtures-differential/`, and the
//! corpus test classifies each disagreement BY ITS CAUSE and fails on any it cannot
//! account for. Read those tests: the analysis is there, not here.
//!
//! Three were designed after reading both checkers. The fourth was found by the fuzzer,
//! in a rule file one character away from a probe written for something else, which is
//! why `binding_defect` classifies by cause rather than by which edit produced the row: a
//! quarantine keyed on the edit would have hidden it.
//!
//! All three have ONE root cause. **Isabelle validates the binding list as a data
//! structure and Lean does not.** `check_step` requires `distinct (map fst b)` and
//! `binding_covers b r` before it instantiates anything; Lean's `substOf` is
//! `fun v => (List.lookup v l).getD v`, which turns any binding list into a total
//! function with a silent default and never inspects it. D1 is the duplicate key, D2 the
//! missing one.
//!
//! Neither checker is unsound. In all three Lean accepts and Isabelle rejects, and Lean's
//! acceptance holds in Lean's own theorem, because `EntailsR` quantifies over every total
//! substitution and the one Lean used is a real one; Isabelle's rejections are false
//! alarms, which is the harmless direction. What is defective is the FORMAT: it does not
//! say whether a binding must have distinct keys or must cover the cited rule's
//! variables, so Lean's answer to the first is whatever `List.lookup` happens to do, and
//! its answer to the second fabricates a term out of a variable's name and puts it in the
//! conclusion. Until the format says, a certificate's validity depends on which verified
//! checker reads it.

mod common;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, OnceLock};

// ── where things live ───────────────────────────────────────────────────────

fn repo() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn lean_dir() -> PathBuf {
    repo().join("lean")
}

fn isabelle_dir() -> PathBuf {
    repo().join("isabelle")
}

fn horn_fixture(name: &str) -> PathBuf {
    repo().join("tests").join("fixtures").join("horn").join(name)
}

fn differential_fixture(name: &str) -> PathBuf {
    isabelle_dir().join("fixtures-differential").join(name)
}

// ── availability, and a loud skip ───────────────────────────────────────────

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

/// The Isabelle side needs Poly/ML to link the exported checker, and the exported
/// checker itself, which `isabelle/export.sh` writes out of the session and which is
/// committed so this test does not need a full Isabelle build to run.
///
/// The same search `isabelle/build_native.sh` does, and for the same reason: asking
/// `isabelle getenv ISABELLE_HOME` is the only answer that is right on a machine that is
/// not this one, and the macOS app bundle is only the fallback.
fn poly_dir() -> Option<PathBuf> {
    let arch = if cfg!(target_arch = "aarch64") { "arm64" } else { "x86_64" };
    let os = if cfg!(target_os = "macos") { "darwin" } else { "linux" };
    let platform = format!("{arch}-{os}");

    let mut roots: Vec<PathBuf> = Vec::new();
    if let Ok(out) = Command::new("isabelle").args(["getenv", "-b", "ISABELLE_HOME"]).output()
        && out.status.success()
    {
        let home = String::from_utf8_lossy(&out.stdout).trim().to_string();
        if !home.is_empty() {
            roots.push(PathBuf::from(home));
        }
    }
    if let Ok(entries) = std::fs::read_dir("/Applications") {
        roots.extend(entries.flatten().map(|e| e.path()));
    }

    let mut found: Vec<PathBuf> = Vec::new();
    for root in roots {
        let contrib = root.join("contrib");
        let Ok(cs) = std::fs::read_dir(&contrib) else { continue };
        for c in cs.flatten() {
            if c.file_name().to_string_lossy().starts_with("polyml-") {
                let d = c.path().join(&platform);
                if d.join("poly").exists() {
                    found.push(d);
                }
            }
        }
    }
    found.sort();
    found.pop()
}

fn isabelle_available() -> bool {
    poly_dir().is_some() && isabelle_dir().join("driver").join("oo_horn_generated.ML").exists()
}

/// Both halves are needed, and a skip has to say WHICH half is missing. A test that
/// returns early reports `ok`, so `common::skip_unless` prints a marker and, under
/// `OO_REQUIRE_FIXTURES=1`, turns the skip into a failure.
fn skip() -> bool {
    if common::skip_unless(
        lake_available(),
        "lake (the Lean 4 build tool), for the Lean half of the differential",
        "install elan from https://github.com/leanprover/elan; lean/lean-toolchain pins the version",
    ) {
        return true;
    }
    common::skip_unless(
        isabelle_available(),
        "Poly/ML (bundled with Isabelle) and isabelle/driver/oo_horn_generated.ML, \
         for the Isabelle half of the differential",
        "install Isabelle2025-2 from https://isabelle.in.tum.de; the generated ML is \
         committed, and isabelle/export.sh regenerates it from the session",
    )
}

// ── building the two checkers, once per test binary ─────────────────────────

/// The Lean proofs are part of `lake build`, so a failure here is a failure and never a
/// skip: the binary that comes out of it is the one the theorems are about.
fn lean_checker() -> &'static Path {
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
        let exe = lean_dir().join(".lake").join("build").join("bin").join("oo-horn");
        assert!(exe.exists(), "checker binary missing at {}", exe.display());
        exe
    })
}

/// The Isabelle side links the code `export_code` wrote into a native executable. The
/// LINK is what happens here; nothing is re-derived from the theories, and the theories
/// are checked by `isabelle build -d isabelle -c OOHorn`, which this test does not run.
fn isabelle_checker() -> &'static Path {
    static BUILT: OnceLock<PathBuf> = OnceLock::new();
    BUILT.get_or_init(|| {
        let script = isabelle_dir().join("build_native.sh");
        let out = Command::new("sh")
            .arg(&script)
            .current_dir(repo())
            .output()
            .expect("run isabelle/build_native.sh");
        assert!(
            out.status.success(),
            "isabelle/build_native.sh failed:\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let exe = isabelle_dir().join("build").join("oo-horn-isabelle");
        assert!(exe.exists(), "checker binary missing at {}", exe.display());
        exe
    })
}

// ── one run of one checker ──────────────────────────────────────────────────

/// What a run of either checker says, reduced to the three things that are comparable.
/// `exit` is the discipline both sides implement: 0 accepted, 1 rejected, 2 unreadable or
/// unparseable. `verdict` is present only when the run accepted.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Outcome {
    exit: i32,
    verdict: Option<String>,
}

fn json_field(json: &str, key: &str) -> Option<String> {
    let pat = format!("\"{key}\":\"");
    let start = json.find(&pat)? + pat.len();
    let rest = &json[start..];
    Some(rest[..rest.find('"')?].to_string())
}

fn run_lean(rules: &Path, asserted: &Path, cert: &Path) -> Outcome {
    let out = Command::new(lean_checker())
        .arg("check")
        .arg(rules)
        .arg(asserted)
        .arg(cert)
        .output()
        .expect("run oo-horn");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let exit = out.status.code().unwrap_or(-1);
    Outcome { exit, verdict: if exit == 0 { json_field(&stdout, "verdict") } else { None } }
}

fn run_isabelle(rules: &Path, asserted: &Path, cert: &Path) -> Outcome {
    let out = Command::new(isabelle_checker())
        .arg("check")
        .arg(rules)
        .arg(asserted)
        .arg(cert)
        .output()
        .expect("run oo-horn-isabelle");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let exit = out.status.code().unwrap_or(-1);
    Outcome { exit, verdict: if exit == 0 { json_field(&stdout, "verdict") } else { None } }
}

// ── the certificate format, as data, so it can be mutated ───────────────────

/// One line of `horn.tsv`:
/// `idx TAB k TAB (var TAB term)*k TAB cs TAB cp TAB co TAB (ps TAB pp TAB po)*m`.
///
/// Note what this parser does NOT need: the rule table. The field count is
/// `2 + 2k + 3 + 3m` and `k` is field 1, so `m` is recoverable from the line alone. Both
/// checkers parse this way; it is why an out-of-range rule index is a rejection (exit 1)
/// on both sides rather than a parse error (exit 2) on either.
#[derive(Debug, Clone)]
struct Step {
    idx: String,
    binds: Vec<(String, String)>,
    concl: [String; 3],
    prems: Vec<[String; 3]>,
}

fn parse_step(line: &str) -> Option<Step> {
    let f: Vec<&str> = line.split('\t').collect();
    if f.len() < 5 {
        return None;
    }
    let k: usize = f[1].parse().ok()?;
    if f.len() < 5 + 2 * k || !(f.len() - 5 - 2 * k).is_multiple_of(3) {
        return None;
    }
    let binds =
        (0..k).map(|i| (f[2 + 2 * i].to_string(), f[3 + 2 * i].to_string())).collect::<Vec<_>>();
    let c = 2 + 2 * k;
    let concl = [f[c].to_string(), f[c + 1].to_string(), f[c + 2].to_string()];
    let mut prems = Vec::new();
    let mut i = c + 3;
    while i + 2 < f.len() {
        prems.push([f[i].to_string(), f[i + 1].to_string(), f[i + 2].to_string()]);
        i += 3;
    }
    Some(Step { idx: f[0].to_string(), binds, concl, prems })
}

fn render_step(s: &Step) -> String {
    let mut parts = vec![s.idx.clone(), s.binds.len().to_string()];
    for (v, t) in &s.binds {
        parts.push(v.clone());
        parts.push(t.clone());
    }
    for t in std::iter::once(&s.concl).chain(s.prems.iter()) {
        parts.extend(t.iter().cloned());
    }
    parts.join("\t")
}

fn parse_cert(text: &str) -> Option<Vec<Step>> {
    text.lines().filter(|l| !l.is_empty()).map(parse_step).collect()
}

fn render_cert(steps: &[Step]) -> String {
    let mut s = String::new();
    for st in steps {
        s.push_str(&render_step(st));
        s.push('\n');
    }
    s
}

// ── the mutations ───────────────────────────────────────────────────────────

/// A fresh IRI no fixture mentions, so substituting it is always a lie.
const ALIEN: &str = "<http://ex.invalid/never-derived>";

/// Each mutation is a named, deterministic edit of a certificate's TEXT. Returning
/// `None` means the mutation does not apply to this certificate (too few steps,
/// bindings or premises) and the row is simply not generated.
type Mutation = (&'static str, fn(&str) -> Option<String>);

fn mutations() -> Vec<Mutation> {
    vec![
        ("rule_index_plus_one", |t| {
            let mut c = parse_cert(t)?;
            let n: usize = c.first()?.idx.parse().ok()?;
            c[0].idx = (n + 1).to_string();
            Some(render_cert(&c))
        }),
        ("rule_index_out_of_range", |t| {
            let mut c = parse_cert(t)?;
            c.first()?;
            c[0].idx = "9999".to_string();
            Some(render_cert(&c))
        }),
        ("rule_index_not_a_number", |t| {
            let mut c = parse_cert(t)?;
            c.first()?;
            c[0].idx = "four".to_string();
            Some(render_cert(&c))
        }),
        ("permute_binding_values", |t| {
            let mut c = parse_cert(t)?;
            if c.first()?.binds.len() < 2 {
                return None;
            }
            let v0 = c[0].binds[0].1.clone();
            c[0].binds[0].1 = c[0].binds[1].1.clone();
            c[0].binds[1].1 = v0;
            Some(render_cert(&c))
        }),
        ("binding_value_replaced", |t| {
            let mut c = parse_cert(t)?;
            if c.first()?.binds.is_empty() {
                return None;
            }
            c[0].binds[0].1 = ALIEN.to_string();
            Some(render_cert(&c))
        }),
        // D1. The key is duplicated with a WRONG second value. Whether this is a
        // rejection depends entirely on how a duplicate key is resolved, which is the
        // thing the format does not say. See `divergence_d1_duplicate_binding_key`.
        ("duplicate_binding_key", |t| {
            let mut c = parse_cert(t)?;
            if c.first()?.binds.is_empty() {
                return None;
            }
            let key = c[0].binds[0].0.clone();
            c[0].binds.push((key, ALIEN.to_string()));
            Some(render_cert(&c))
        }),
        // D2's shape, though over ordinary IRI terms it does NOT diverge: Lean
        // substitutes the variable's own name, which is not an IRI, so both reject. The
        // case where it does diverge is hand-built in `fixtures-differential/`.
        ("drop_binding_pair", |t| {
            let mut c = parse_cert(t)?;
            if c.first()?.binds.is_empty() {
                return None;
            }
            c[0].binds.remove(0);
            Some(render_cert(&c))
        }),
        ("drop_last_premise", |t| {
            let mut c = parse_cert(t)?;
            if c.first()?.prems.is_empty() {
                return None;
            }
            c[0].prems.pop();
            Some(render_cert(&c))
        }),
        ("permute_premises", |t| {
            let mut c = parse_cert(t)?;
            if c.first()?.prems.len() < 2 {
                return None;
            }
            c[0].prems.swap(0, 1);
            Some(render_cert(&c))
        }),
        ("premise_object_replaced", |t| {
            let mut c = parse_cert(t)?;
            if c.first()?.prems.is_empty() {
                return None;
            }
            c[0].prems[0][2] = ALIEN.to_string();
            Some(render_cert(&c))
        }),
        ("conclusion_object_replaced", |t| {
            let mut c = parse_cert(t)?;
            c.first()?;
            c[0].concl[2] = ALIEN.to_string();
            Some(render_cert(&c))
        }),
        // The step now cites its own conclusion as its first premise. On a rule whose
        // body and head differ this also breaks instantiation, which is why no shipped
        // fixture reaches the no-self-support property on its own.
        ("step_cites_own_conclusion", |t| {
            let mut c = parse_cert(t)?;
            if c.first()?.prems.is_empty() {
                return None;
            }
            let concl = c[0].concl.clone();
            c[0].prems[0] = concl;
            Some(render_cert(&c))
        }),
        ("reverse_steps", |t| {
            let mut c = parse_cert(t)?;
            if c.len() < 2 {
                return None;
            }
            c.reverse();
            Some(render_cert(&c))
        }),
        ("swap_first_two_steps", |t| {
            let mut c = parse_cert(t)?;
            if c.len() < 2 {
                return None;
            }
            c.swap(0, 1);
            Some(render_cert(&c))
        }),
        // Accepting mutations, so the corpus is not all rejections. A duplicated step is
        // redundant, and a prefix of a valid certificate is a valid certificate.
        ("duplicate_first_step", |t| {
            let mut c = parse_cert(t)?;
            let first = c.first()?.clone();
            c.push(first);
            Some(render_cert(&c))
        }),
        ("drop_last_step", |t| {
            let mut c = parse_cert(t)?;
            if c.len() < 2 {
                return None;
            }
            c.pop();
            Some(render_cert(&c))
        }),
        // The field separator, injected into a term. One tab shifts the field count by
        // one, so `(NF - 5 - 2k)` stops being a multiple of three and the line is
        // unparseable on both sides: exit 2, not a rejection.
        ("tab_inside_a_term", |t| {
            let first = t.lines().find(|l| !l.is_empty())?;
            let s = parse_step(first)?;
            let broken = first.replacen(&s.concl[0], &format!("{}\t{}", s.concl[0], "x"), 1);
            Some(t.replacen(first, &broken, 1))
        }),
        // Three tabs keep the count a multiple of three, so the line PARSES — into a
        // different step, with a spurious premise. It must be rejected, not accepted.
        ("three_tabs_inside_terms", |t| {
            let first = t.lines().find(|l| !l.is_empty())?;
            let s = parse_step(first)?;
            let broken = first.replacen(&s.concl[0], &format!("{}\tx\ty\tz", s.concl[0]), 1);
            Some(t.replacen(first, &broken, 1))
        }),
        ("truncate_last_field", |t| {
            let first = t.lines().find(|l| !l.is_empty())?;
            let cut = first.rfind('\t')?;
            Some(t.replacen(first, &first[..cut], 1))
        }),
        ("empty_certificate", |_| Some(String::new())),
    ]
}

/// Edits of the RULE TABLE rather than the certificate. These are where the VERDICT
/// WORD is at stake: a table that is not the built-in one must earn the relativised
/// verdict on both sides, and a certificate over it may still check.
type RuleMutation = (&'static str, fn(&str) -> Option<String>);

fn rule_mutations() -> Vec<RuleMutation> {
    vec![
        // Names are labels, not keys: the certificate cites an INDEX. Both sides must
        // still accept, and both must downgrade the verdict, because both decide the
        // absolute verdict by comparing the whole table.
        ("rule_renamed", |t| {
            let first = t.lines().find(|l| !l.is_empty())?;
            let name = first.split('\t').next()?;
            Some(t.replacen(&format!("{name}\t"), "renamed-rule\t", 1))
        }),
        ("rules_reversed", |t| {
            let mut ls: Vec<&str> = t.lines().filter(|l| !l.is_empty()).collect();
            if ls.len() < 2 {
                return None;
            }
            ls.reverse();
            Some(ls.join("\n") + "\n")
        }),
        ("rule_appended", |t| {
            Some(
                t.to_string()
                    + "invented\t1\t?s\t<http://ex.invalid/p>\t?o\t?s\t<http://ex.invalid/q>\t?o\n",
            )
        }),
        ("rules_truncated_to_two", |t| {
            let ls: Vec<&str> = t.lines().filter(|l| !l.is_empty()).collect();
            if ls.len() < 3 {
                return None;
            }
            Some(ls[..2].join("\n") + "\n")
        }),
        ("rule_variable_renamed", |t| {
            let first = t.lines().find(|l| !l.is_empty())?;
            if !first.contains("?x") {
                return None;
            }
            Some(t.replacen(first, &first.replace("?x", "?renamedvar"), 1))
        }),
        ("rule_body_length_wrong", |t| {
            let first = t.lines().find(|l| !l.is_empty())?;
            let f: Vec<&str> = first.split('\t').collect();
            let n: usize = f[1].parse().ok()?;
            let mut g = f.clone();
            let bumped = (n + 1).to_string();
            g[1] = &bumped;
            Some(t.replacen(first, &g.join("\t"), 1))
        }),
    ]
}

// ── the corpus ──────────────────────────────────────────────────────────────

struct Case {
    name: String,
    /// The mutation that produced it, or `"base"`. Disagreements are classified by this.
    kind: String,
    rules: PathBuf,
    asserted: PathBuf,
    cert: PathBuf,
}

/// The repository's own RDF, as source graphs. Directories rather than a hand-typed file
/// list, so a fixture added to the repository is picked up rather than silently missed.
/// Sorted, so the corpus is the same on every run.
fn source_graphs() -> Vec<PathBuf> {
    let dirs = [
        "benchmark/reference",
        "benchmark/generated",
        "benchmark/data",
        "benchmark/epc",
        "benchmark/gvr",
        "benchmark/mushroom",
        "demo/derived",
        "demo/corpus/dcat-us",
        "tests/w3c-shacl/core/complex",
        "tests/data",
    ];
    let mut out: Vec<PathBuf> = Vec::new();
    for d in dirs {
        let dir = repo().join(d);
        let Ok(entries) = std::fs::read_dir(&dir) else { continue };
        for e in entries.flatten() {
            let p = e.path();
            if p.extension().and_then(|s| s.to_str()) == Some("ttl") {
                out.push(p);
            }
        }
    }
    out.push(repo().join("tests").join("test_ontology.ttl"));
    out.sort();
    out
}

/// Generate one certificate per (graph, rule table) pair, using the engine as the
/// producer. Steps are capped: a prefix of a valid certificate is a valid certificate,
/// because a step may only cite what came strictly before it, so truncation cannot turn
/// a bad certificate into a good one.
const MAX_STEPS: usize = 30;

fn generate_base_certificates(scratch: &Path) -> Vec<Case> {
    use open_ontologies::graph::GraphStore;
    use open_ontologies::reason::Reasoner;

    let mut cases = Vec::new();
    for (i, graph) in source_graphs().iter().enumerate() {
        let Ok(ttl) = std::fs::read_to_string(graph) else { continue };
        let store = Arc::new(GraphStore::new());
        if store.load_turtle(&ttl, None).is_err() {
            continue;
        }
        for table in ["builtin_rules.tsv", "user_rules.tsv"] {
            let stem = graph.file_stem().and_then(|s| s.to_str()).unwrap_or("graph").to_string();
            let tag = format!("{i:02}-{stem}-{}", table.trim_end_matches(".tsv"));
            let dir = scratch.join(&tag);
            if std::fs::create_dir_all(&dir).is_err() {
                continue;
            }
            if Reasoner::run_horn(&store, &horn_fixture(table), &dir).is_err() {
                continue;
            }
            let Ok(horn) = std::fs::read_to_string(dir.join("horn.tsv")) else { continue };
            let steps: Vec<&str> = horn.lines().filter(|l| !l.is_empty()).collect();
            if steps.is_empty() {
                // A graph the table derives nothing from certifies nothing. Keeping it
                // would pad the count with rows on which both checkers accept the empty
                // certificate, which is agreement about nothing.
                continue;
            }
            let capped: String =
                steps.iter().take(MAX_STEPS).map(|l| format!("{l}\n")).collect::<String>();
            let cert = dir.join("cert.tsv");
            std::fs::write(&cert, &capped).unwrap();
            cases.push(Case {
                name: tag,
                kind: "base".to_string(),
                rules: dir.join("rules.tsv"),
                asserted: dir.join("asserted.tsv"),
                cert,
            });
        }
    }
    cases
}

/// Every committed fixture, including the ones `isabelle/fixtures-added/` carries for
/// properties the shipped set cannot reach.
fn fixture_cases() -> Vec<Case> {
    let added = |n: &str| isabelle_dir().join("fixtures-added").join(n);
    let rows: Vec<(&str, PathBuf, PathBuf, PathBuf)> = vec![
        ("fx-good", horn_fixture("builtin_rules.tsv"), horn_fixture("asserted.tsv"), horn_fixture("good.tsv")),
        ("fx-good-user-table", horn_fixture("user_rules.tsv"), horn_fixture("asserted.tsv"), horn_fixture("good.tsv")),
        ("fx-good-short-table", horn_fixture("short_rules.tsv"), horn_fixture("asserted.tsv"), horn_fixture("good.tsv")),
        ("fx-bad-index", horn_fixture("builtin_rules.tsv"), horn_fixture("asserted.tsv"), horn_fixture("bad_index.tsv")),
        ("fx-bad-binding", horn_fixture("builtin_rules.tsv"), horn_fixture("asserted.tsv"), horn_fixture("bad_binding.tsv")),
        ("fx-bad-conclusion", horn_fixture("builtin_rules.tsv"), horn_fixture("asserted.tsv"), horn_fixture("bad_conclusion.tsv")),
        ("fx-bad-premise", horn_fixture("builtin_rules.tsv"), horn_fixture("asserted.tsv"), horn_fixture("bad_premise.tsv")),
        ("fx-bad-self", horn_fixture("builtin_rules.tsv"), horn_fixture("asserted.tsv"), horn_fixture("bad_self.tsv")),
        ("fx-good-chain", horn_fixture("builtin_rules.tsv"), added("asserted_chain.tsv"), added("good_chain.tsv")),
        ("fx-bad-self-chain", horn_fixture("builtin_rules.tsv"), added("asserted_chain.tsv"), added("bad_self_chain.tsv")),
        ("fx-bad-order", horn_fixture("builtin_rules.tsv"), horn_fixture("asserted.tsv"), added("bad_order.tsv")),
        // The D1 certificate is in the corpus like every other committed fixture, and
        // not held back because it is the one that disagrees. `binding_defect` classifies
        // it, `divergence_d1_duplicate_binding_key` pins it, and its mutants are checked
        // like anything else.
        ("fx-bad-dup-key", horn_fixture("builtin_rules.tsv"), horn_fixture("asserted.tsv"), added("bad_dup_key.tsv")),
        ("fx-generalized", horn_fixture("builtin_rules.tsv"), added("asserted_gen.tsv"), added("generalized.tsv")),
    ];
    rows.into_iter()
        .filter(|(_, r, a, c)| r.exists() && a.exists() && c.exists())
        .map(|(n, r, a, c)| Case {
            name: n.to_string(),
            kind: "base".to_string(),
            rules: r,
            asserted: a,
            cert: c,
        })
        .collect()
}

/// The corners of the term format that NO generated certificate reaches, because the
/// engine writes IRIs and the repository's fixtures are ASCII. Each is a committed
/// `probe_<name>_{rules,asserted,cert}.tsv` triple under `isabelle/fixtures-differential/`.
/// They join the corpus as base cases, so they are mutated and fuzzed like everything
/// else; `the_untested_corners_of_the_term_format_agree` pins what each one should do.
fn probe_cases() -> Vec<Case> {
    let dir = isabelle_dir().join("fixtures-differential");
    let Ok(entries) = std::fs::read_dir(&dir) else { return Vec::new() };
    let mut names: Vec<String> = entries
        .flatten()
        .filter_map(|e| {
            let f = e.file_name().to_string_lossy().to_string();
            f.strip_prefix("probe_")
                .and_then(|r| r.strip_suffix("_rules.tsv"))
                .map(|s| s.to_string())
        })
        .collect();
    names.sort();
    names
        .into_iter()
        .map(|n| Case {
            name: format!("probe-{n}"),
            kind: "base".to_string(),
            rules: dir.join(format!("probe_{n}_rules.tsv")),
            asserted: dir.join(format!("probe_{n}_asserted.tsv")),
            cert: dir.join(format!("probe_{n}_cert.tsv")),
        })
        .filter(|c| c.rules.exists() && c.asserted.exists() && c.cert.exists())
        .collect()
}

/// Expand each base case into its mutants.
fn mutate(bases: &[Case], scratch: &Path) -> Vec<Case> {
    let mut out = Vec::new();
    for base in bases {
        let Ok(cert_text) = std::fs::read_to_string(&base.cert) else { continue };
        let Ok(rules_text) = std::fs::read_to_string(&base.rules) else { continue };
        let dir = scratch.join("mut").join(&base.name);
        if std::fs::create_dir_all(&dir).is_err() {
            continue;
        }
        for (name, f) in mutations() {
            let Some(text) = f(&cert_text) else { continue };
            if text == cert_text {
                continue;
            }
            let p = dir.join(format!("{name}.tsv"));
            if std::fs::write(&p, &text).is_err() {
                continue;
            }
            out.push(Case {
                name: format!("{}/{name}", base.name),
                kind: name.to_string(),
                rules: base.rules.clone(),
                asserted: base.asserted.clone(),
                cert: p,
            });
        }
        for (name, f) in rule_mutations() {
            let Some(text) = f(&rules_text) else { continue };
            if text == rules_text {
                continue;
            }
            let p = dir.join(format!("rules-{name}.tsv"));
            if std::fs::write(&p, &text).is_err() {
                continue;
            }
            out.push(Case {
                name: format!("{}/{name}", base.name),
                kind: name.to_string(),
                rules: p,
                asserted: base.asserted.clone(),
                cert: base.cert.clone(),
            });
        }
    }
    out
}

fn scratch_dir() -> PathBuf {
    let d = std::env::temp_dir().join(format!("oo-cross-kernel-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).expect("create scratch dir");
    d
}

// ── classifying a divergence by its cause, not by the edit that produced it ──

/// A rule, read far enough to know which variables it has. Not a third checker: this is
/// used only to EXPLAIN a divergence the two checkers have already produced, never to
/// decide whether they agree. If it is wrong, a row goes unexplained and the test fails,
/// which is the safe direction.
struct Rule {
    vars: Vec<String>,
}

fn parse_rule_line(line: &str) -> Option<Rule> {
    let f: Vec<&str> = line.split('\t').collect();
    if f.len() < 5 {
        return None;
    }
    let n: usize = f[1].parse().ok()?;
    if f.len() != 5 + 3 * n {
        return None;
    }
    let mut vars = Vec::new();
    for field in &f[2..] {
        if let Some(v) = field.strip_prefix('?')
            && !vars.iter().any(|x| x == v)
        {
            vars.push(v.to_string());
        }
    }
    Some(Rule { vars })
}

/// Why the two kernels differ on these files, if the reason is the one known root cause:
/// **Isabelle validates the binding list as a data structure and Lean does not.**
///
/// Isabelle's `check_step` runs `distinct (map fst b)` and then `binding_covers b r`
/// before instantiating anything. Lean's `substOf` is `fun v => (List.lookup v l).getD v`
/// — a total function with a silent default, built without looking at the list at all. So
/// a binding with a repeated key (D1) or with a variable missing (D2) is rejected by one
/// and silently resolved by the other.
///
/// This is a POSITIVE test of that diagnosis, and that is the point. Excusing a
/// divergence because of the EDIT that produced it would hide a second, unrelated
/// divergence arriving through the same edit — and would have hidden the one the fuzzer
/// found through a one-character change to a rule file. Excusing it because the binding
/// list really is malformed, in a specific way, at the step in question, cannot.
fn binding_defect(rules_path: &Path, cert_path: &Path) -> Option<&'static str> {
    let rules_text = std::fs::read_to_string(rules_path).ok()?;
    let rules: Vec<Rule> =
        rules_text.lines().filter(|l| !l.is_empty()).map(parse_rule_line).collect::<Option<_>>()?;
    let cert_text = std::fs::read_to_string(cert_path).ok()?;
    let steps = parse_cert(&cert_text)?;

    for step in &steps {
        let Ok(idx) = step.idx.parse::<usize>() else { return None };
        let Some(rule) = rules.get(idx) else { continue };
        let mut seen: Vec<&str> = Vec::new();
        for (k, _) in &step.binds {
            if seen.contains(&k.as_str()) {
                return Some(
                    "D1: the binding list repeats a key. Isabelle rejects it as malformed \
                     (R_binding_dup_key); Lean resolves it with List.lookup, which is \
                     first-wins, and accepts.",
                );
            }
            seen.push(k);
        }
        if rule.vars.iter().any(|v| !seen.contains(&v.as_str())) {
            return Some(
                "D2: the binding does not cover every variable of the cited rule. Isabelle \
                 rejects (R_binding_incomplete); Lean's substOf sends the unbound variable \
                 to its own NAME and carries on, so the step checks whenever that name is \
                 the term the certificate used.",
            );
        }
    }
    None
}

/// A divergence is excused only when Lean ACCEPTED, Isabelle REJECTED, and the binding
/// list really is malformed in one of the two known ways. Every other shape — Isabelle
/// accepting where Lean rejects, a divergence on an exit code of 2, a divergence over a
/// well-formed binding — is unexplained and fails the corpus test.
fn known_divergence(
    rules: &Path,
    cert: &Path,
    lean: &Outcome,
    isabelle: &Outcome,
) -> Option<&'static str> {
    if lean.exit != 0 || isabelle.exit != 1 {
        return None;
    }
    binding_defect(rules, cert)
}

// ── a seeded fuzzer over the file format ────────────────────────────────────

/// The hand-written mutations above test the failures someone thought of. This tests the
/// ones nobody did, and it is aimed squarely at the PARSERS, which is where two
/// independent readers of one format are most likely to part company: field counts,
/// numbers that are not numbers, empty fields, and the field separator appearing inside
/// a term.
///
/// Seeded, so a run is reproducible. It is NOT stable across changes to the corpus: one
/// stream feeds every base in order, so adding a base shifts every draw after it and a
/// given row stops being generated. That is why a row the fuzzer finds interesting gets
/// COMMITTED as a fixture with its own test — `divergence_d2c_*` is one it found and
/// this configuration no longer reaches. The fuzzer is a search, and the fixtures are
/// what the search found.
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        // xorshift64*. Written out rather than pulled in: a dev-dependency for four
        // lines of arithmetic is a dependency in the trust surface of a test whose whole
        // subject is trust surfaces.
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        if n == 0 { 0 } else { (self.next_u64() % n as u64) as usize }
    }
}

/// Tokens a corrupted field may be replaced with, chosen to hit the dispatch points both
/// parsers have: the `?` that makes a rule field a variable, the `<`/`>` that make a term
/// an IRI, the `_:` that make it a blank node, a quote, an empty field, numbers in and
/// out of range, and a raw TAB.
const FUZZ_TOKENS: &[&str] = &[
    "",
    "?",
    "?x",
    "?renamed",
    "<http://ex.org/a>",
    "<",
    ">",
    "<>",
    "_:b",
    "_:",
    "\"lit\"",
    "\"lit\"@en",
    "0",
    "1",
    "4",
    "27",
    "9999",
    "-1",
    "007",
    "not-a-number",
    "x",
    "a\tb",
];

fn fuzz_tsv(text: &str, rng: &mut Rng, edits: usize) -> String {
    let mut lines: Vec<Vec<String>> = text
        .lines()
        .filter(|l| !l.is_empty())
        .map(|l| l.split('\t').map(|s| s.to_string()).collect())
        .collect();
    if lines.is_empty() {
        return text.to_string();
    }
    for _ in 0..edits {
        let li = rng.below(lines.len());
        if lines[li].is_empty() {
            continue;
        }
        let fi = rng.below(lines[li].len());
        match rng.below(6) {
            0 => {
                lines[li].remove(fi);
            }
            1 => {
                let v = lines[li][fi].clone();
                lines[li].insert(fi, v);
            }
            2 => {
                let fj = rng.below(lines[li].len());
                lines[li].swap(fi, fj);
            }
            3 => {
                lines[li][fi] = FUZZ_TOKENS[rng.below(FUZZ_TOKENS.len())].to_string();
            }
            4 => {
                let n: u64 = lines[li][fi].parse().unwrap_or(0);
                lines[li][fi] = n.wrapping_add(1 + rng.below(3) as u64).to_string();
            }
            _ => {
                let t = FUZZ_TOKENS[rng.below(FUZZ_TOKENS.len())];
                lines[li][fi] = format!("{}{t}", lines[li][fi]);
            }
        }
    }
    lines.iter().map(|f| f.join("\t") + "\n").collect()
}

const FUZZ_SEED: u64 = 0x0000_00D1_FFED_0001;

/// Six fuzzed variants of each base, three corrupting the certificate and three the rule
/// table, with a growing number of edits.
fn fuzz(bases: &[Case], scratch: &Path) -> Vec<Case> {
    let mut rng = Rng(FUZZ_SEED);
    let mut out = Vec::new();
    for base in bases {
        let Ok(cert_text) = std::fs::read_to_string(&base.cert) else { continue };
        let Ok(rules_text) = std::fs::read_to_string(&base.rules) else { continue };
        let dir = scratch.join("fuzz").join(&base.name);
        if std::fs::create_dir_all(&dir).is_err() {
            continue;
        }
        for edits in 1..=3 {
            let text = fuzz_tsv(&cert_text, &mut rng, edits);
            let p = dir.join(format!("cert-{edits}.tsv"));
            if std::fs::write(&p, &text).is_ok() {
                out.push(Case {
                    name: format!("{}/fuzz-cert-{edits}", base.name),
                    kind: format!("fuzz_cert_{edits}"),
                    rules: base.rules.clone(),
                    asserted: base.asserted.clone(),
                    cert: p,
                });
            }
            let text = fuzz_tsv(&rules_text, &mut rng, edits);
            let p = dir.join(format!("rules-{edits}.tsv"));
            if std::fs::write(&p, &text).is_ok() {
                out.push(Case {
                    name: format!("{}/fuzz-rules-{edits}", base.name),
                    kind: format!("fuzz_rules_{edits}"),
                    rules: p,
                    asserted: base.asserted.clone(),
                    cert: base.cert.clone(),
                });
            }
        }
    }
    out
}

// ── the tests ───────────────────────────────────────────────────────────────

#[test]
fn the_skip_says_which_half_is_missing() {
    // The skip path is the one nobody looks at until CI is silently green over nothing,
    // so it is exercised here rather than assumed. `skip_unless` returns false when the
    // thing IS available, and prints a SKIPPED_FIXTURE marker when it is not.
    let present = common::skip_unless(true, "a thing that is here", "nothing to do");
    assert!(!present, "skip_unless must not skip when the tool is available");
    if lake_available() && isabelle_available() {
        assert!(!skip(), "both toolchains are present, so this must not skip");
    } else {
        assert!(skip(), "a missing toolchain must skip loudly, not run half a differential");
    }
}

/// The two embedded rule tables are shown equal THROUGH the committed fixture, which is
/// what makes comparing the verdict word mean anything.
///
/// `lean_horn_certificate_test.rs` already pins `oo-horn rules` against
/// `tests/fixtures/horn/builtin_rules.tsv` byte for byte. This adds the other half:
/// `verdict_of` assigns the ABSOLUTE verdict to a table only when that table IS
/// `builtin_table`, so `table_verdict: entailed` over the same bytes says Isabelle's
/// embedded table is the fixture too. Lean's `Builtin.asHorn` and Isabelle's
/// `builtin_table` are therefore the same 27 rules, by two independent comparisons
/// against one file, rather than by anybody's say-so.
#[test]
fn both_embedded_rule_tables_are_the_committed_fixture() {
    if skip() {
        return;
    }
    let lean = Command::new(lean_checker()).arg("rules").output().expect("oo-horn rules");
    assert!(lean.status.success());
    let printed = String::from_utf8_lossy(&lean.stdout).to_string();
    let committed = std::fs::read_to_string(horn_fixture("builtin_rules.tsv")).unwrap();
    assert_eq!(
        printed.trim_end(),
        committed.trim_end(),
        "Lean's built-in table has drifted from the committed fixture"
    );

    let isa = Command::new(isabelle_checker())
        .arg("table")
        .arg(horn_fixture("builtin_rules.tsv"))
        .output()
        .expect("oo-horn-isabelle table");
    let out = String::from_utf8_lossy(&isa.stdout).to_string();
    assert_eq!(
        json_field(&out, "table_verdict").as_deref(),
        Some("entailed"),
        "Isabelle's verdict_of must call the committed fixture the built-in table; if it \
         does not, the two embedded tables differ and every verdict comparison below is \
         comparing two different things: {out}"
    );

    // And the negative, or the assertion above is unfalsifiable: a table that is NOT the
    // built-in one must not earn the absolute verdict on either side.
    let isa = Command::new(isabelle_checker())
        .arg("table")
        .arg(horn_fixture("user_rules.tsv"))
        .output()
        .expect("oo-horn-isabelle table");
    let out = String::from_utf8_lossy(&isa.stdout).to_string();
    assert_eq!(
        json_field(&out, "table_verdict").as_deref(),
        Some("entailed_under_supplied_rules"),
        "a user table must not be mistaken for the built-in one: {out}"
    );
}

/// **The differential.** Both checkers, every certificate, the accept/reject bit, the
/// exit code and the verdict word.
#[test]
fn the_two_kernels_agree_on_the_whole_corpus() {
    if skip() {
        return;
    }
    let scratch = scratch_dir();
    let mut bases = fixture_cases();
    bases.extend(probe_cases());
    bases.extend(generate_base_certificates(&scratch));
    let mutants = mutate(&bases, &scratch);
    let fuzzed = fuzz(&bases, &scratch);
    let total = bases.len() + mutants.len() + fuzzed.len();

    assert!(
        total >= 200,
        "a differential over {total} certificates is not evidence of anything. Agreement \
         on a handful of hand-written files is what a shared bug looks like. Something \
         has gone wrong in corpus generation"
    );

    let mut agree_accept = 0usize;
    let mut agree_reject = 0usize;
    let mut agree_unreadable = 0usize;
    let mut classified: BTreeMap<String, usize> = BTreeMap::new();
    let mut unexplained: Vec<String> = Vec::new();

    for case in bases.iter().chain(mutants.iter()).chain(fuzzed.iter()) {
        let l = run_lean(&case.rules, &case.asserted, &case.cert);
        let i = run_isabelle(&case.rules, &case.asserted, &case.cert);
        if l == i {
            match l.exit {
                0 => agree_accept += 1,
                1 => agree_reject += 1,
                _ => agree_unreadable += 1,
            }
            continue;
        }
        match known_divergence(&case.rules, &case.cert, &l, &i) {
            Some(why) => {
                let class = if why.starts_with("D1") { "D1 duplicate key" } else { "D2 missing" };
                *classified.entry(format!("{class} [{}]", case.kind)).or_default() += 1;
            }
            None => unexplained.push(format!(
                "{}\n    lean:     exit {} verdict {:?}\n    isabelle: exit {} verdict {:?}\n    \
                 rules={} asserted={} cert={}",
                case.name,
                l.exit,
                l.verdict,
                i.exit,
                i.verdict,
                case.rules.display(),
                case.asserted.display(),
                case.cert.display()
            )),
        }
    }

    let known: usize = classified.values().sum();
    println!(
        "cross-kernel differential\n  \
         certificates:     {total} ({} base, {} mutated, {} fuzzed, seed {FUZZ_SEED:#x})\n  \
         both accept:      {agree_accept}\n  \
         both reject:      {agree_reject}\n  \
         both exit 2:      {agree_unreadable}\n  \
         known divergence: {known}\n  \
         unexplained:      {}",
        bases.len(),
        mutants.len(),
        fuzzed.len(),
        unexplained.len()
    );
    for (kind, n) in &classified {
        println!("  {kind}: {n} rows");
    }

    assert!(
        unexplained.is_empty(),
        "THE TWO KERNELS DISAGREE, and not in a way this file has an account of. A \
         disagreement is the headline result of this test, not a nuisance: do not adjust \
         either checker to make it go away, and do not add it to `known_divergence` \
         without first deciding from the specification which side is wrong.\n\n{}",
        unexplained.join("\n\n")
    );

    // A corpus that is all rejections would prove only that both sides can say no.
    assert!(agree_accept >= 20, "only {agree_accept} certificates were accepted by both");
    assert!(agree_reject >= 100, "only {agree_reject} certificates were rejected by both");
    assert!(agree_unreadable >= 10, "only {agree_unreadable} inputs were unparseable on both");

    let _ = std::fs::remove_dir_all(&scratch);
}

/// **Divergence D1.** A binding list with a repeated key.
///
/// `isabelle/fixtures-added/bad_dup_key.tsv` binds `x` twice: first to `<http://ex.org/a>`,
/// which is the value that makes the step check, then to `<http://ex.org/zzz>`, which
/// does not.
///
/// * Isabelle: `check_step` tests `distinct (map fst b)` first and returns
///   `R_binding_dup_key`. Decision M25 records this as a deliberate STRICTNESS and
///   uncertainty U10 records it as a coin-flip between two honest authors.
/// * Lean: `substOf` is `fun v => (List.lookup v l).getD v`, and `List.lookup` returns
///   the FIRST match. `x` resolves to `<http://ex.org/a>`, the step checks, and the run
///   earns the ABSOLUTE verdict.
///
/// Which is wrong? Neither, on soundness. `checkHornStep_sound` quantifies over the
/// substitution `substOf st.binds`, which is a perfectly good total substitution
/// whichever value it picks, so Lean's acceptance is sound in Lean's own theorem, and
/// Isabelle's rejection is a false alarm rather than a missed forgery.
///
/// The defect is in the FORMAT, and it is real. `docs/lean-certificates.md` and decision
/// 0003 do not say what a repeated binding key means, so Lean's answer is whatever
/// `List.lookup` happens to do. That is a tie-break inside a standard-library function
/// standing in for a rule about the file format, and it decides whether a certificate is
/// valid. Isabelle's `binding_covers` comment predicted exactly this and named `map_of`'s
/// first-wins behaviour as the reason not to rely on it; the Lean side has no comment on
/// duplicate keys at all — `substOf`'s docstring discusses MISSING bindings only.
///
/// The repair belongs on the Lean side (reject a repeated key, or write the first-wins
/// rule into the format as normative), and it is not made here: the instruction for this
/// exercise is that a disagreement is the result, and a disagreement quietly fixed is a
/// disagreement hidden.
#[test]
fn divergence_d1_duplicate_binding_key() {
    if skip() {
        return;
    }
    let cert = isabelle_dir().join("fixtures-added").join("bad_dup_key.tsv");
    if common::skip_unless(cert.exists(), "isabelle/fixtures-added/bad_dup_key.tsv", "it is committed") {
        return;
    }
    let rules = horn_fixture("builtin_rules.tsv");
    let asserted = horn_fixture("asserted.tsv");
    let lean = run_lean(&rules, &asserted, &cert);
    let isa = run_isabelle(&rules, &asserted, &cert);

    assert_eq!(lean.exit, 0, "Lean accepts a duplicate binding key, first-wins");
    assert_eq!(
        lean.verdict.as_deref(),
        Some("entailed"),
        "and it accepts with the ABSOLUTE verdict, which is what makes the divergence \
         worth reporting rather than filing"
    );
    assert_eq!(isa.exit, 1, "Isabelle rejects it as malformed");
    assert_ne!(lean, isa, "if these ever agree, D1 has been resolved and this test should say how");
}

/// **Divergence D2.** A binding that does not cover every variable of the rule, where
/// the missing variable's NAME is itself a term in the graph.
///
/// The certificate in `isabelle/fixtures-differential/` cites a one-atom rule
/// `?s <p> ?o -> ?s <q> ?o` over a graph whose only triple is `s <p> <b>` — note the
/// subject is the bare term `s`, spelled exactly like the rule's variable. The binding
/// supplies `o` and omits `s`.
///
/// * Isabelle: `binding_covers` requires every variable of the rule to have a binding,
///   and returns `R_binding_incomplete`. Its instantiation `iptriple` is PARTIAL, so an
///   unbound variable has no value at all and there is nothing to fall through to.
/// * Lean: `substOf` is total by construction — `(List.lookup v l).getD v` — so an
///   unbound variable takes its own NAME as its value. `s` becomes the term `s`, the
///   body instantiates to the asserted triple, the head instantiates to the claimed
///   conclusion, and the step checks.
///
/// Which side is wrong depends on which question is being asked, and the two questions
/// have opposite answers. That is worth saying plainly rather than picking a winner.
///
/// On "is the conclusion entailed under this rule table?", LEAN IS RIGHT. `EntailsR`
/// quantifies over every total substitution, so a step whose body instantiates into known
/// triples under SOME total substitution really does entail its conclusion, and the
/// substitution Lean used is a real one. Isabelle's rejection is incompleteness, and a
/// false alarm is the harmless direction.
///
/// On "is this a well-formed certificate?", ISABELLE IS RIGHT, and
/// `divergence_d2b_unsafe_rule_head` is why: Lean's default does not merely admit more
/// certificates, it FABRICATES a term out of a variable's name and puts it in the
/// conclusion. A certificate can therefore be accepted whose conclusion is not a writable
/// RDF triple at all.
///
/// This also contradicts, ACROSS the two checkers, a claim proved inside one of them.
/// Isabelle's `coverage_implied` says removing the coverage check cannot change its
/// accept/reject bit, and that is true — of Isabelle, where instantiation is partial, so
/// a missing binding kills the step anyway. It does not transfer: Lean's instantiation is
/// total, so the same check is load-bearing there and in the opposite direction. A
/// property proved of one formalisation's checker is not a property of the format, and
/// this is what that looks like when it bites.
///
/// Neither side is adjusted. What the pair needs is a sentence in the format saying
/// whether a binding must be total over the rule's variables; until there is one, a
/// certificate's validity depends on which verified checker reads it.
#[test]
fn divergence_d2_binding_omits_a_variable_named_like_a_term() {
    if skip() {
        return;
    }
    let rules = differential_fixture("varname_rules.tsv");
    let asserted = differential_fixture("varname_asserted.tsv");
    let cert = differential_fixture("varname_unbound_cert.tsv");
    if common::skip_unless(
        rules.exists() && asserted.exists() && cert.exists(),
        "isabelle/fixtures-differential/varname_*.tsv",
        "they are committed",
    ) {
        return;
    }

    let lean = run_lean(&rules, &asserted, &cert);
    let isa = run_isabelle(&rules, &asserted, &cert);
    assert_eq!(lean.exit, 0, "Lean accepts: the omitted variable takes its own name, which matches");
    assert_eq!(
        lean.verdict.as_deref(),
        Some("entailed_under_supplied_rules"),
        "relativised, because this is a user table and nothing discharges it"
    );
    assert_eq!(isa.exit, 1, "Isabelle rejects: binding_incomplete");
    assert_ne!(lean, isa, "if these ever agree, D2 has been resolved and this test should say how");

    // The control. Bind `s` as well and both accept, so the divergence is about the
    // MISSING binding and not about anything else in these three files.
    let full = differential_fixture("varname_bound_cert.tsv");
    if full.exists() {
        let lean = run_lean(&rules, &asserted, &full);
        let isa = run_isabelle(&rules, &asserted, &full);
        assert_eq!(lean.exit, 0, "the fully bound certificate must be accepted by Lean");
        assert_eq!(isa.exit, 0, "and by Isabelle");
        assert_eq!(lean, isa, "with the same verdict");
    }
}

/// **Divergence D2c: the same hole, found by the fuzzer rather than designed.**
///
/// The three files here are not hand-built. `d2c_fuzzfound_rules.tsv` is
/// `probe_degen2_rules.tsv` with ONE field replaced by the seeded fuzzer: the body's
/// object pattern `?o` became a bare `?`, which both parsers read as a variable whose
/// NAME IS THE EMPTY STRING. The graph's object is an empty field. So Lean's default
/// sends the unbound variable `""` to the term `""`, the body instantiates to the
/// asserted triple, and the step checks. Isabelle wants a binding for `""` and does not
/// find one.
///
/// It is worth its own test because of where it came from. D2a needed a graph whose
/// subject was spelled like a variable, and the obvious objection is that nobody writes
/// such a graph. This one needed a single character to change in a rule file. The hole is
/// reachable by a typo, and `substOf`'s silent default is what turns a typo into an
/// accepted certificate rather than an error.
#[test]
fn divergence_d2c_fuzzer_found_the_same_hole_through_a_typo() {
    if skip() {
        return;
    }
    let rules = differential_fixture("d2c_fuzzfound_rules.tsv");
    let asserted = differential_fixture("d2c_fuzzfound_asserted.tsv");
    let cert = differential_fixture("d2c_fuzzfound_cert.tsv");
    if common::skip_unless(
        rules.exists() && asserted.exists() && cert.exists(),
        "isabelle/fixtures-differential/d2c_fuzzfound_*.tsv",
        "they are committed",
    ) {
        return;
    }

    // One field apart from the probe it was fuzzed from, and that field is the bare `?`.
    let original = std::fs::read_to_string(differential_fixture("probe_degen2_rules.tsv")).unwrap();
    let fuzzed = std::fs::read_to_string(&rules).unwrap();
    let a: Vec<&str> = original.trim_end().split('\t').collect();
    let b: Vec<&str> = fuzzed.trim_end().split('\t').collect();
    assert_eq!(a.len(), b.len(), "the fuzzer changed a field, not the field count");
    let differing: Vec<usize> = (0..a.len()).filter(|i| a[*i] != b[*i]).collect();
    assert_eq!(differing.len(), 1, "exactly one field differs: {a:?} vs {b:?}");
    assert_eq!(b[differing[0]], "?", "and the one that differs is a bare question mark");

    assert_eq!(
        binding_defect(&rules, &cert),
        Some(
            "D2: the binding does not cover every variable of the cited rule. Isabelle \
             rejects (R_binding_incomplete); Lean's substOf sends the unbound variable \
             to its own NAME and carries on, so the step checks whenever that name is \
             the term the certificate used."
        ),
        "this must be classified as D2 and not as something new"
    );

    let lean = run_lean(&rules, &asserted, &cert);
    let isa = run_isabelle(&rules, &asserted, &cert);
    assert_eq!(lean.exit, 0, "Lean accepts: the empty-named variable takes the empty term");
    assert_eq!(isa.exit, 1, "Isabelle rejects: binding_incomplete");
    assert_ne!(lean, isa);
}

/// **Divergence D2b, the sharp form of D2.** A rule whose HEAD carries a variable its
/// body never binds, and a certificate that does not bind it either.
///
/// The rule is `?s <p> ?o -> ?s <q> ?z`. The graph is one ordinary triple of IRIs,
/// `<a> <p> <b>`; nothing about it is contrived. The certificate binds `s` and `o`, omits
/// `z`, and claims the conclusion `<a> <q> z`.
///
/// Lean accepts it. `substOf` sends the unbound `z` to the string `"z"`, the head
/// instantiates to exactly the claimed conclusion, and the run reports
/// `entailed_under_supplied_rules`. Isabelle rejects it, `R_binding_incomplete`.
///
/// This is the same hole as D2 and a worse consequence. The accepted conclusion contains
/// the term `z`, which is not an IRI, not a blank node and not a literal: it is not RDF,
/// and no serialiser can write it. Lean's term type is an opaque string, so nothing in
/// the checker notices. The term was never written by the certificate's author; it was
/// minted out of a VARIABLE NAME in the rule file.
///
/// It is still not unsoundness. `EntailsR` is a statement about `Interp`, whose `ι` is
/// total over terms, so `<a> <q> z` genuinely holds in every interpretation that models
/// the graph and satisfies the rule. The theorem is true. What is false is the thing a
/// reader takes the theorem to be about.
///
/// The engine already refuses to EVALUATE such a rule: `parse_rules` in `src/reason.rs`
/// rejects "a head variable the body never binds", and `reason_horn_emit_test.rs` gates
/// it. That guard is in the PRODUCER only. `oo-horn` is a checker anyone may point at any
/// rule file, and it has no such guard, so the guarantee evaporates exactly when the
/// certificate did not come from this engine — which is the only case in which an
/// independent checker is worth having.
#[test]
fn divergence_d2b_unsafe_rule_head() {
    if skip() {
        return;
    }
    let rules = differential_fixture("unsafehead_rules.tsv");
    let asserted = differential_fixture("unsafehead_asserted.tsv");
    let cert = differential_fixture("unsafehead_cert.tsv");
    if common::skip_unless(
        rules.exists() && asserted.exists() && cert.exists(),
        "isabelle/fixtures-differential/unsafehead_*.tsv",
        "they are committed",
    ) {
        return;
    }

    // The conclusion the certificate claims really does carry a bare `z`. If this ever
    // stops being true the test below is checking something else.
    let text = std::fs::read_to_string(&cert).unwrap();
    let step = parse_step(text.lines().next().unwrap()).expect("the probe must parse");
    assert_eq!(step.concl[2], "z", "the claimed conclusion must carry the bare term `z`: {text}");
    assert!(
        !step.binds.iter().any(|(k, _)| k == "z"),
        "and the binding must NOT mention z, or there is nothing to fabricate: {text}"
    );

    let lean = run_lean(&rules, &asserted, &cert);
    let isa = run_isabelle(&rules, &asserted, &cert);
    assert_eq!(
        lean.exit, 0,
        "Lean accepts a conclusion containing a term minted from a variable's name"
    );
    assert_eq!(lean.verdict.as_deref(), Some("entailed_under_supplied_rules"));
    assert_eq!(isa.exit, 1, "Isabelle rejects: binding_incomplete");
    assert_ne!(lean, isa, "if these ever agree, D2b has been resolved and this test should say how");
}

/// The corners of the term format that no generated certificate reaches. Both
/// formalisations flag them as untested and each names a different reason to worry:
/// Isabelle's DECISION M38 says the fixtures are pure ASCII, "which is exactly the
/// circumstance in which a String.literal implementation would stay silent", and its M1
/// says terms are opaque byte strings with no value-space normalisation.
///
/// Both concerns are settled here, empirically, in the agreeing direction:
///
/// * A non-ASCII IRI round-trips through both checkers, and altering one byte of it is
///   rejected by both. Isabelle's verified core is over `string = char list` and its
///   driver uses SML's own `String.explode` on a byte string, so the bytes reach the
///   theorem unchanged; the ASCII trap M38 warns about is a trap that was avoided, not
///   one that was never there.
/// * `"01"^^xsd:integer` and `"1"^^xsd:integer` are ONE value and TWO terms, and both
///   checkers reject a certificate that swaps one for the other. M1's scope note holds
///   on both sides: no datatype-aware rule is in the table, and neither checker
///   normalises.
/// * `http://ex.org/a` without angle brackets does not collide with `<http://ex.org/a>`
///   on either side, which is the injectivity that Isabelle's DECISION D-PARSE-2 needs
///   for bracket-stripping to be invisible to the accept/reject bit. Isabelle strips the
///   brackets and Lean does not, so if the renaming were not injective this is where the
///   two would part company.
#[test]
fn the_untested_corners_of_the_term_format_agree() {
    if skip() {
        return;
    }
    // (probe, expected exit, what it is for). The exit code rather than a bare bit,
    // because 2 is a THIRD answer and a checker that turned an unparseable file into a
    // rejection would still look like agreement on the accept/reject bit alone.
    let expected: &[(&str, i32, &str)] = &[
        ("utf8", 0, "non-ASCII UTF-8 IRIs in the rule, the graph and the certificate"),
        ("utf8bad", 1, "one byte of a non-ASCII IRI altered in the certificate"),
        ("literals", 0, "a language-tagged literal and a datatyped literal"),
        ("litdt", 1, "\"01\"^^xsd:integer standing in for \"1\"^^xsd:integer"),
        ("bnode", 0, "blank node labels in every position"),
        ("degen", 0, "the degenerate spellings <> and _:"),
        ("degen2", 0, "a bare < and an empty field as terms"),
        ("inject", 1, "an IRI without its angle brackets, against one with them"),
        ("emptybody", 0, "a rule with an empty body, cited with no premises"),
        ("repeated", 0, "a rule whose body repeats one atom, cited twice"),
        ("extrabind", 0, "a binding for a variable the rule never mentions"),
        ("qmarkkey", 1, "binding keys written WITH the question mark"),
        // Degenerate files, where an off-by-one in either parser would show up.
        ("emptyall", 0, "an empty rule table and an empty certificate"),
        ("emptyrules", 1, "an empty rule table and a step that cites rule 0"),
        ("emptygraph", 0, "an empty graph and a rule with an empty body"),
        ("allempty", 0, "all three files empty"),
        ("duprow", 0, "the built-in table with one row duplicated after the cited index"),
        ("trailtab", 2, "a trailing tab on every certificate line"),
        ("crlf", 1, "CRLF line endings, so every last field carries a stray carriage return"),
        ("blank", 0, "blank lines at the start and end of all three files"),
        ("nonl", 0, "no trailing newline anywhere"),
        ("hugeidx", 1, "a rule index of 200 digits"),
    ];
    let dir = isabelle_dir().join("fixtures-differential");

    // Two probes are about BYTES, and `.gitattributes` says `*.tsv text eol=lf`, which
    // would rewrite one of them into a file that tests nothing while still reporting
    // green. A `-text` exception keeps the carriage returns; this is the guard that
    // notices if the exception is ever dropped, because a probe that has been normalised
    // away passes silently and that is the failure this repository exists to catch.
    for f in ["probe_crlf_rules.tsv", "probe_crlf_asserted.tsv", "probe_crlf_cert.tsv"] {
        let p = dir.join(f);
        if p.exists() {
            let bytes = std::fs::read(&p).unwrap();
            assert!(
                bytes.contains(&b'\r'),
                "{f} has lost its carriage returns. `.gitattributes` normalises *.tsv to \
                 LF and this file needs the `-text` exception; without the CR it is a \
                 probe that passes without probing anything"
            );
        }
    }
    let p = dir.join("probe_nonl_cert.tsv");
    if p.exists() {
        let bytes = std::fs::read(&p).unwrap();
        assert!(
            !bytes.ends_with(b"\n"),
            "probe_nonl_cert.tsv is supposed to end WITHOUT a newline; something has \
             added one and the probe now tests the ordinary case"
        );
    }

    let mut checked = 0;
    for (name, want_exit, what) in expected {
        let r = dir.join(format!("probe_{name}_rules.tsv"));
        let a = dir.join(format!("probe_{name}_asserted.tsv"));
        let c = dir.join(format!("probe_{name}_cert.tsv"));
        if common::skip_unless(
            r.exists() && a.exists() && c.exists(),
            &format!("isabelle/fixtures-differential/probe_{name}_*.tsv"),
            "they are committed",
        ) {
            continue;
        }
        let lean = run_lean(&r, &a, &c);
        let isa = run_isabelle(&r, &a, &c);
        assert_eq!(lean, isa, "the two kernels disagree on {name} ({what})");
        assert_eq!(
            lean.exit, *want_exit,
            "{name} ({what}) was expected to exit {want_exit}, and both kernels say \
             {}. Agreement on the WRONG answer is the failure mode a differential cannot \
             see on its own, which is why the expected answer is written down here",
            lean.exit
        );
        checked += 1;
    }
    assert_eq!(checked, expected.len(), "every probe must have run");

    // Every committed probe must appear in the table above. Without this, adding a
    // fixture and forgetting to say what it should do would leave it checked for
    // agreement only, which is the weaker half.
    let listed: std::collections::BTreeSet<&str> = expected.iter().map(|(n, _, _)| *n).collect();
    let on_disk: Vec<String> = probe_cases()
        .iter()
        .map(|c| c.name.trim_start_matches("probe-").to_string())
        .collect();
    for name in &on_disk {
        assert!(
            listed.contains(name.as_str()),
            "isabelle/fixtures-differential/probe_{name}_*.tsv is committed but this test \
             does not say what it should do"
        );
    }
}

/// Agreement is about the checking discipline. It is not a proof, and nothing in this
/// file's output may be read as one.
///
/// This test exists because the claim is easy to overstate and the overstatement is the
/// exact failure the project is built to catch. It pins the two facts that bound what
/// the differential can mean: a certificate that is accepted over a USER table earns the
/// relativised verdict on BOTH sides, and the two sides name DIFFERENT theorems for it,
/// because each side's warrant is its own.
#[test]
fn agreement_is_about_the_definitions_and_is_not_itself_a_proof() {
    if skip() {
        return;
    }
    let rules = horn_fixture("user_rules.tsv");
    let asserted = horn_fixture("asserted.tsv");
    let cert = horn_fixture("good.tsv");

    let lean_out = Command::new(lean_checker())
        .arg("check")
        .arg(&rules)
        .arg(&asserted)
        .arg(&cert)
        .output()
        .expect("run oo-horn");
    let lean_json = String::from_utf8_lossy(&lean_out.stdout).to_string();
    let isa_out = Command::new(isabelle_checker())
        .arg("check")
        .arg(&rules)
        .arg(&asserted)
        .arg(&cert)
        .output()
        .expect("run oo-horn-isabelle");
    let isa_json = String::from_utf8_lossy(&isa_out.stdout).to_string();

    assert_eq!(json_field(&lean_json, "verdict").as_deref(), Some("entailed_under_supplied_rules"));
    assert_eq!(json_field(&isa_json, "verdict").as_deref(), Some("entailed_under_supplied_rules"));

    let lean_thm = json_field(&lean_json, "theorem").unwrap();
    let isa_thm = json_field(&isa_json, "theorem").unwrap();
    assert_ne!(
        lean_thm, isa_thm,
        "each side must name ITS OWN theorem. If they ever printed the same string, a \
         reader could take one side's agreement as the other side's warrant, which is \
         precisely the laundering this layer exists to prevent"
    );
    assert!(lean_thm.starts_with("OOCert."), "{lean_thm}");
    assert!(isa_thm.starts_with("OOHorn."), "{isa_thm}");

    for json in [&lean_json, &isa_json] {
        assert!(
            json.contains("assumed, not checked"),
            "a run over a user table must say the rules are assumed: {json}"
        );
    }
}
