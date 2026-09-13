# Derivation certificates and the Lean checker

Every inference the forward-chaining reasoner makes can be written out with the rule that
produced it and the premises the rule read, and a checker in `lean/` verifies that record against a
formal semantics. The checker's soundness is a machine-checked theorem, so a certificate it accepts
contains only triples entailed by the asserted graph, whatever the Rust engine did to find them.

This page is the how-to. The design and its limits are in
[decision 0002](decisions/0002-an-inference-carries-a-certificate.md).

## Produce a certificate

```bash
# CLI: any of rdfs, owl-rl, owl-rl-ext. The tableaux path (owl-dl) refuses the flag.
open-ontologies load ontology.ttl
open-ontologies reason --profile owl-rl-ext --certificate /tmp/cert

# Batch, when the store is in-memory per process:
printf 'load ontology.ttl\nreason --profile owl-rl-ext --certificate /tmp/cert\n' \
  | open-ontologies --no-connect --data-dir /tmp/store batch -
```

Over MCP, `onto_reason` takes `certificate_dir`. The response gains a `certificate` object:

```json
{
  "inferred_count": 268,
  "certificate": {
    "dir": "/tmp/cert",
    "format": "oo-cert/1",
    "asserted": 1128,
    "derivations": 268,
    "by_rule": {"rdfs2": 41, "rdfs9": 190, "scm-eqc1": 3, "...": "..."},
    "check_with": "cd lean && lake exe oo-cert <dir>/asserted.tsv <dir>/derivations.tsv"
  }
}
```

`derivations` always equals `inferred_count`: one line per inferred triple, recorded the first time
it is derived.

## Check it

The checker needs a Lean 4 toolchain. [elan](https://github.com/leanprover/elan) installs the
version `lean/lean-toolchain` pins; nothing else is downloaded, the project has no dependencies.

```bash
cd lean
lake build                      # builds the checker AND checks the proofs
lake exe oo-cert /tmp/cert/asserted.tsv /tmp/cert/derivations.tsv
```

Exit codes: `0` every step checks; `1` a step was rejected, and the JSON on stdout names the first
one with its rule, conclusion and premises; `2` a file could not be read or parsed.

```json
{"ok":true,"asserted":1128,"derivations":268,"theorem":"OOCert.certificate_sound"}
```

## The files

Two tab-separated files. Terms are in N-Triples spelling, exactly as the engine's interner holds
them, so a term is spelled identically wherever it appears and tabs and newlines cannot occur
inside one.

- `asserted.tsv`: one triple per line, `s TAB p TAB o`. Every triple the run started from.
- `derivations.tsv`: one step per line, `rule TAB s TAB p TAB o` for the conclusion, then the
  premises as further triples, in the order documented per rule in `lean/OOCert/Rules.lean`.

## What is proved

`OOCert.certificate_sound` in `lean/OOCert/Soundness.lean`:

> if `checkCert G steps = true` then for every step, `G ⊨ step.conclusion`

where `G ⊨ t` is truth in every model of `G` under the semantics in `lean/OOCert/Semantics.lean`:
the RDF-based reading of the twenty rules' vocabulary, with each semantic condition the *if*
direction of the W3C condition or a consequence of it, never more. Weaker conditions admit more
interpretations, so the result carries over to the OWL 2 RDF-Based Semantics and to the Direct
Semantics read through triples.

The axioms the theorem depends on are pinned in the source by `#guard_msgs`:
`propext`, `Classical.choice`, `Quot.sound`. A `sorry`, or a `native_decide`, fails `lake build`.

## Why the theorem is not vacuous

A soundness theorem about an unsatisfiable semantics proves nothing: if no interpretation met the
conditions, every triple would be entailed and the checker could accept anything. `lean/OOCert/Witness.lean`
closes that by construction, and its own axiom lists are pinned the same way.

| theorem | says |
|---|---|
| `saturated_is_a_model` | every graph has a model, so the conditions are satisfiable and no graph is inconsistent here |
| `not_everything_is_entailed` | some triple is not entailed, so `Entails` is not the trivial relation |
| `the_old_svf_derivation_is_not_entailed` | `C ⊑ ∃p.D` with `x p y` and `y ∈ D` does **not** entail `x ∈ C` |
| `the_sound_half_survives` | the same premises **do** entail `x ∈ ∃p.D`, so the fix did not overshoot |

The third is the one worth reading. It is a machine-checked refutation of the derivation this engine
used to make: a model of the premises in which `x` is not a `C`. So the removed rule was unsound in
fact, not merely unjustified by the rule set the checker implements. The witness is the Herbrand
interpretation of the premises plus the single consequence the semantics does force.

## What is not proved

- Completeness. The checker rejects anything it cannot re-derive by pattern, including valid
  inferences in an order it does not expect. A rejection is a false alarm at worst, never a false
  pass.
- The parser and the file format (`lean/OOCert/Parse.lean`, `lean/Main.lean`). A parse error
  rejects.
- Anything outside the forward-chaining family: the SHACL validator (the pyshacl differential in
  `tools/shacl_differential.py` is its gate), the SHIQ tableaux reasoner, the RDF parsers.
- Datatype semantics. Two spellings of one literal value are two terms. No rule compares literals
  by value, so nothing is lost, but do not read `Entails` as datatype-aware.

## What it caught on day one

`cls-svf1` in the `owl-rl-ext` profile derived `x rdf:type C` from `C rdfs:subClassOf ∃p.D`,
`x p y` and `y rdf:type D`. That is the converse of the axiom. It also treated `x p D`, with `D` the
filler class IRI itself, as a witness. Neither has a sound rule, so neither could be given one in
the checker, and both are gone (`tests/reason_rl_ext_soundness_test.rs`). The old derivation is
kept in `tests/lean_certificate_test.rs` as a forged certificate the checker must reject.

## In CI

The `lean` job builds `lean/` (which is the proof check), then runs
`tests/lean_certificate_test.rs` with `OO_REQUIRE_FIXTURES=1`: every RDF file under
`case-studies/`, `demo/`, `tests/fixtures/`, `data/` and `examples/` is loaded, reasoned under
`owl-rl-ext` with a certificate, and the certificate checked. Files over 4 MB and files that do not
parse are listed with the reason, never dropped silently. The same test appends three forgeries
and requires each to be rejected.
