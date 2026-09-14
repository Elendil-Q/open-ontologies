# Lean certificate layer, design

Date: 2026-09-13. Status: implemented on branch `lean-certificate-layer`.

## Purpose

Give every inference the forward-chaining reasoner makes an independent, machine-checked
justification, so that trusting a materialised graph no longer means trusting the Rust that
produced it.

## Constraints that shaped it

- The request was "a Lean layer so all ontologies are correct, no bugs". No proof can deliver the
  literal reading: correctness of an ontology against the world is not a formal property. The
  deliverable is the strongest formal property available: **soundness of every reported
  inference**, checked per run by a program whose own correctness is a theorem.
- The reasoner is a hand-written rule engine (`src/reason.rs`). Verifying that code directly
  would mean re-implementing it in Lean and proving equivalence, which is large and brittle.
  Certifying its *output* is small and decoupled: the engine may change freely, the checker does
  not care how a derivation was found.
- Repository convention: core Lean only, small trust surface, every kill condition executable
  (see `~/projects/owl-lean`, the sibling formalisation this follows in style).
- A green run must mean something. Tests that cannot fail, and skips that look like passes, are
  the failure mode this repository exists to catch (`tests/common/mod.rs`).

## Architecture

```
  ontology (Turtle)
        │  load
        ▼
  GraphStore ──reason --certificate DIR──▶ asserted.tsv   (every asserted triple, s TAB p TAB o)
        │                                  derivations.tsv (rule TAB conclusion TAB premises…)
        │  materialise                            │
        ▼                                         ▼
  materialised graph                    lake exe oo-cert asserted.tsv derivations.tsv
                                                  │
                                        exit 0 ⇔ OOCert.checkCert = true
                                                  │
                                        theorem certificate_sound:
                                        checkCert G steps = true → ∀ st ∈ steps, G ⊨ st.conclusion
```

Components:

| unit | where | does | depends on |
|---|---|---|---|
| emitter | `src/reason.rs` (`Reasoner::run_full`) | records the first derivation of each inferred triple with rule id and premises; writes the two TSVs | the interner's N-Triples spellings |
| semantics | `lean/OOCert/Semantics.lean` | `Interp`, `Conditions`, `Chain`, `Model`, `Entails` | `Triple.lean` |
| checker | `lean/OOCert/Rules.lean` | `Rule`, `Step`, `takeChain`, `allTyped`, `checkStep`, `checkAll`, `checkCert` | `Std.HashSet` |
| proof | `lean/OOCert/Soundness.lean` | per-rule lemmas, `checkAll_sound`, `certificate_sound`, axiom tripwire | checker + semantics |
| front end | `lean/OOCert/Parse.lean`, `lean/Main.lean` | TSV parsing, exit codes, diagnostic naming the first rejected step | unverified by design |
| gate | `tests/lean_certificate_test.rs`, CI job `lean` | builds the checker, certifies every shipped ontology, proves the gate rejects forgeries | `lake` on PATH |

## Data flow and contract

- One certificate line per inferred triple; `derivations == inferred_count` is asserted by the
  tests.
- Premise order per rule is fixed and documented in `Rules.lean`. The emitter and the checker are
  held to it by a test that fires all twenty rules and requires the certificate to be accepted.
- The list constructors' chain triples must be asserted; every other premise may be asserted or
  previously derived.
- Blank nodes are constants scoped to one certificate (the skolemised reading). Both files come
  from one run, so labels agree.

## Semantics, in one paragraph

An interpretation is a domain, a denotation for every term, and one relation `iext p x y`. A
triple holds when its predicate's extension contains its subject and object; class membership is
`rdf:type`'s extension. Schema meaning lives in `Conditions`, each the *if* half of the W3C
RDF-based condition or a consequence of it, never more. Lists are read off the asserted graph
(`Chain`), as the W3C tables do. `G ⊨ t` is truth in every model of `G`.

## Error handling

- Parse error in either file: exit 2, nothing accepted.
- Any step rejected: exit 1 with the index, rule, conclusion and premises of the first rejected
  step (from an unverified diagnostic pass that runs only after the verified checker said no).
- `owl-dl` with a certificate directory: the engine refuses with a message; it has no rule trace.
- `lake` missing locally: the Rust tests skip through `common::skip_unless`, printing the marker;
  CI sets `OO_REQUIRE_FIXTURES=1` so the skip is a failure there.

## Testing

- `every_rule_family_appears_in_an_accepted_certificate`: all twenty rules, accepted.
- `a_forged_conclusion_is_rejected`, `a_premise_outside_the_graph_is_rejected`,
  `the_derivation_the_old_svf_rule_made_is_rejected`: the gate fails when it should.
- `every_shipped_ontology_certifies`: walks `case-studies/`, `demo/`, `tests/fixtures/`, `data/`,
  `examples/`; files over 4 MB and files that do not parse are listed with the reason, never
  dropped silently; at least 30 files must certify and at least one inference must be checked.
- `lean/`'s own build is the proof check; `#guard_msgs` pins the axiom list.

## Out of scope, stated

SHACL (pyshacl differential remains the gate), the SHIQ tableaux reasoner (would need
model or refutation certificates; SHIQ lacks the finite model property so this is real work), the
RDF parsers, datatype-aware literal semantics, and `owl:sameAs` beyond symmetry.
