# 0002 · An inference carries a certificate, and the certificate has a proof

- **Status**: implemented for the forward-chaining family (`rdfs`, `owl-rl`, `owl-rl-ext`) ·
  `reason --certificate DIR`, `onto_reason` with `certificate_dir`, batch `reason --certificate` ·
  checker in `lean/` with `OOCert.certificate_sound` machine-checked, axioms pinned by
  `#guard_msgs` · every shipped ontology certified in CI (`tests/lean_certificate_test.rs`) ·
  **opt-in, default unchanged** · the `owl-dl` tableaux path refuses the flag rather than
  pretending · the SHIQ tableaux reasoner now certifies its POSITIVE answers
  (`Dl.satisfiable_of_checkModel`, decision 0006); its negative answers and the
  parsers remain uncovered
- **Written**: 2026-09-13
- **Related**: decision 0001 (an inference is not an assertion); issues #131 and #132, fixed the
  same day; `tests/reason_rl_ext_soundness_test.rs`, the first thing the layer caught

## The problem

The engine's inferences were trusted because the engine was trusted. The reasoner is a few hundred
lines of Rust applying rules by hand, and on 13 September 2026 two of those rules turned out to be
unsound: `cls-svf1` derived membership in a class from membership in its restriction *superclass*
(the converse of the axiom), and it treated a class IRI in object position as an instance of that
class. Both had been there since the extended profile was written. Both were found not by a test
but by asking, rule by rule, "what semantic condition would make this sound", and finding none.

A test suite catches the bugs someone thought of. What was missing is a check that does not depend
on the engine's author having thought of the bug.

## Decisions

1. **The reasoner emits a certificate, not a claim.** With `--certificate DIR` every inferred
   triple is written with the rule that produced it and the premises the rule read, in a fixed
   order per rule. The asserted graph goes beside it. Nothing about the engine's internals is
   needed to read the two files.
2. **The checker re-derives, it does not search.** `OOCert.checkStep` matches the premises
   against the rule's shape, checks each premise is asserted or was concluded by an earlier step,
   and checks the conclusion is the one the rule yields. No fixpoint, no indices, no search: a few
   hundred lines that a reader can hold at once.
3. **The checker's soundness is a theorem, not a test.** `OOCert.certificate_sound` states that a
   certificate the checker accepts contains only triples entailed by the asserted graph under the
   RDF-based semantics of the vocabulary the rules use (`lean/OOCert/Semantics.lean`). The proof
   is one lemma per rule plus an induction over the certificate. `#guard_msgs` pins the axioms to
   `propext`, `Classical.choice` and `Quot.sound`; a `sorry` or a `native_decide` fails the build.
4. **The semantic conditions are the weakest the rules need.** Each is the *if* direction of the
   corresponding W3C condition or a consequence of it. Weaker conditions admit more
   interpretations, so soundness here implies soundness under the OWL 2 RDF-Based Semantics and
   under the Direct Semantics read through triples. Where the W3C reads a list off the graph, so
   does `Model`, through `Chain`.
5. **The theorem is shown non-vacuous in the same directory.** A soundness result about an
   unsatisfiable semantics proves nothing, so `lean/OOCert/Witness.lean` exhibits a model of an
   arbitrary graph, exhibits a triple that is not entailed, and proves that the derivation
   `cls-svf1` used to make is refuted by a model of its own premises while the half the reasoner
   still makes is entailed. That last pair turns "we removed a rule we could not justify" into "we
   removed a rule that was unsound", machine-checked.
6. **Core Lean only.** No Mathlib. `Std.HashSet` for membership, with its own lemmas bridging to
   list membership in the proof. The trust surface is the Lean kernel plus `lean/`.
7. **The gate is proved able to fail.** The test suite appends a forged conclusion, a premise
   outside the graph, and the exact line the old `cls-svf1` emitted, and requires each to be
   rejected. A gate that cannot fail is decoration.
8. **The reasoner derives less from malformed lists.** `owl:intersectionOf` and `owl:unionOf`
   lists are read only when every node carries `rdf:first` and `rdf:rest` and the chain reaches
   `rdf:nil`. The old lenient walk fired the class rules on whatever it recovered; the checker has
   no rule for a list it cannot walk, so neither does the reasoner. Deriving less from malformed
   input is the sound direction.

## What this does not claim

It does not make ontologies "correct". It makes every OWL-RL inference the engine reports
independently checkable against a formal semantics with a proved checker. Whether an ontology says
what its author meant is a different question and no proof answers it. The SHACL validator, the
RDF parsers are outside the theorem. The SHIQ tableaux reasoner is partly inside it now: when it
answers that a class is satisfiable or an ontology consistent it has built a completion graph, that
graph is a model, and `Dl.checkModel` verifies it. When it answers unsatisfiable or inconsistent it
still carries no certificate, because that needs a refutation rather than a model, and the report
says so rather than leaving the reader to assume symmetry. The differential oracle
against pyshacl (`tools/shacl_differential.py`) remains the gate for SHACL.
