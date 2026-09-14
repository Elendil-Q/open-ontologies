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
4. **The semantic conditions are the weakest the rules need**, with fourteen exceptions that were
   found later and are now discharged; see the correction at the foot of this record. Each of the
   rest is the *if* direction of the corresponding W3C condition or a consequence of it. Weaker
   conditions admit more interpretations, so soundness here implies soundness under the OWL 2
   RDF-Based Semantics, and since 15 September 2026 that implication is a theorem
   (`OOCert.W3CEntails.of_entails`) rather than an argument in a docstring. `Model` reads a list
   off the asserted graph through `Chain`, which is weaker than the specification's semantic
   sequence relation and so keeps the model class larger.
5. **The theorem is shown non-vacuous in the same directory.** A soundness result about an
   unsatisfiable semantics proves nothing, so `lean/OOCert/Witness.lean` exhibits a model of an
   arbitrary graph, exhibits a triple that is not entailed, and proves that the derivation
   `cls-svf1` used to make is refuted by a model of its own premises while the half the reasoner
   still makes is entailed. That last pair turns "we removed a rule we could not justify" into "we
   removed a rule that was unsound", machine-checked. Those refutations are about this layer's own
   model class and not about the specification's; the correction below says why, and which one now
   has a conforming replacement.
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

## Correction, 15 September 2026

An independent second formalisation in Isabelle/HOL, written from the W3C specifications with the
Lean deliberately unread, found two things wrong with decisions 4 and 5 above. Both are recorded
here rather than quietly edited, because the original wording is what the project told people.

**Fourteen arms were not the weakest condition the rule needs. They were the rule.** Twelve of them
(`scm-eqc1` and `scm-eqp1`, two conclusions each, plus `scm-svf1`, `scm-svf2`, `scm-avf1`,
`scm-avf2`, `scm-dom1`, `scm-dom2`, `scm-rng1`, `scm-rng2`) are stated by no cell of any
specification table, and `rdfs5` and `rdfs11` were licensed but redundant. For those arms the
machine-checked content was close to nothing: the theorem said the rule was sound because a field of
the condition record said so. All fourteen are now derived from quoted cells in
`lean/OOCert/W3C.lean`, and every derivation is a proof term depending on no axiom at all. The cell
that makes them derivable is Table 5.8's connective, which carries `rowspan="4"` in the
specification's HTML and therefore states an `iff`, not the `if-then` that RDFS alone gives.

**The claim about the OWL 2 Direct Semantics read through triples is withdrawn.** It was never
verified, and it is false as written for those twelve arms.

**The claim that the W3C reads a list off the graph is withdrawn.** The specification's sequence
notation quantifies over `IEXT(I(rdf:first))` and `IEXT(I(rdf:rest))`, never over the graph, and it
says explicitly that no semantic constraint enforces well-formed sequence structures. `Chain` is
still the right thing to use, but for the opposite reason to the one given: it fires on strictly
fewer lists, so the conditions over it are weaker and the model class is larger.

**Non-entailment never transferred outward and the record did not say so.** A model of the weaker
conditions need not be a conforming interpretation, so a refutation built from one is a statement
about this layer's model class alone. That covers every `¬ Entails`, every `¬ Unsat` and every
exhibited `Model` in the repository. One of them now has a conforming replacement,
`the_natural_avf2_direction_is_not_w3c_entailed` in `lean/OOCert/W3CWitness.lean`; the rest stay
open with the obstruction written at each of them.

Neither finding is a soundness bug. Both are the layer claiming more than it had earned, which by
this project's own standard is the same category of defect.
