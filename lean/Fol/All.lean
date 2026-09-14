import Fol.Syntax
import Fol.Semantics
import Fol.Check
import Fol.Free
import Fol.Witness
import Fol.Parse

/-!
# `Fol`: a model certificate for an external SAT/SMT solver or finite model finder

The root module. Importing this builds every proof in the directory, including the axiom pins and
the format `#guard`s, so a `sorry`, a changed axiom footprint or a drifted digest anywhere fails
`lake build`.

* `Fol/Syntax.lean` the fragment, the monomorphisation and its one obligation, both file formats,
  a worked example with a measured digest, and a list of what is deliberately not covered.
* `Fol/Semantics.lean` structures, satisfaction, `Satisfiable` and `Entails`, transcribed from
  `OwlLean/FOL/Basic.lean`. Nothing here computes.
* `Fol/Check.lean` the decision procedure, `Fol.eval_iff`, `Fol.satisfiable_of_check`,
  `Fol.check_complete`, `Fol.not_entails_of_check`, and the coverage gate.
* `Fol/Free.lean` the coincidence lemma, and the upgrade that makes a rejection a statement about
  every assignment rather than the one the checker used.
* `Fol/Witness.lean` an accepted structure, a formula it refuses, five rejected forgeries and an
  unsatisfiable problem, so that neither the checker nor `Satisfiable` is trivial.
* `Fol/Parse.lean` the two file readers, the canonical printer and the digest. Outside the theorem.

The verdict vocabulary this layer plugs into, and the four solver verdicts that must never be
collapsed, are in `docs/decisions/0006-a-model-is-a-certificate-and-a-refutation-is-not.md`.
-/
