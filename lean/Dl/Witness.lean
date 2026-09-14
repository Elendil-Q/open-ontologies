import Dl.Check

/-!
# Witnesses: the checker accepts something, rejects something, and the semantics is not trivial

`satisfiable_of_checkModel` would be worth nothing if `checkModel` accepted everything, and
`checkModel_complete` would be worth nothing if it accepted nothing. This file closes both
by construction rather than by argument, and closes a third gap as well: that `Satisfiable`
is not a predicate that happens to hold of every axiom set.

1. `employment_model_is_accepted` exhibits an axiom set that uses an existential, a
   universal through `rdfs:range`, `rdfs:domain`, disjointness, an inverse role, a maximum
   number restriction and a non-emptiness claim, together with a model of it that the
   checker accepts. `employment_is_satisfiable` is the existence result read off it.

2. `forged_missing_successor_is_rejected` takes that same axiom set and the same
   interpretation with one role edge removed, the shape a hand-edited certificate would
   have, and proves it is NOT a model. The proof goes through `checkModel_complete`, so it
   is the checker's own rejection that is being certified, not an independent argument.

3. `forged_duplicate_successor_is_rejected` is the one that pins the counting. `≥2 r.B`
   needs two DISTINCT successors. The forged interpretation lists the same successor twice,
   which a length comparison that forgot to deduplicate would accept. It is rejected.

4. `bottom_class_is_unsatisfiable` exhibits an axiom set with no model at all, so
   `Satisfiable` is not trivially true and an accepted certificate is saying something.

The names here are bare strings rather than the `<iri>` spellings the emitter writes. The
checker never looks inside a name, so nothing depends on the difference, and short names
keep the kernel's evaluation of these `decide` calls quick.
-/
namespace Dl

/-! ## An ontology about employment -/

/-- `P ⊑ ∃w.C`, `P` and `C` disjoint, `w` has domain `P` and range `C`, `w` is the inverse
of `e`, a `C` employs at most one `P`, and `P` is not empty. -/
def employment : List Axiom :=
  [ .sub (.atom "P") (.ex "w" (.atom "C")),
    .disjoint (.atom "P") (.atom "C"),
    .dom "w" (.atom "P"),
    .rng "w" (.atom "C"),
    .inv "w" "e",
    .sub (.atom "C") (.max 1 "e" (.atom "P")),
    .nonempty (.atom "P") ]

/-- One person, one company, an employment edge and its inverse. -/
def employmentModel : Interp where
  dom := ["p", "c"]
  cext := fun a => if a = "P" then ["p"] else if a = "C" then ["c"] else []
  rext := fun r x =>
    if r = "w" && x = "p" then ["c"]
    else if r = "e" && x = "c" then ["p"]
    else []
  ind := fun _ => "p"

theorem employment_model_is_accepted : checkModel employmentModel employment = true := by decide

/-- The existence result, read off the accepted interpretation. -/
theorem employment_is_satisfiable : Satisfiable employment :=
  satisfiable_of_checkModel employment_model_is_accepted

/-! ## A model with a required successor removed -/

/-- The same interpretation with the `w` edge deleted. Everything else is untouched, so the
only axiom it can break is `P ⊑ ∃w.C`. -/
def employmentForged : Interp where
  dom := ["p", "c"]
  cext := fun a => if a = "P" then ["p"] else if a = "C" then ["c"] else []
  rext := fun r x => if r = "e" && x = "c" then ["p"] else []
  ind := fun _ => "p"

theorem forged_missing_successor_is_rejected : ¬ (employmentForged ⊨ employment) :=
  checkModel_complete (by decide)

/-! ## A model that lists one successor twice where two are required -/

/-- `A ⊑ ≥2 r.B`, and `A` is not empty. -/
def twoSuccessors : List Axiom :=
  [ .sub (.atom "A") (.min 2 "r" (.atom "B")),
    .nonempty (.atom "A") ]

/-- Two genuinely different `B`s. -/
def twoSuccessorsModel : Interp where
  dom := ["x", "y", "z"]
  cext := fun a => if a = "A" then ["x"] else if a = "B" then ["y", "z"] else []
  rext := fun r x => if r = "r" && x = "x" then ["y", "z"] else []
  ind := fun _ => "x"

theorem two_successors_model_is_accepted :
    checkModel twoSuccessorsModel twoSuccessors = true := by decide

theorem two_successors_is_satisfiable : Satisfiable twoSuccessors :=
  satisfiable_of_checkModel two_successors_model_is_accepted

/-- The same element offered twice. A checker that compared `≥2` against the raw length of
the successor list would accept this. -/
def twoSuccessorsForged : Interp where
  dom := ["x", "y", "z"]
  cext := fun a => if a = "A" then ["x"] else if a = "B" then ["y", "z"] else []
  rext := fun r x => if r = "r" && x = "x" then ["y", "y"] else []
  ind := fun _ => "x"

theorem forged_duplicate_successor_is_rejected : ¬ (twoSuccessorsForged ⊨ twoSuccessors) :=
  checkModel_complete (by decide)

/-! ## Satisfiability is not trivial -/

/-- An axiom set with no model: a class is claimed non-empty and contained in `⊥`.

The proof is not a `decide`, because "no interpretation whatsoever" is not a finite check.
It is the one-line argument: the non-emptiness claim produces a domain element in the class,
the subclass axiom sends it to `Sat I .bot`, and that is `False` by definition. -/
def emptyClaim : List Axiom := [.nonempty (.atom "A"), .sub (.atom "A") .bot]

theorem bottom_class_is_unsatisfiable : ¬ Satisfiable emptyClaim := by
  rintro ⟨I, M⟩
  obtain ⟨x, hx, hA⟩ := M.holds (.nonempty (.atom "A")) (by simp [emptyClaim])
  exact M.holds (.sub (.atom "A") .bot) (by simp [emptyClaim]) x hx hA

/-! ## Axioms, pinned -/

/-- info: 'Dl.employment_is_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms employment_is_satisfiable

/-- info: 'Dl.forged_missing_successor_is_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forged_missing_successor_is_rejected

/-- info: 'Dl.two_successors_is_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_successors_is_satisfiable

/-- info: 'Dl.forged_duplicate_successor_is_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forged_duplicate_successor_is_rejected

/-- info: 'Dl.bottom_class_is_unsatisfiable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bottom_class_is_unsatisfiable

end Dl
