import Fol.Free

/-!
# Witnesses: the checker accepts something, rejects each forgery on its own, and the semantics is
not trivial

`satisfiable_of_check` would be worth nothing if `check` accepted everything, and `check_complete`
would be worth nothing if it accepted nothing. This file closes both by construction rather than
by argument, and closes a third gap as well: that `Satisfiable` is not a predicate that happens to
hold of every problem.

Every rejection below goes through `check_complete`, so it is the CHECKER'S OWN rejection that is
being certified rather than an independent argument about the same structure. A file that proved
these forgeries by hand would be proving something about the mathematics and nothing about the
gate the driver runs.

The five forgeries are the five ways of lying this format admits.

1. `forged_missing_edge_is_rejected`. A structure that omits what an axiom requires: the
   `worksFor` edge every `Person` needs is deleted and nothing else is touched.
2. `all_false_is_rejected` and `all_false_is_unsatisfiable`. The empty carrier. It is
   UNREPRESENTABLE here, because `FinModel.toStruc` is defined only at `n+1`, so the forgery has
   no Lean-level form at all; what is proved instead is that non-emptiness is load-bearing, since
   `∀x.⊥` is rejected by every structure and really has no model. The file-level half is the
   parser, which refuses `domain 0` with exit 2, demonstrated in `Fol/Parse.lean`.
3. `forged_arity_is_rejected`. A predicate interpreted at the wrong arity. In `FinModel` the arity
   is in the TYPE, so arity confusion cannot be a Lean-level error; it is a table-level fault and
   it is caught twice over. Here `worksFor` is supplied as a unary table, which leaves the binary
   slot empty and the `false` default rejects. In the parser a `p2` row for a symbol declared
   unary is exit 2. That double catch is the cleanest argument for the `false` default: its
   failure mode is rejection.
4. `an_undeclared_symbol_is_caught`, with `a_full_declaration_passes` so the gate is not a
   constant. A symbol the problem uses that the model file never declares. This is the ATTRIBUTION
   gate, not a soundness gate, and `Fol/Check.lean` says so at the definition.
5. `a_model_of_another_problem_is_rejected`. A perfectly good structure, checked against a problem
   it was not built for. The file-level half is the digest in `Fol/Parse.lean`.

`employment_does_not_entail_company` is the headline: a machine-checked NON-ENTAILMENT, which is
the sentence no automated theorem prover in decision 0005 can ever produce.

The names here are short bare strings rather than the prefixed `c:IRI` spellings the emitter
writes. The checker never looks inside a symbol, so nothing depends on the difference, and short
names keep the kernel's evaluation of these `decide` calls quick. `Fol/Parse.lean` carries the
digest pin over the real prefixed spellings, so the two conventions are both exercised.
-/
namespace Fol

/-! ## An ontology about employment -/

private def v (k : Nat) : Term := .var k
private def a : Term := .const "a"

/-- Nothing is both a thing and a literal, something is a thing, `a` is a thing, every `Person`
works for some `Company`, and `a` is a `Person`. The first three lines are the shape
`OwlLean.background` and `OwlLean.indAxioms` emit; the last two are a translated `subClassOf` with
a nested existential and a class assertion. -/
def employment : List Form :=
  [ .all 0 (.neg (.and (.app1 "thing" (v 0)) (.app1 "lit" (v 0)))),
    .ex 0 (.app1 "thing" (v 0)),
    .app1 "thing" a,
    .all 0 (.imp (.app1 "Person" (v 0))
              (.ex 1 (.and (.app2 "worksFor" (v 0) (v 1)) (.app1 "Company" (v 1))))),
    .app1 "Person" a ]

/-- Two elements: `a` at 0 is the person, 1 is the company, and there is one employment edge. -/
def employmentModel : FinModel 2 where
  p1 := fun p x =>
    if p = "thing" then true
    else if p = "Person" then x == 0
    else if p = "Company" then x == 1
    else false
  p2 := fun r x y => r == "worksFor" && x == 0 && y == 1
  const := fun _ => 0

/-- **G2, acceptance.** The checker accepts a real structure for a five-formula problem with a
nested existential under a universal. -/
theorem employment_is_accepted : check employmentModel employment = true := by decide

/-- **G2, the existence result read off it.** -/
theorem employment_is_satisfiable : Satisfiable employment :=
  satisfiable_of_check employment_is_accepted

/-- **G2, non-triviality of the semantics.** The same accepted structure does NOT satisfy
`Company(a)`. Without this the acceptance above would be consistent with a `holds` that is true of
everything. -/
theorem the_model_does_not_satisfy_everything :
    ¬ Form.holds employmentModel.toStruc (fun _ => (0 : Fin 2)) (.app1 "Company" a) := by
  intro h
  exact absurd ((eval_iff employmentModel (.app1 "Company" a) (fun _ => 0)).2 h) (by decide)

/-- A carrier of ONE is legal and is checked, so the layer does not quietly need two elements. -/
def singleton : FinModel 1 where
  p1 := fun p _ => p == "thing"
  p2 := fun _ _ _ => false
  const := fun _ => 0

theorem a_one_element_model_is_accepted :
    check singleton [.app1 "thing" a, .ex 0 (.app1 "thing" (v 0))] = true := by decide

theorem a_one_element_model_is_satisfiable :
    Satisfiable [.app1 "thing" a, .ex 0 (.app1 "thing" (v 0))] :=
  satisfiable_of_check a_one_element_model_is_accepted

/-! ## G3.1 A structure that omits what an axiom requires -/

/-- The same structure with the employment edge deleted. Everything else is untouched, so the only
formula it can break is the one that needs the edge. -/
def forgedNoEdge : FinModel 2 := { employmentModel with p2 := fun _ _ _ => false }

theorem forged_missing_edge_is_rejected :
    ¬ (∀ g ∈ employment, Form.holds forgedNoEdge.toStruc (fun _ => (0 : Fin 2)) g) :=
  check_complete (by decide)

/-- And the stronger sentence, because `employment` is a set of SENTENCES: the forgery is not a
model under ANY assignment, not merely under the one the checker used. -/
theorem forged_missing_edge_is_rejected_everywhere :
    ∀ e : Nat → Fin 2, ¬ (∀ g ∈ employment, Form.holds forgedNoEdge.toStruc e g) :=
  check_complete_closed (by decide) (by decide)

/-! ## G3.2 The empty carrier, and why non-emptiness is load-bearing -/

/-- No finite structure of this layer satisfies `∀x.⊥`, whatever its carrier and whatever it
interprets. An empty carrier would satisfy it, which is exactly why `FinModel.toStruc` is defined
only at `n+1` and why `Struc` carries `nonempty` as a field. -/
theorem all_false_is_rejected (n : Nat) (M : FinModel (n+1)) :
    check M [.all 0 .fls] = false := by
  simp [check, eval, List.finRange_succ]

/-- And the semantic fact behind it: `∀x.⊥` has no model at all. The proof is not a `decide`,
because "no structure whatsoever" is not a finite check. It is the one-line argument, and it uses
`Struc.nonempty`, which is what makes that field do work rather than decorate. -/
theorem all_false_is_unsatisfiable : ¬ Satisfiable [Form.all 0 .fls] := by
  rintro ⟨M, e, h⟩
  have hall := h (.all 0 .fls) (by simp)
  obtain ⟨d⟩ := M.nonempty
  exact hall d

/-- `Satisfiable` is not the trivial predicate. -/
theorem not_everything_is_satisfiable : ¬ Satisfiable [Form.fls] := by
  rintro ⟨M, e, h⟩
  exact h .fls (by simp)

/-! ## G3.3 A predicate interpreted at the wrong arity -/

/-- `worksFor` supplied as a UNARY table. The binary slot is then empty, the `false` default makes
the atom false wherever the problem uses it as a binary predicate, and the structure is rejected.
The parser refuses this file shape outright, so the fault is caught at both levels. -/
def forgedArity : FinModel 2 where
  p1 := fun p x =>
    if p = "thing" then true
    else if p = "Person" then x == 0
    else if p = "Company" then x == 1
    else if p = "worksFor" then x == 0
    else false
  p2 := fun _ _ _ => false
  const := fun _ => 0

theorem forged_arity_is_rejected :
    ¬ (∀ g ∈ employment, Form.holds forgedArity.toStruc (fun _ => (0 : Fin 2)) g) :=
  check_complete (by decide)

/-! ## G3.4 A symbol the problem uses that the model never declares

The coverage gate, which is about ATTRIBUTION and not about soundness. `Company` is missing from
the declared unary symbols, so the gate fails; adding it makes the gate pass, so the gate is not a
constant. -/

theorem an_undeclared_symbol_is_caught :
    covers ["thing", "lit", "Person"] ["worksFor"] ["a"] employment = false := by decide

theorem a_full_declaration_passes :
    covers ["thing", "lit", "Person", "Company"] ["worksFor"] ["a"] employment = true := by decide

/-! ## G3.5 A structure checked against a problem it was not built for -/

/-- A different problem entirely, and an inconsistent one. `employmentModel` is a perfectly good
structure and it is rejected here, because being a model is a relation between a structure and a
problem rather than a property of the structure. The file-level defence is the digest. -/
def otherProblem : List Form := [.app1 "Person" a, .neg (.app1 "Person" a)]

theorem a_model_of_another_problem_is_rejected :
    ¬ (∀ g ∈ otherProblem, Form.holds employmentModel.toStruc (fun _ => (0 : Fin 2)) g) :=
  check_complete (by decide)

/-! ## The headline: a machine-checked non-entailment -/

/-- **The sentence this layer exists to be able to say.** The employment theory does not entail
`Company(a)`, and the proof is a finite structure that was checked rather than a prover's opinion
that was believed.

Decision 0005 rules that an automated theorem prover's `SZS status Theorem` is an oracle opinion,
because a superposition refutation cannot be replayed in core Lean. This is the other direction,
and it is certified. -/
theorem employment_does_not_entail_company :
    ¬ Entails employment (.app1 "Company" a) :=
  not_entails_of_check (M := employmentModel) (by decide)

/-! ## Scale

The kernel's `decide`, not `native_decide`, which would add `Lean.ofReduceBool` to the footprint
and fail the audit. A carrier of 8 at quantifier depth 3 is 512 evaluation points per formula and
compiles in well under a second. If a witness ever gets slow, shrink the witness rather than
change the tactic. -/

def big : FinModel 8 where
  p1 := fun p x => p == "thing" || (p == "P" && x.val % 2 == 0)
  p2 := fun r x y => r == "r" && (x.val + 1) % 8 == y.val
  const := fun _ => 0

theorem big_is_accepted :
    check big [.all 0 (.all 1 (.ex 2 (.or (.app2 "r" (.var 0) (.var 2))
                                          (.app2 "r" (.var 1) (.var 2)))))] = true := by decide

/-! ## Axioms, pinned -/

/-- info: 'Fol.employment_is_satisfiable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms employment_is_satisfiable

/-- info: 'Fol.the_model_does_not_satisfy_everything' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms the_model_does_not_satisfy_everything

/-- info: 'Fol.a_one_element_model_is_satisfiable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms a_one_element_model_is_satisfiable

/-- info: 'Fol.forged_missing_edge_is_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms forged_missing_edge_is_rejected

/-- info: 'Fol.forged_missing_edge_is_rejected_everywhere' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms forged_missing_edge_is_rejected_everywhere

/-- info: 'Fol.all_false_is_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms all_false_is_rejected

/-- info: 'Fol.all_false_is_unsatisfiable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms all_false_is_unsatisfiable

/-- info: 'Fol.not_everything_is_satisfiable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms not_everything_is_satisfiable

/-- info: 'Fol.forged_arity_is_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms forged_arity_is_rejected

/-- info: 'Fol.an_undeclared_symbol_is_caught' does not depend on any axioms -/
#guard_msgs in
#print axioms an_undeclared_symbol_is_caught

/-- info: 'Fol.a_full_declaration_passes' does not depend on any axioms -/
#guard_msgs in
#print axioms a_full_declaration_passes

/-- info: 'Fol.a_model_of_another_problem_is_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms a_model_of_another_problem_is_rejected

/-- info: 'Fol.employment_does_not_entail_company' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms employment_does_not_entail_company

/-- info: 'Fol.big_is_accepted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms big_is_accepted

end Fol
