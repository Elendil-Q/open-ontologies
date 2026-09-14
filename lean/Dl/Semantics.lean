import Dl.Syntax

/-!
# Satisfaction

The standard set-theoretic semantics of the covered fragment, written against the finite
interpretation of `Dl/Syntax.lean`. Nothing in this file computes; `Dl/Check.lean` carries
the decision procedure and the proof that it agrees with what is written here.

Two points a reader should check rather than take on trust.

**Counting.** `≥n R.C` and `≤n R.C` are stated with `AtLeast` and `AtMost`, which say "there
is a list of `n` DISTINCT witnesses" and "every list of distinct witnesses is at most `n`
long". They are deliberately not phrased through any deduplication function, because that
would make the meaning of a number restriction depend on a piece of the checker. The bridge
from a computed count to these statements is a theorem in `Dl/Check.lean`, proved from a
pigeonhole lemma, not a definition.

**Where satisfaction is evaluated.** A subclass axiom quantifies over `I.dom` and nothing
else. `WellFormed` is what makes that enough: it says every role successor of a domain
element is again a domain element, so the recursion in `Sat` never leaves the domain, and a
subclass axiom that holds at every element of `I.dom` holds at every element the model has.
Without `WellFormed` the statement would be much weaker than it looks, which is why
`Models` carries it and every theorem here does too.
-/
namespace Dl

/-- There are at least `n` distinct elements satisfying `P`. -/
def AtLeast (n : Nat) (P : Name → Prop) : Prop :=
  ∃ ys : List Name, ys.Nodup ∧ ys.length = n ∧ ∀ y ∈ ys, P y

/-- There are at most `n` distinct elements satisfying `P`. -/
def AtMost (n : Nat) (P : Name → Prop) : Prop :=
  ∀ ys : List Name, ys.Nodup → (∀ y ∈ ys, P y) → ys.length ≤ n

/-- `x` is in the extension of `c`. -/
def Sat (I : Interp) : Concept → Name → Prop
  | .top, _ => True
  | .bot, _ => False
  | .atom a, x => x ∈ I.cext a
  | .neg c, x => ¬ Sat I c x
  | .and c d, x => Sat I c x ∧ Sat I d x
  | .or c d, x => Sat I c x ∨ Sat I d x
  | .ex r c, x => ∃ y ∈ I.rext r x, Sat I c y
  | .all r c, x => ∀ y ∈ I.rext r x, Sat I c y
  | .min n r c, x => AtLeast n (fun y => y ∈ I.rext r x ∧ Sat I c y)
  | .max n r c, x => AtMost n (fun y => y ∈ I.rext r x ∧ Sat I c y)

/-- `I` satisfies the axiom.

`invfunc` is the one clause that has no concept-level counterpart. `≤1 R⁻.⊤` cannot be
written as a concept here unless `R` happens to have a named inverse, so inverse
functionality is an axiom in its own right and is stated the way the OWL 2 Direct Semantics
states it: no element has two distinct `R`-predecessors. -/
def Holds (I : Interp) : Axiom → Prop
  | .sub c d => ∀ x ∈ I.dom, Sat I c x → Sat I d x
  | .disjoint c d => ∀ x ∈ I.dom, ¬ (Sat I c x ∧ Sat I d x)
  | .dom r c => ∀ x ∈ I.dom, I.rext r x ≠ [] → Sat I c x
  | .rng r c => ∀ x ∈ I.dom, ∀ y ∈ I.rext r x, Sat I c y
  | .subrole r s => ∀ x ∈ I.dom, ∀ y ∈ I.rext r x, y ∈ I.rext s x
  | .trans r => ∀ x ∈ I.dom, ∀ y ∈ I.rext r x, ∀ z ∈ I.rext r y, z ∈ I.rext r x
  | .sym r => ∀ x ∈ I.dom, ∀ y ∈ I.rext r x, x ∈ I.rext r y
  | .inv r s =>
      (∀ x ∈ I.dom, ∀ y ∈ I.rext r x, x ∈ I.rext s y) ∧
      (∀ x ∈ I.dom, ∀ y ∈ I.rext s x, x ∈ I.rext r y)
  | .invfunc r => ∀ y ∈ I.dom, AtMost 1 (fun x => x ∈ I.dom ∧ y ∈ I.rext r x)
  | .inst a c => Sat I c (I.ind a)
  | .rel a r b => I.ind b ∈ I.rext r (I.ind a)
  | .indiv a => I.ind a ∈ I.dom
  | .nonempty c => ∃ x ∈ I.dom, Sat I c x

/-- The interpretation is a genuine finite interpretation of `A`'s vocabulary.

Without the first clause every subclass axiom holds vacuously in the empty interpretation
and "satisfiable" would mean nothing. Without the others the extension maps could place
elements outside the carrier, and `Sat` could then be evaluated at a point no axiom ever
constrains. -/
structure WellFormed (I : Interp) (A : List Axiom) : Prop where
  /-- The carrier is not empty. -/
  nonempty : I.dom ≠ []
  /-- No atomic concept the axiom set mentions reaches outside the carrier. -/
  cextInDom : ∀ a ∈ atomNames A, ∀ x ∈ I.cext a, x ∈ I.dom
  /-- No role the axiom set mentions leads outside the carrier. -/
  rextInDom : ∀ r ∈ roleNames A, ∀ x ∈ I.dom, ∀ y ∈ I.rext r x, y ∈ I.dom
  /-- Every individual the axiom set mentions denotes a carrier element. -/
  indInDom : ∀ a ∈ indNames A, I.ind a ∈ I.dom

/-- `I` is a model of `A`. -/
structure Models (I : Interp) (A : List Axiom) : Prop where
  wf : WellFormed I A
  holds : ∀ a ∈ A, Holds I a

@[inherit_doc] scoped notation:50 I " ⊨ " A => Models I A

/-- `A` has a finite model. This is the conclusion a certificate buys: not "the tableau ran
without a clash", but the existence of an interpretation, exhibited. -/
def Satisfiable (A : List Axiom) : Prop := ∃ I : Interp, I ⊨ A

theorem Satisfiable.intro {I : Interp} {A : List Axiom} (h : I ⊨ A) : Satisfiable A := ⟨I, h⟩

end Dl
