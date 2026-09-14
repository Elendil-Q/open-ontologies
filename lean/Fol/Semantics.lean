import Fol.Syntax

/-!
# Satisfaction

The standard Tarskian semantics of the fragment, transcribed from `OwlLean/FOL/Basic.lean` in the
sibling project `owl-lean` clause for clause and monomorphised at `Sym`. Nothing in this file
computes; `Fol/Check.lean` carries the decision procedure and the proof that it agrees with what
is written here.

Two points a reader should check rather than take on trust.

**Why there is no well-formedness predicate.** `lean/Dl/Semantics.lean` carries `WellFormed` with
four clauses and every theorem there carries it as a hypothesis, because a `Dl.Interp` has a
carrier given as a LIST and extension maps that are total on `String`, so an extension can place
elements outside the carrier and `∃R.C` enumerates a successor list rather than the carrier. None
of that happens here. `Struc.Dom` is a TYPE, every quantifier ranges over that type, and atoms are
only ever tested, never enumerated. There is nothing outside the carrier to check. Copying
`Dl.WellFormed` into this layer would not be a shortcut, it would be a defect: `check_complete`
would then reject structures that are genuine models. This is the same observation from the other
side as `Dl/Syntax.lean`'s own docstring, which says that without `WellFormed` its statement
"would be much weaker than it looks".

**Non-emptiness is load-bearing and is carried in the structure.** `Struc.nonempty` is a field, not
a hypothesis, because a first-order structure with an empty carrier is not a structure: with one,
`∀x.⊥` would be true and "satisfiable" would mean nothing. `Fol/Witness.lean` proves
`all_false_is_unsatisfiable` from that field, which is how the layer demonstrates the field is
doing work rather than decorating.

**A deviation here is the one edit that silently unhooks the layer from `OwlLean.adequacy`.** The
OWL-level reading of a certified non-entailment rides on `Entails` below being the `Entails` that
theorem is stated about. That transcription is pinned by tests and is NOT proved; it is about
twenty lines of inductive types and their semantics rather than a translation, so it is a far
smaller claim than `src/tptp.rs`'s, and `docs/decisions/0006` says so rather than letting the two
sound equally load-bearing.
-/
namespace Fol

/-- A first-order structure: a non-empty carrier, an interpretation for each unary predicate
symbol, each binary predicate symbol, and each constant.

`c : Sym → Dom` is TOTAL into the carrier. That is not a convenience. In a design where a
constant's denotation is a lookup with a default, the default has to live somewhere, and a default
OUTSIDE the carrier makes `{∀x. P(x), ¬P(c)}` check green. Here that state is not representable. -/
structure Struc where
  Dom : Type
  nonempty : Nonempty Dom
  p1 : Sym → Dom → Prop
  p2 : Sym → Dom → Dom → Prop
  c : Sym → Dom

/-- A variable assignment. -/
abbrev Env (M : Struc) := Nat → M.Dom

/-- `e` with `n` rebound to `d`. -/
def update {M : Struc} (e : Env M) (n : Nat) (d : M.Dom) : Env M :=
  fun m => if m = n then d else e m

/-- What a term denotes. -/
def Term.eval (M : Struc) (e : Env M) : Term → M.Dom
  | .var n => e n
  | .const k => M.c k

/-- Satisfaction. -/
def Form.holds (M : Struc) : Env M → Form → Prop
  | e, .app1 p t => M.p1 p (t.eval M e)
  | e, .app2 p t u => M.p2 p (t.eval M e) (u.eval M e)
  | e, .eq t u => t.eval M e = u.eval M e
  | _, .tru => True
  | _, .fls => False
  | e, .neg f => ¬ f.holds M e
  | e, .and f g => f.holds M e ∧ g.holds M e
  | e, .or f g => f.holds M e ∨ g.holds M e
  | e, .imp f g => f.holds M e → g.holds M e
  | e, .all n f => ∀ d, f.holds M (update e n d)
  | e, .ex n f => ∃ d, f.holds M (update e n d)

/-- `Γ` has a model. This is the conclusion a certificate buys: not "the solver returned sat", but
the existence of a structure, exhibited. -/
def Satisfiable (Γ : List Form) : Prop :=
  ∃ (M : Struc) (e : Env M), ∀ g ∈ Γ, Form.holds M e g

/-- `Γ` entails `f`: true in every structure and every assignment satisfying `Γ`.

This is the relation `OwlLean.adequacy` is stated about, and the relation a certified countermodel
refutes. -/
def Entails (Γ : List Form) (f : Form) : Prop :=
  ∀ (M : Struc) (e : Env M), (∀ g ∈ Γ, Form.holds M e g) → Form.holds M e f

end Fol
