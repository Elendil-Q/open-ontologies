import Fol.Semantics

/-!
# The decision procedure, and the theorems about it

`check M Γ` decides whether the finite structure `M` satisfies every formula of `Γ`.
`Fol.satisfiable_of_check` is what a solver's `sat` answer buys once a model comes with it: an
accepted structure is an existence proof, so the problem really is satisfiable.

`Fol.check_complete` is the other half and is what stops the layer being decoration. The checker
agrees with `Form.holds` in BOTH directions, so it rejects exactly the structures that fail some
formula. A checker that accepted everything would satisfy the soundness theorem just as well; this
one cannot.

`Fol.not_entails_of_check` is the result this layer exists for and is the exact dual of decision
0005. A refutation cannot be replayed in core Lean and stays an oracle opinion. A COUNTERMODEL is
a finite object, so a checked model of `¬φ :: Γ` is a machine-checked proof that `Γ` does not
entail `φ`, under the same `Entails` that `OwlLean.adequacy` is stated about.

## The carrier

`FinModel n` interprets everything over `Fin n`, and `toStruc` is only defined at `n = m + 1`, so
the carrier is a TYPE and it is non-empty by construction. Three consequences, all of which are
why this shape was chosen over a carrier given as a list of names:

* there is nothing outside the carrier, so this layer needs no well-formedness predicate and no
  domain-membership hypothesis anywhere;
* `const : Sym → Fin n` is total INTO the carrier, so "the constant denotes something outside the
  domain" is unrepresentable rather than merely excluded by a check that a bug could drop;
* `Env M.toStruc` unifies with `Nat → Fin (n+1)` definitionally, which is what lets the quantifier
  cases of `eval_iff` close in six lines each.

Everything here is `Bool`-valued and runs. No `native_decide`, no `Classical` case split on an
undecidable proposition, no Mathlib.
-/
namespace Fol

/-- A finite structure over `Fin n`.

All three fields are TOTAL, so a symbol the model file never mentioned still has an
interpretation: `false` everywhere, and element `0`. That is sound, because a defaulted structure
is still a structure and `check` validates it from scratch rather than trusting where it came
from. It is not free, because the object certified is then not the object the solver produced,
which is what `covers` and the strict parser are for.

The `false` default is not arbitrary and the reason is not soundness. It is chosen because its
FAILURE MODE IS REJECTION. Under a `true` default the all-true structure models any purely
positive theory, every certificate would check green, and the layer would be worthless while
staying sound. A reader who assumes the default was picked for soundness will feel free to change
it, so the argument is written here rather than left to be reconstructed. -/
structure FinModel (n : Nat) where
  p1 : Sym → Fin n → Bool
  p2 : Sym → Fin n → Fin n → Bool
  const : Sym → Fin n

/-- The finite structure read as a `Struc`.

`@[reducible]` is LOAD-BEARING. Without it `Env M.toStruc` will not unify with `Nat → Fin (n+1)`
and the quantifier cases of `eval_iff` fail with an application type mismatch on `update`. -/
@[reducible] def FinModel.toStruc {n : Nat} (M : FinModel (n+1)) : Struc where
  Dom := Fin (n+1)
  nonempty := ⟨0⟩
  p1 := fun p x => M.p1 p x = true
  p2 := fun p x y => M.p2 p x y = true
  c := M.const

/-- The computable counterpart of `update`. -/
def upd {n : Nat} (e : Nat → Fin n) (k : Nat) (d : Fin n) : Nat → Fin n :=
  fun m => if m = k then d else e m

/-- The computable counterpart of `Term.eval`. -/
def evalT {n : Nat} (M : FinModel n) (e : Nat → Fin n) : Term → Fin n
  | .var k => e k
  | .const c => M.const c

/-- The computable counterpart of `Form.holds`.

Structural recursion on `Form`, the LAST argument, with the environment varying. The recursive
call sits under a lambda handed to `List.all`, which Lean accepts because the decreasing argument
does not depend on that binder. No `termination_by`, no `decreasing_by`, the same shape as
`Dl.sat`. -/
def eval {n : Nat} (M : FinModel n) : (Nat → Fin n) → Form → Bool
  | e, .app1 p t => M.p1 p (evalT M e t)
  | e, .app2 p t u => M.p2 p (evalT M e t) (evalT M e u)
  | e, .eq t u => evalT M e t == evalT M e u
  | _, .tru => true
  | _, .fls => false
  | e, .neg f => !eval M e f
  | e, .and f g => eval M e f && eval M e g
  | e, .or f g => eval M e f || eval M e g
  | e, .imp f g => !eval M e f || eval M e g
  | e, .all k f => (List.finRange n).all (fun d => eval M (upd e k d) f)
  | e, .ex k f => (List.finRange n).any (fun d => eval M (upd e k d) f)

theorem evalT_eq {n : Nat} (M : FinModel (n+1)) (e : Nat → Fin (n+1)) (t : Term) :
    evalT M e t = Term.eval M.toStruc e t := by
  cases t <;> rfl

theorem upd_eq {n : Nat} (M : FinModel (n+1)) (e : Nat → Fin (n+1)) (k : Nat) (d : Fin (n+1)) :
    upd e k d = update (M := M.toStruc) e k d := rfl

/-- **The bridge.** The Boolean evaluator and the `Prop`-valued satisfaction relation agree, at
every formula and every environment.

`intro f` then `induction f`, leaving `e` in the goal: the environment MUST be generalised or the
quantifier cases have no usable induction hypothesis. -/
theorem eval_iff {n : Nat} (M : FinModel (n+1)) :
    ∀ (f : Form) (e : Nat → Fin (n+1)), eval M e f = true ↔ Form.holds M.toStruc e f := by
  intro f
  induction f with
  | app1 p t => intro e; simp [eval, Form.holds, FinModel.toStruc, evalT_eq]
  | app2 p t u => intro e; simp [eval, Form.holds, FinModel.toStruc, evalT_eq]
  | eq t u => intro e; simp [eval, Form.holds, evalT_eq, beq_iff_eq]
  | tru => intro e; simp [eval, Form.holds]
  | fls => intro e; simp [eval, Form.holds]
  | neg f ih => intro e; simp [eval, Form.holds, ← ih]
  | and f g ihf ihg => intro e; simp [eval, Form.holds, ihf, ihg]
  | or f g ihf ihg => intro e; simp [eval, Form.holds, ihf, ihg]
  | imp f g ihf ihg =>
      intro e
      simp only [eval, Form.holds, Bool.or_eq_true, Bool.not_eq_true']
      rw [← ihf, ← ihg]
      cases h : eval M e f <;> simp
  | all k f ih =>
      intro e
      simp only [eval, Form.holds, List.all_eq_true]
      constructor
      · intro h d
        rw [← ih]
        exact h d (List.mem_finRange d)
      · intro h d _
        rw [ih]
        exact h d
  | ex k f ih =>
      intro e
      simp only [eval, Form.holds, List.any_eq_true]
      constructor
      · rintro ⟨d, _, hd⟩
        exact ⟨d, (ih _).1 hd⟩
      · rintro ⟨d, hd⟩
        exact ⟨d, List.mem_finRange d, (ih _).2 hd⟩

/-- The whole check: every formula of the problem true in the structure, at the constant
assignment. Acceptance does not depend on that choice of assignment, because `Satisfiable` binds
the environment existentially; rejection does, and `Fol/Free.lean` is what removes the dependence
for a problem of sentences. -/
def check {n : Nat} (M : FinModel (n+1)) (Γ : List Form) : Bool :=
  Γ.all (fun g => eval M (fun _ => 0) g)

theorem check_iff {n : Nat} (M : FinModel (n+1)) (Γ : List Form) :
    check M Γ = true ↔ ∀ g ∈ Γ, Form.holds M.toStruc (fun _ => (0 : Fin (n+1))) g := by
  simp only [check, List.all_eq_true]
  exact ⟨fun h g hg => (eval_iff M g _).1 (h g hg),
         fun h g hg => (eval_iff M g _).2 (h g hg)⟩

/-- **Soundness.** An accepted finite structure is an existence proof: the problem really is
satisfiable, and the conclusion no longer mentions the structure the solver happened to build. -/
theorem satisfiable_of_check {n : Nat} {M : FinModel (n+1)} {Γ : List Form}
    (h : check M Γ = true) : Satisfiable Γ :=
  ⟨M.toStruc, (fun _ => (0 : Fin (n+1))), (check_iff M Γ).1 h⟩

/-- **Completeness, finite case.** The gate can fail, so a rejection is a statement about the
structure and not about the checker's patience: the checker accepts every structure that satisfies
the problem at the checked assignment. -/
theorem check_complete {n : Nat} {M : FinModel (n+1)} {Γ : List Form}
    (h : check M Γ = false) :
    ¬ (∀ g ∈ Γ, Form.holds M.toStruc (fun _ => (0 : Fin (n+1))) g) := by
  intro hm
  rw [(check_iff M Γ).2 hm] at h
  exact Bool.noConfusion h

/-- **The result this layer exists for.** A checked model of `¬φ :: Γ` is a machine-checked proof
that `Γ` does NOT entail `φ`, under the same `Entails` that `OwlLean.adequacy` is stated about.

This is the exact dual of decision 0005: a refutation cannot be replayed in core Lean and stays an
oracle opinion, while a countermodel is a finite object and is certified here. -/
theorem not_entails_of_check {n : Nat} {M : FinModel (n+1)} {Γ : List Form} {φ : Form}
    (h : check M (Form.neg φ :: Γ) = true) : ¬ Entails Γ φ := by
  intro hE
  have hall := (check_iff M _).1 h
  have hneg := hall (Form.neg φ) (by simp)
  exact hneg (hE M.toStruc _ (fun g hg => hall g (by simp [hg])))

/-- **Signature coverage: an attribution gate, NOT a soundness gate.**

Every symbol the problem uses is declared by the model file. Soundness holds WITHOUT this: a
symbol the file never declared is still interpreted, by the totality of `FinModel`'s fields, and
`check` validates the resulting structure from scratch. What the gate buys is that the structure
certified is the structure the solver described, rather than the solver's structure silently
completed with defaults.

Dressing this up as part of the soundness statement would be the laundering move, so it is kept
out of `Satisfiable`, out of `Models`, out of every theorem above, and reported at its own exit
code with its own reason string. -/
def covers (d1 d2 dc : List Sym) (Γ : List Form) : Bool :=
  (Γ.flatMap p1Syms).all (fun p => d1.contains p)
  && (Γ.flatMap p2Syms).all (fun p => d2.contains p)
  && (Γ.flatMap constSyms).all (fun c => dc.contains c)

/-! ## Axioms, pinned

`[propext, Quot.sound]`, and NOT the `[propext, Classical.choice, Quot.sound]` triple the rest of
this repository carries. That is a measurement rather than a preference: nothing in this file
needs choice, and pinning the habitual triple here would be looser than the truth and would stop
catching anything. `lean/Dl/Check.lean` already does the same for `checkWF_iff`. A `sorry` or a
`native_decide` anywhere above changes one of these lines and the build fails. -/

/-- info: 'Fol.eval_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_iff

/-- info: 'Fol.check_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_iff

/-- info: 'Fol.satisfiable_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms satisfiable_of_check

/-- info: 'Fol.check_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_complete

/-- info: 'Fol.not_entails_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_entails_of_check

end Fol
