import Fol.Check

/-!
# What a rejection says when the problem is a set of sentences

`check` evaluates at the single assignment `fun _ => 0`. For ACCEPTANCE that costs nothing:
`Satisfiable` binds the environment existentially, so `satisfiable_of_check` is already the
strongest statement available. For REJECTION it costs something real. `check_complete` says only
that the structure fails some formula UNDER THAT ONE ASSIGNMENT, and for a problem with a free
variable in it that is genuinely weaker than "this is not a model".

The export in `src/tptp.rs` emits sentences, so the gap is normally empty. It is closed here
rather than assumed away, because "normally" is not a proof and because the driver has to report
which of the two sentences it is entitled to.

`holds_congr` is the coincidence lemma: satisfaction depends only on the free variables. The two
consequences are what the driver quotes. `check_complete_closed` upgrades a rejection from "not a
model under the checked assignment" to "not a model under ANY assignment".
`holds_everywhere_of_check` does the same for acceptance, which matters to nothing in the theorem
but makes the accepted verdict quotable without a footnote.

Every result here is `[propext, Quot.sound]`, the same as the rest of the layer and strictly
cleaner than the `[propext, Classical.choice, Quot.sound]` triple the older layers carry. That is a
measurement, not a preference: the binder cases discharge their side conditions with an explicit
`simp only [free, List.mem_filter, bne_iff_ne, ne_eq]` rather than a general `simpa`, and the
general one was what pulled choice in. Pinning the habitual triple here would be looser than the
truth and would stop catching anything.
-/
namespace Fol

theorem Term.eval_congr (M : Struc) (e e' : Env M) (t : Term)
    (h : ∀ k ∈ t.free, e k = e' k) : t.eval M e = t.eval M e' := by
  cases t with
  | var k => exact h k (by simp [Term.free])
  | const c => rfl

/-- **The coincidence lemma.** Two assignments agreeing on the free variables of `f` agree on
whether `f` holds. -/
theorem holds_congr (M : Struc) : ∀ (f : Form) (e e' : Env M),
    (∀ k ∈ free f, e k = e' k) → (Form.holds M e f ↔ Form.holds M e' f) := by
  intro f
  induction f with
  | app1 p t => intro e e' h; simp [Form.holds, Term.eval_congr M e e' t h]
  | app2 p t u =>
      intro e e' h
      simp only [Form.holds]
      rw [Term.eval_congr M e e' t (fun k hk => h k (by simp [free, hk])),
          Term.eval_congr M e e' u (fun k hk => h k (by simp [free, hk]))]
  | eq t u =>
      intro e e' h
      simp only [Form.holds]
      rw [Term.eval_congr M e e' t (fun k hk => h k (by simp [free, hk])),
          Term.eval_congr M e e' u (fun k hk => h k (by simp [free, hk]))]
  | tru => intro e e' h; rfl
  | fls => intro e e' h; rfl
  | neg f ih => intro e e' h; simp only [Form.holds]; rw [ih e e' h]
  | and f g ihf ihg =>
      intro e e' h
      simp only [Form.holds]
      rw [ihf e e' (fun k hk => h k (by simp [free, hk])),
          ihg e e' (fun k hk => h k (by simp [free, hk]))]
  | or f g ihf ihg =>
      intro e e' h
      simp only [Form.holds]
      rw [ihf e e' (fun k hk => h k (by simp [free, hk])),
          ihg e e' (fun k hk => h k (by simp [free, hk]))]
  | imp f g ihf ihg =>
      intro e e' h
      simp only [Form.holds]
      rw [ihf e e' (fun k hk => h k (by simp [free, hk])),
          ihg e e' (fun k hk => h k (by simp [free, hk]))]
  | all n f ih =>
      intro e e' h
      simp only [Form.holds]
      constructor
      · intro hA d
        refine (ih (update e n d) (update e' n d) ?_).1 (hA d)
        intro k hk
        by_cases hkn : k = n
        · subst hkn; simp [update]
        · simp only [update, if_neg hkn]
          refine h k ?_
          simp only [free, List.mem_filter, bne_iff_ne, ne_eq]
          exact ⟨hk, hkn⟩
      · intro hA d
        refine (ih (update e n d) (update e' n d) ?_).2 (hA d)
        intro k hk
        by_cases hkn : k = n
        · subst hkn; simp [update]
        · simp only [update, if_neg hkn]
          refine h k ?_
          simp only [free, List.mem_filter, bne_iff_ne, ne_eq]
          exact ⟨hk, hkn⟩
  | ex n f ih =>
      intro e e' h
      simp only [Form.holds]
      constructor
      · rintro ⟨d, hd⟩
        refine ⟨d, (ih (update e n d) (update e' n d) ?_).1 hd⟩
        intro k hk
        by_cases hkn : k = n
        · subst hkn; simp [update]
        · simp only [update, if_neg hkn]
          refine h k ?_
          simp only [free, List.mem_filter, bne_iff_ne, ne_eq]
          exact ⟨hk, hkn⟩
      · rintro ⟨d, hd⟩
        refine ⟨d, (ih (update e n d) (update e' n d) ?_).2 hd⟩
        intro k hk
        by_cases hkn : k = n
        · subst hkn; simp [update]
        · simp only [update, if_neg hkn]
          refine h k ?_
          simp only [free, List.mem_filter, bne_iff_ne, ne_eq]
          exact ⟨hk, hkn⟩

/-- A sentence's truth does not depend on the assignment at all. -/
theorem holds_closed (M : Struc) (f : Form) (hf : free f = []) (e e' : Env M) :
    Form.holds M e f ↔ Form.holds M e' f :=
  holds_congr M f e e' (fun k hk => absurd (hf ▸ hk) (by simp))

/-- **The rejection, strengthened.** For a problem of sentences, a rejected structure is not a
model under ANY assignment. This is the sentence the driver prints when it reports `closed: true`;
with a free variable anywhere in the problem it reports `closed: false` and the weaker
`check_complete` is what covers the verdict. -/
theorem check_complete_closed {n : Nat} {M : FinModel (n+1)} {Γ : List Form}
    (hc : ∀ g ∈ Γ, free g = []) (h : check M Γ = false) :
    ∀ e : Nat → Fin (n+1), ¬ (∀ g ∈ Γ, Form.holds M.toStruc e g) := by
  intro e hm
  refine check_complete h ?_
  intro g hg
  exact (holds_closed M.toStruc g (hc g hg) e (fun _ => 0)).1 (hm g hg)

/-- And the same upgrade for acceptance: a checked structure satisfies the sentences under EVERY
assignment, not only the one the checker used. -/
theorem holds_everywhere_of_check {n : Nat} {M : FinModel (n+1)} {Γ : List Form}
    (hc : ∀ g ∈ Γ, free g = []) (h : check M Γ = true) :
    ∀ (e : Nat → Fin (n+1)), ∀ g ∈ Γ, Form.holds M.toStruc e g := by
  intro e g hg
  exact (holds_closed M.toStruc g (hc g hg) (fun _ => 0) e).1 ((check_iff M Γ).1 h g hg)

/-! ## Axioms, pinned -/

/-- info: 'Fol.holds_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms holds_congr

/-- info: 'Fol.check_complete_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms check_complete_closed

/-- info: 'Fol.holds_everywhere_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms holds_everywhere_of_check

end Fol
