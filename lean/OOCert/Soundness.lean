import OOCert.Rules

/-!
# Soundness

`certificate_sound`: if `checkCert G steps` returns `true`, then every
conclusion in `steps` is entailed by `G` under the semantics in
`Semantics.lean`. The proof is one lemma per rule, each a direct appeal to
the matching condition on the interpretation, plus an induction over the
certificate carrying the invariant "everything concluded so far is entailed".

What the theorem does not say, so that nobody reads more into it:

* Nothing about completeness. A certificate the checker rejects may still be
  a valid inference; the checker is a gate, not an oracle.
* Nothing about the parser (`Parse.lean`) or the file format. The theorem is
  about `checkCert` applied to lists of triples and steps. A parse error
  rejects; it cannot accept.
* Nothing about what the engine does with a rejected certificate. That is
  the caller's contract: the engine's run is trusted only when the checker
  says yes.

The `#guard_msgs` at the end pins the axioms the theorem depends on. If a
`sorry` ever enters this file, or a `native_decide`, the build fails there.
-/
namespace OOCert

section
variable {G : List Triple}

theorem allTyped_sound {x : Term} {k : Triple → Bool} :
    ∀ {ms : List Term} {ps : List Triple}, allTyped x k ms ps = true →
      ∀ m ∈ ms, k ⟨x, V.type, m⟩ = true := by
  intro ms
  induction ms with
  | nil =>
    intro ps _ m hm
    simp at hm
  | cons m ms ih =>
    intro ps h m' hm'
    rcases ps with _ | ⟨⟨x', t, m''⟩, ps⟩
    · simp [allTyped] at h
    · simp only [allTyped, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl, rfl, hk, hrest⟩ := h
      rcases List.mem_cons.mp hm' with rfl | hmem
      · exact hk
      · exact ih hrest m' hmem

theorem takeChain_sound {inG : Triple → Bool} (hG : ∀ t, inG t = true → t ∈ G) :
    ∀ (n : Nat) (ps : List Triple), ps.length ≤ n →
      ∀ (l : Term) (ms : List Term) (q : List Triple),
        takeChain inG l ps = some (ms, q) → Chain G l ms := by
  intro n
  induction n with
  | zero =>
    intro ps hlen l ms q h
    unfold takeChain at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rename_i hl
      subst hl
      exact Chain.nil
    · rcases ps with _ | ⟨_, _⟩
      · simp at h
      · simp at hlen
  | succ n ih =>
    intro ps hlen l ms q h
    unfold takeChain at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rename_i hl
      subst hl
      exact Chain.nil
    · rcases ps with _ | ⟨⟨l1, f, m⟩, _ | ⟨⟨l2, r, l'⟩, ps'⟩⟩
      · simp at h
      · simp at h
      · simp only at h
        split at h
        · rename_i hc
          obtain ⟨rfl, rfl, rfl, rfl, h1, h2⟩ := hc
          revert h
          cases hrec : takeChain inG l' ps' with
          | none =>
            intro h
            simp at h
          | some pr =>
            intro h
            obtain ⟨ms', q'⟩ := pr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hlen' : ps'.length ≤ n := by
              simp at hlen
              omega
            exact Chain.cons (hG _ h1) (hG _ h2) (ih ps' hlen' l' ms' q' hrec)
        · simp at h

theorem checkStep_sound {inG derived : Triple → Bool} {st : Step}
    (hG : ∀ t, inG t = true → t ∈ G)
    (hD : ∀ t, derived t = true → Entails G t)
    (h : checkStep inG derived st = true) : Entails G st.conclusion := by
  have hk : ∀ t, (inG t || derived t) = true → Entails G t := by
    intro t ht
    simp only [Bool.or_eq_true] at ht
    rcases ht with h1 | h1
    · exact Entails.of_mem (hG t h1)
    · exact hD t h1
  obtain ⟨rule, premises, conclusion⟩ := st
  unfold checkStep at h
  dsimp only at h
  cases rule
  case rdfs2 =>
    rcases premises with _ | ⟨⟨s, p, o⟩, _ | ⟨⟨p', d, c⟩, _ | _⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, h1, h2, rfl⟩ := h
    intro I M
    exact M.conds.dom _ _ (hk _ h2 I M) _ _ (hk _ h1 I M)
  case rdfs3 =>
    rcases premises with _ | ⟨⟨s, p, o⟩, _ | ⟨⟨p', r, c⟩, _ | _⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, h1, h2, rfl⟩ := h
    intro I M
    exact M.conds.rng _ _ (hk _ h2 I M) _ _ (hk _ h1 I M)
  case rdfs5 =>
    rcases premises with _ | ⟨⟨a, sp1, b⟩, _ | ⟨⟨b', sp2, c⟩, _ | _⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, rfl, h1, h2, rfl⟩ := h
    intro I M
    exact M.conds.sp_trans _ _ _ (hk _ h1 I M) (hk _ h2 I M)
  case rdfs7 =>
    rcases premises with _ | ⟨⟨s, p, o⟩, _ | ⟨⟨p', sp, q⟩, _ | _⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, h1, h2, rfl⟩ := h
    intro I M
    exact M.conds.sp_sub _ _ (hk _ h2 I M) _ _ (hk _ h1 I M)
  case rdfs9 =>
    rcases premises with _ | ⟨⟨x, t, a⟩, _ | ⟨⟨a', sc, b⟩, _ | _⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, rfl, h1, h2, rfl⟩ := h
    intro I M
    exact M.conds.sc_sub _ _ (hk _ h2 I M) _ (hk _ h1 I M)
  case rdfs11 =>
    rcases premises with _ | ⟨⟨a, sc1, b⟩, _ | ⟨⟨b', sc2, c⟩, _ | _⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, rfl, h1, h2, rfl⟩ := h
    intro I M
    exact M.conds.sc_trans _ _ _ (hk _ h1 I M) (hk _ h2 I M)
  case prpTrp =>
    rcases premises with _ | ⟨⟨p, t, tp⟩, _ | ⟨⟨x, p1, y⟩, _ | ⟨⟨y', p2, z⟩, _ | _⟩⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, h1, h2, h3, rfl⟩ := h
    intro I M
    exact M.conds.trp _ (hk _ h1 I M) _ _ _ (hk _ h2 I M) (hk _ h3 I M)
  case prpSymp =>
    rcases premises with _ | ⟨⟨p, t, sy⟩, _ | ⟨⟨x, p1, y⟩, _ | _⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, rfl, h1, h2, rfl⟩ := h
    intro I M
    exact M.conds.symp _ (hk _ h1 I M) _ _ (hk _ h2 I M)
  case prpInv1 =>
    rcases premises with _ | ⟨⟨p, io, q⟩, _ | ⟨⟨x, p1, y⟩, _ | _⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, h1, h2, rfl⟩ := h
    intro I M
    exact (M.conds.inv _ _ (hk _ h1 I M) _ _).mp (hk _ h2 I M)
  case prpInv2 =>
    rcases premises with _ | ⟨⟨p, io, q⟩, _ | ⟨⟨x, q1, y⟩, _ | _⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, h1, h2, rfl⟩ := h
    intro I M
    exact (M.conds.inv _ _ (hk _ h1 I M) _ _).mpr (hk _ h2 I M)
  case eqSym =>
    rcases premises with _ | ⟨⟨a, sa, b⟩, _ | _⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, h1, rfl⟩ := h
    intro I M
    have s : I.iext (I.ι V.sameAs) (I.ι a) (I.ι b) := hk _ h1 I M
    have e := M.conds.same _ _ s
    show I.iext (I.ι V.sameAs) (I.ι b) (I.ι a)
    rw [← e]
    rw [← e] at s
    exact s
  case scmEqc1 =>
    rcases premises with _ | ⟨⟨a, e, b⟩, _ | _⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, h1, hc⟩ := h
    intro I M
    rcases hc with rfl | rfl
    · exact (M.conds.eqc _ _ (hk _ h1 I M)).1
    · exact (M.conds.eqc _ _ (hk _ h1 I M)).2
  case scmEqp1 =>
    rcases premises with _ | ⟨⟨a, e, b⟩, _ | _⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, h1, hc⟩ := h
    intro I M
    rcases hc with rfl | rfl
    · exact (M.conds.eqp _ _ (hk _ h1 I M)).1
    · exact (M.conds.eqp _ _ (hk _ h1 I M)).2
  case clsSvf1 =>
    rcases premises with
      _ | ⟨⟨r, op, p⟩, _ | ⟨⟨r', sv, c⟩, _ | ⟨⟨x, p1, y⟩, _ | ⟨⟨y', t, c'⟩, _ | _⟩⟩⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h1, h2, h3, h4, rfl⟩ := h
    intro I M
    exact M.conds.svf _ _ _ (hk _ h1 I M) (hk _ h2 I M) _ _ (hk _ h3 I M) (hk _ h4 I M)
  case clsAvf =>
    rcases premises with
      _ | ⟨⟨r, op, p⟩, _ | ⟨⟨r', av, c⟩, _ | ⟨⟨x, t, r''⟩, _ | ⟨⟨x', p1, y⟩, _ | _⟩⟩⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h1, h2, h3, h4, rfl⟩ := h
    intro I M
    exact M.conds.avf _ _ _ (hk _ h1 I M) (hk _ h2 I M) _ _ (hk _ h3 I M) (hk _ h4 I M)
  case clsHv1 =>
    rcases premises with
      _ | ⟨⟨r, op, p⟩, _ | ⟨⟨r', hv, v⟩, _ | ⟨⟨x, t, r''⟩, _ | _⟩⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, h1, h2, h3, rfl⟩ := h
    intro I M
    exact (M.conds.hv _ _ _ (hk _ h1 I M) (hk _ h2 I M) _).mp (hk _ h3 I M)
  case clsHv2 =>
    rcases premises with
      _ | ⟨⟨r, op, p⟩, _ | ⟨⟨r', hv, v⟩, _ | ⟨⟨x, p1, v'⟩, _ | _⟩⟩⟩ <;>
      simp only [decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, h1, h2, h3, rfl⟩ := h
    intro I M
    exact (M.conds.hv _ _ _ (hk _ h1 I M) (hk _ h2 I M) _).mpr (hk _ h3 I M)
  case clsInt1 =>
    rcases premises with _ | ⟨⟨c, io, l⟩, ps⟩
    · simp at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hin⟩, hm⟩ := h
      revert hm
      cases hchain : takeChain inG l ps with
      | none =>
        intro hm
        simp at hm
      | some pr =>
        intro hm
        obtain ⟨ms, q⟩ := pr
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
        obtain ⟨hall, hp, ho⟩ := hm
        have hC : Chain G l ms :=
          takeChain_sound hG ps.length ps (Nat.le_refl _) l ms q hchain
        intro I M
        have hx : ∀ m ∈ ms, I.cext (I.ι m) (I.ι conclusion.s) :=
          fun m hm => hk _ (allTyped_sound hall m hm) I M
        have hc := M.int c l ms (hG _ hin) hC (I.ι conclusion.s) hx
        show I.iext (I.ι conclusion.p) (I.ι conclusion.s) (I.ι conclusion.o)
        rw [hp, ho]
        exact hc
  case clsUni =>
    rcases premises with _ | ⟨⟨c, uo, l⟩, ps⟩
    · simp at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hin⟩, hm⟩ := h
      revert hm
      cases hchain : takeChain inG l ps with
      | none =>
        intro hm
        simp at hm
      | some pr =>
        intro hm
        obtain ⟨ms, q⟩ := pr
        rcases q with _ | ⟨⟨x, t, m⟩, _ | _⟩ <;>
          simp only [decide_eq_true_eq, Bool.false_eq_true] at hm
        obtain ⟨rfl, hmem, hkx, rfl⟩ := hm
        have hC : Chain G l ms :=
          takeChain_sound hG ps.length ps (Nat.le_refl _) l ms _ hchain
        intro I M
        exact M.uni c l ms (hG _ hin) hC (I.ι x) m hmem (hk _ hkx I M)

theorem checkAll_sound {inG : Triple → Bool} (hG : ∀ t, inG t = true → t ∈ G) :
    ∀ (steps : List Step) (derived : Std.HashSet Triple),
      (∀ t, derived.contains t = true → Entails G t) →
      checkAll inG steps derived = true →
      ∀ st ∈ steps, Entails G st.conclusion := by
  intro steps
  induction steps with
  | nil =>
    intro _ _ _ st hst
    simp at hst
  | cons st rest ih =>
    intro derived hD h st' hst'
    simp only [checkAll, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hst : Entails G st.conclusion := checkStep_sound hG hD h1
    have hD' : ∀ t, (derived.insert st.conclusion).contains t = true → Entails G t := by
      intro t ht
      rw [Std.HashSet.contains_insert] at ht
      simp only [Bool.or_eq_true, beq_iff_eq] at ht
      rcases ht with rfl | ht
      · exact hst
      · exact hD t ht
    rcases List.mem_cons.mp hst' with rfl | hmem
    · exact hst
    · exact ih _ hD' h2 st' hmem

end

/-- The theorem the checker is trusted for. -/
theorem certificate_sound (G : List Triple) (steps : List Step)
    (h : checkCert G steps = true) : ∀ st ∈ steps, Entails G st.conclusion := by
  unfold checkCert at h
  refine checkAll_sound (G := G) (inG := fun t => (Std.HashSet.ofList G).contains t)
    ?_ steps ∅ ?_ h
  · intro t ht
    rw [Std.HashSet.contains_ofList] at ht
    simpa using ht
  · intro t ht
    simp at ht

/-! The axiom tripwire. `sorryAx`, `native_decide`'s `Lean.ofReduceBool` or any
other addition to this list fails the build. -/
/-- info: 'OOCert.certificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificate_sound

end OOCert
