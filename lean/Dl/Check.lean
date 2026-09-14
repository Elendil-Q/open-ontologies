import Dl.Count

/-!
# The decision procedure, and the theorem about it

`checkModel I A` decides whether the finite interpretation `I` is a model of the axiom set
`A`. `Dl.satisfiable_of_checkModel` is the result the reasoner buys with it: an accepted
interpretation is an existence proof, so the axiom set really is satisfiable.

`Dl.checkModel_complete` is the other half and is what stops the layer being decoration. The
checker agrees with `Models` in both directions, so it rejects exactly the interpretations
that are not models. A checker that accepted everything would satisfy the soundness theorem
just as well; this one cannot.

Everything here is `Bool`-valued and runs. No `native_decide`, no `Classical` case split on
an undecidable proposition, no Mathlib.
-/
namespace Dl

/-- Does `x` satisfy `c`?

The two counting cases deduplicate the successors that satisfy the filler and compare the
length to the bound. `Dl.atLeast_iff` and `Dl.atMost_iff` are what make that the same
statement as `AtLeast` and `AtMost`; the deduplication is an implementation detail of this
function and appears nowhere in `Dl/Semantics.lean`. -/
def sat (I : Interp) : Concept → Name → Bool
  | .top, _ => true
  | .bot, _ => false
  | .atom a, x => (I.cext a).contains x
  | .neg c, x => !sat I c x
  | .and c d, x => sat I c x && sat I d x
  | .or c d, x => sat I c x || sat I d x
  | .ex r c, x => (I.rext r x).any (fun y => sat I c y)
  | .all r c, x => (I.rext r x).all (fun y => sat I c y)
  | .min n r c, x => n ≤ (nub ((I.rext r x).filter (fun y => sat I c y))).length
  | .max n r c, x => (nub ((I.rext r x).filter (fun y => sat I c y))).length ≤ n

theorem sat_iff (I : Interp) : ∀ (c : Concept) (x : Name), sat I c x = true ↔ Sat I c x
  | .top, x => by simp [sat, Sat]
  | .bot, x => by simp [sat, Sat]
  | .atom a, x => by simp [sat, Sat]
  | .neg c, x => by
    simp only [sat, Sat, Bool.not_eq_true']
    rw [Bool.eq_false_iff, ne_eq, sat_iff I c x]
  | .and c d, x => by
    simp only [sat, Sat, Bool.and_eq_true]
    rw [sat_iff I c x, sat_iff I d x]
  | .or c d, x => by
    simp only [sat, Sat, Bool.or_eq_true]
    rw [sat_iff I c x, sat_iff I d x]
  | .ex r c, x => by
    simp only [sat, Sat, List.any_eq_true]
    exact ⟨fun ⟨y, hy, hs⟩ => ⟨y, hy, (sat_iff I c y).1 hs⟩,
           fun ⟨y, hy, hs⟩ => ⟨y, hy, (sat_iff I c y).2 hs⟩⟩
  | .all r c, x => by
    simp only [sat, Sat, List.all_eq_true]
    exact ⟨fun h y hy => (sat_iff I c y).1 (h y hy),
           fun h y hy => (sat_iff I c y).2 (h y hy)⟩
  | .min n r c, x => by
    have h : ∀ y, (y ∈ I.rext r x ∧ Sat I c y) ↔
        y ∈ (I.rext r x).filter (fun y => sat I c y) := by
      intro y
      rw [List.mem_filter]
      exact and_congr_right (fun _ => (sat_iff I c y).symm)
    simp only [sat, Sat, decide_eq_true_eq]
    exact (atLeast_iff h).symm
  | .max n r c, x => by
    have h : ∀ y, (y ∈ I.rext r x ∧ Sat I c y) ↔
        y ∈ (I.rext r x).filter (fun y => sat I c y) := by
      intro y
      rw [List.mem_filter]
      exact and_congr_right (fun _ => (sat_iff I c y).symm)
    simp only [sat, Sat, decide_eq_true_eq]
    exact (atMost_iff h).symm

/-- Does `I` satisfy the axiom? -/
def holds (I : Interp) : Axiom → Bool
  | .sub c d => I.dom.all (fun x => !sat I c x || sat I d x)
  | .disjoint c d => I.dom.all (fun x => !(sat I c x && sat I d x))
  | .dom r c => I.dom.all (fun x => (I.rext r x).isEmpty || sat I c x)
  | .rng r c => I.dom.all (fun x => (I.rext r x).all (fun y => sat I c y))
  | .subrole r s => I.dom.all (fun x => (I.rext r x).all (fun y => (I.rext s x).contains y))
  | .trans r =>
      I.dom.all (fun x =>
        (I.rext r x).all (fun y => (I.rext r y).all (fun z => (I.rext r x).contains z)))
  | .sym r => I.dom.all (fun x => (I.rext r x).all (fun y => (I.rext r y).contains x))
  | .inv r s =>
      I.dom.all (fun x => (I.rext r x).all (fun y => (I.rext s y).contains x)) &&
      I.dom.all (fun x => (I.rext s x).all (fun y => (I.rext r y).contains x))
  | .invfunc r =>
      I.dom.all (fun y =>
        (nub (I.dom.filter (fun x => (I.rext r x).contains y))).length ≤ 1)
  | .inst a c => sat I c (I.ind a)
  | .rel a r b => (I.rext r (I.ind a)).contains (I.ind b)
  | .indiv a => I.dom.contains (I.ind a)
  | .nonempty c => I.dom.any (fun x => sat I c x)

theorem holds_iff (I : Interp) : ∀ a : Axiom, holds I a = true ↔ Holds I a
  | .sub c d => by
    simp only [holds, Holds, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    constructor
    · intro h x hx hc
      rcases h x hx with h | h
      · exact absurd ((sat_iff I c x).2 hc) (by simp [h])
      · exact (sat_iff I d x).1 h
    · intro h x hx
      by_cases hc : sat I c x = true
      · exact Or.inr ((sat_iff I d x).2 (h x hx ((sat_iff I c x).1 hc)))
      · exact Or.inl (by simpa using hc)
  | .disjoint c d => by
    simp only [holds, Holds, List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
    constructor
    · rintro h x hx ⟨hc, hd⟩
      rcases h x hx with h | h
      · exact absurd ((sat_iff I c x).2 hc) (by simp [h])
      · exact absurd ((sat_iff I d x).2 hd) (by simp [h])
    · intro h x hx
      by_cases hc : sat I c x = true
      · refine Or.inr ?_
        by_cases hd : sat I d x = true
        · exact absurd ⟨(sat_iff I c x).1 hc, (sat_iff I d x).1 hd⟩ (h x hx)
        · simpa using hd
      · exact Or.inl (by simpa using hc)
  | .dom r c => by
    simp only [holds, Holds, List.all_eq_true, Bool.or_eq_true]
    constructor
    · intro h x hx hne
      rcases h x hx with h | h
      · exact absurd (List.isEmpty_iff.1 h) hne
      · exact (sat_iff I c x).1 h
    · intro h x hx
      by_cases hne : I.rext r x = []
      · exact Or.inl (List.isEmpty_iff.2 hne)
      · exact Or.inr ((sat_iff I c x).2 (h x hx hne))
  | .rng r c => by
    simp only [holds, Holds, List.all_eq_true]
    exact ⟨fun h x hx y hy => (sat_iff I c y).1 (h x hx y hy),
           fun h x hx y hy => (sat_iff I c y).2 (h x hx y hy)⟩
  | .subrole r s => by simp [holds, Holds, List.all_eq_true]
  | .trans r => by simp [holds, Holds, List.all_eq_true]
  | .sym r => by simp [holds, Holds, List.all_eq_true]
  | .inv r s => by simp [holds, Holds, List.all_eq_true]
  | .invfunc r => by
    simp only [holds, Holds, List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro h y hy
      refine (atMost_iff (L := I.dom.filter (fun x => (I.rext r x).contains y)) ?_).2 (h y hy)
      intro x; rw [List.mem_filter]; simp
    · intro h y hy
      refine (atMost_iff (L := I.dom.filter (fun x => (I.rext r x).contains y)) ?_).1 (h y hy)
      intro x; rw [List.mem_filter]; simp
  | .inst a c => by simp only [holds, Holds]; exact sat_iff I c (I.ind a)
  | .rel a r b => by simp [holds, Holds]
  | .indiv a => by simp [holds, Holds]
  | .nonempty c => by
    simp only [holds, Holds, List.any_eq_true]
    exact ⟨fun ⟨x, hx, hs⟩ => ⟨x, hx, (sat_iff I c x).1 hs⟩,
           fun ⟨x, hx, hs⟩ => ⟨x, hx, (sat_iff I c x).2 hs⟩⟩

/-- Is `I` a finite interpretation of `A`'s vocabulary at all? -/
def checkWF (I : Interp) (A : List Axiom) : Bool :=
  !I.dom.isEmpty
  && (atomNames A).all (fun a => (I.cext a).all (fun x => I.dom.contains x))
  && (roleNames A).all (fun r =>
       I.dom.all (fun x => (I.rext r x).all (fun y => I.dom.contains y)))
  && (indNames A).all (fun a => I.dom.contains (I.ind a))

theorem checkWF_iff (I : Interp) (A : List Axiom) :
    checkWF I A = true ↔ WellFormed I A := by
  constructor
  · intro h
    simp only [checkWF, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hd; rw [hd] at h1; simp at h1
    · intro a ha x hx; simpa using h2 a ha x hx
    · intro r hr x hx y hy; simpa using h3 r hr x hx y hy
    · intro a ha; simpa using h4 a ha
  · intro hwf
    simp only [checkWF, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · match hd : I.dom with
      | [] => exact absurd hd hwf.nonempty
      | _ :: _ => simp
    · intro a ha x hx; simpa using hwf.cextInDom a ha x hx
    · intro r hr x hx y hy; simpa using hwf.rextInDom r hr x hx y hy
    · intro a ha; simpa using hwf.indInDom a ha

/-- The whole check: a finite interpretation of the vocabulary, satisfying every axiom. -/
def checkModel (I : Interp) (A : List Axiom) : Bool :=
  checkWF I A && A.all (fun a => holds I a)

theorem checkModel_iff (I : Interp) (A : List Axiom) :
    checkModel I A = true ↔ (I ⊨ A) := by
  simp only [checkModel, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨hwf, ha⟩
    exact ⟨(checkWF_iff I A).1 hwf, fun a h => (holds_iff I a).1 (ha a h)⟩
  · rintro ⟨hwf, ha⟩
    exact ⟨(checkWF_iff I A).2 hwf, fun a h => (holds_iff I a).2 (ha a h)⟩

/-- **What a model certificate buys.** An interpretation the checker accepts is a model, so
the axiom set has one, so it is satisfiable. This is the useful form: the conclusion no
longer mentions the interpretation the reasoner happened to build. -/
theorem satisfiable_of_checkModel {I : Interp} {A : List Axiom}
    (h : checkModel I A = true) : Satisfiable A :=
  ⟨I, (checkModel_iff I A).1 h⟩

/-- **The gate can fail.** The checker rejects nothing that is a model, so a rejection is a
statement about the interpretation, not about the checker's patience. -/
theorem checkModel_complete {I : Interp} {A : List Axiom}
    (h : checkModel I A = false) : ¬ (I ⊨ A) := by
  intro hm
  rw [(checkModel_iff I A).2 hm] at h
  exact Bool.noConfusion h

/-! ## Axioms, pinned

The footprint is the one the rest of this repository carries: propositional extensionality,
choice and quotient soundness, all three from the Lean core. A `sorry` or a `native_decide`
anywhere above changes one of these lines and the build fails. -/

/-- info: 'Dl.sat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sat_iff

/-- info: 'Dl.holds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms holds_iff

/-- info: 'Dl.checkWF_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkWF_iff

/-- info: 'Dl.checkModel_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkModel_iff

/-- info: 'Dl.satisfiable_of_checkModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms satisfiable_of_checkModel

/-- info: 'Dl.checkModel_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkModel_complete

end Dl
