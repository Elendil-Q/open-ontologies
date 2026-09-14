import Dl.Semantics

/-!
# Counting distinct witnesses

`≥n R.C`, `≤n R.C` and inverse functionality all say something about how many DISTINCT
elements satisfy a condition. `Dl/Semantics.lean` states that with `AtLeast` and `AtMost`,
which quantify over duplicate-free lists and mention no computation at all. A checker has
to turn those into a number, and this file is the bridge.

The whole bridge rests on one lemma, `nodup_length_le`: a duplicate-free list whose members
all come from `l` is no longer than `l`. That is pigeonhole, and it is proved here by
induction with `List.erase` rather than assumed, because the entire soundness of the `≤`
direction is that one inequality.

`nub` keeps the last occurrence of each element. Which occurrence survives does not matter;
what matters is `mem_nub` and `nub_nodup`, and both are proved.
-/
namespace Dl

/-- Remove duplicates, keeping the last occurrence. -/
def nub : List Name → List Name
  | [] => []
  | a :: l => if l.contains a then nub l else a :: nub l

theorem mem_nub : ∀ {l : List Name} {x : Name}, x ∈ nub l ↔ x ∈ l
  | [], x => by simp [nub]
  | a :: l, x => by
    by_cases h : l.contains a
    · rw [nub, if_pos h]
      constructor
      · intro hx; exact List.mem_cons_of_mem _ (mem_nub.1 hx)
      · intro hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact mem_nub.2 (List.elem_iff.1 h)
        · exact mem_nub.2 hx
    · rw [nub, if_neg h]
      constructor
      · intro hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mem_nub.1 hx)
      · intro hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mem_nub.2 hx)

theorem nub_nodup : ∀ l : List Name, (nub l).Nodup
  | [] => by simp [nub]
  | a :: l => by
    by_cases h : l.contains a
    · rw [nub, if_pos h]; exact nub_nodup l
    · rw [nub, if_neg h]
      refine List.nodup_cons.2 ⟨?_, nub_nodup l⟩
      intro hm
      exact h (List.elem_iff.2 (mem_nub.1 hm))

/-- Pigeonhole. A duplicate-free list drawn from `l` is no longer than `l`.

Proved by induction on the duplicate-free list: its head is in `l`, its tail avoids that
head and so is drawn from `l` with one occurrence of the head erased, and erasing an
element that is present shortens the list by exactly one. -/
theorem nodup_length_le :
    ∀ {ys l : List Name}, ys.Nodup → (∀ y ∈ ys, y ∈ l) → ys.length ≤ l.length
  | [], _, _, _ => Nat.zero_le _
  | a :: ys, l, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha : a ∈ l := hsub a (List.mem_cons_self ..)
    have hsub' : ∀ y ∈ ys, y ∈ l.erase a := by
      intro y hy
      have hne : y ≠ a := fun h => hnd.1 (h ▸ hy)
      exact (List.mem_erase_of_ne hne).2 (hsub y (List.mem_cons_of_mem _ hy))
    have ih := nodup_length_le hnd.2 hsub'
    rw [List.length_erase_of_mem ha] at ih
    have hpos : 0 < l.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- `AtLeast n P` is exactly "the deduplicated list of `P`'s members is at least `n` long",
for any list `L` that enumerates `P`. -/
theorem atLeast_iff {n : Nat} {P : Name → Prop} {L : List Name} (h : ∀ y, P y ↔ y ∈ L) :
    AtLeast n P ↔ n ≤ (nub L).length := by
  constructor
  · rintro ⟨ys, hnd, hlen, hmem⟩
    have : ∀ y ∈ ys, y ∈ nub L := fun y hy => mem_nub.2 ((h y).1 (hmem y hy))
    have := nodup_length_le hnd this
    omega
  · intro hle
    refine ⟨(nub L).take n, ?_, ?_, ?_⟩
    · exact List.Nodup.sublist (List.take_sublist n _) (nub_nodup L)
    · rw [List.length_take]; omega
    · intro y hy
      exact (h y).2 (mem_nub.1 ((List.take_sublist n _).mem hy))

/-- `AtMost n P` is exactly "the deduplicated list of `P`'s members is at most `n` long". -/
theorem atMost_iff {n : Nat} {P : Name → Prop} {L : List Name} (h : ∀ y, P y ↔ y ∈ L) :
    AtMost n P ↔ (nub L).length ≤ n := by
  constructor
  · intro hA
    exact hA (nub L) (nub_nodup L) (fun y hy => (h y).2 (mem_nub.1 hy))
  · intro hle ys hnd hmem
    have : ∀ y ∈ ys, y ∈ nub L := fun y hy => mem_nub.2 ((h y).1 (hmem y hy))
    exact Nat.le_trans (nodup_length_le hnd this) hle

/-! ## Axioms, pinned -/

/-- info: 'Dl.nodup_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nodup_length_le

/-- info: 'Dl.atLeast_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms atLeast_iff

/-- info: 'Dl.atMost_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms atMost_iff

end Dl
