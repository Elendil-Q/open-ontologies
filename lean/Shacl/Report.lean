import Shacl.Agreement

/-!
# The whole report

`eval_conforms_iff` is about one focus node and one shape. A validator answers a
different question: given a data graph and a set of shape declarations with their
targets, does anything violate anything. That is what `validate` computes and what
`validate_spec` is about.

The target computation is inside the theorem deliberately. A validator that
evaluates the right shape at the wrong nodes is wrong in a way no amount of
correctness about `Conf` would catch, and `sh:targetClass` in particular reuses the
subclass closure, so it inherits the same refusal.
-/
namespace Shacl

theorem mem_focusNodes {G : Graph} {t : Target} {l : List Term} (h : focusNodes G t = .ok l)
    {x : Term} : x ∈ l ↔ IsFocus G t x := by
  cases t with
  | node n =>
      rw [focusNodes] at h
      injection h with h
      subst h
      exact Iff.trans List.mem_singleton (Iff.rfl : x = n ↔ IsFocus G (.node n) x)
  | klass c =>
      rw [focusNodes] at h
      cases hcl : subClosure G c with
      | none => simp only [hcl] at h; exact absurd h (by simp)
      | some S =>
          simp only [hcl] at h
          injection h with h
          subst h
          rw [mem_dedup, List.mem_map]
          constructor
          · rintro ⟨tr, htr, hs⟩
            rw [List.mem_filter] at htr
            obtain ⟨hG, hsel⟩ := htr
            simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hsel
            obtain ⟨hp, ho⟩ := hsel
            cases tr with
            | mk a b cc =>
                simp only at hp ho hs
                subst hp
                subst hs
                exact ⟨cc, hG, subClosure_sound hcl cc ho⟩
          · rintro ⟨ty, hG, hsc⟩
            refine ⟨⟨x, V.type, ty⟩, ?_, rfl⟩
            rw [List.mem_filter]
            refine ⟨hG, ?_⟩
            show ((V.type == V.type) && S.contains ty) = true
            rw [beq_self_eq_true, Bool.true_and]
            exact List.contains_iff_mem.mpr (subClosure_complete hcl hsc)
  | subjectsOf p =>
      rw [focusNodes] at h
      injection h with h
      subst h
      rw [mem_dedup, List.mem_map]
      constructor
      · rintro ⟨tr, htr, hs⟩
        rw [List.mem_filter] at htr
        obtain ⟨hG, hsel⟩ := htr
        simp only [beq_iff_eq] at hsel
        cases tr with
        | mk a b cc =>
            simp only at hsel hs
            subst hsel
            subst hs
            exact ⟨cc, hG⟩
      · rintro ⟨o, hG⟩
        exact ⟨⟨x, p, o⟩, by rw [List.mem_filter]; exact ⟨hG, by simp⟩, rfl⟩
  | objectsOf p =>
      rw [focusNodes] at h
      injection h with h
      subst h
      rw [mem_dedup, List.mem_map]
      constructor
      · rintro ⟨tr, htr, hs⟩
        rw [List.mem_filter] at htr
        obtain ⟨hG, hsel⟩ := htr
        simp only [beq_iff_eq] at hsel
        cases tr with
        | mk a b cc =>
            simp only at hsel hs
            subst hsel
            subst hs
            exact ⟨a, hG⟩
      · rintro ⟨s, hG⟩
        exact ⟨⟨s, p, x⟩, by rw [List.mem_filter]; exact ⟨hG, by simp⟩, rfl⟩

theorem mem_focusList {G : Graph} {x : Term} :
    ∀ {ts : List Target} {l : List Term}, focusList G ts = .ok l →
      (x ∈ l ↔ ∃ t ∈ ts, IsFocus G t x)
  | [], l, h => by
      rw [focusList] at h; injection h with h; subst h; simp
  | t :: ts, l, h => by
      rw [focusList] at h
      cases ha : focusNodes G t with
      | error e => rw [bind_error_eq ha] at h; exact absurd h (by simp)
      | ok a =>
          rw [bind_ok_eq ha] at h
          cases hb : focusList G ts with
          | error e => rw [bind_error_eq hb] at h; exact absurd h (by simp)
          | ok b =>
              rw [bind_ok_eq hb] at h
              injection h with h
              subst h
              rw [mem_dedup, List.mem_append, mem_focusNodes ha, mem_focusList hb]
              constructor
              · rintro (hx | ⟨u, hu, hx⟩)
                · exact ⟨t, List.mem_cons_self .., hx⟩
                · exact ⟨u, List.mem_cons_of_mem _ hu, hx⟩
              · rintro ⟨u, hu, hx⟩
                rcases List.mem_cons.mp hu with rfl | hu
                · exact Or.inl hx
                · exact Or.inr ⟨u, hu, hx⟩

theorem evalDecl_spec {G : Graph} {d : ShapeDecl} {rs : List Result}
    (h : evalDecl G d = .ok rs) :
    (rs = [] ↔ ∀ f, Targeted G d f → Conf G d.shape f) ∧
      (∀ r ∈ rs, ¬ Conf G r.blamed r.blamedNode) := by
  rw [evalDecl] at h
  cases hf : focusList G d.targets with
  | error e => rw [bind_error_eq hf] at h; exact absurd h (by simp)
  | ok fs =>
      rw [bind_ok_eq hf] at h
      cases hc : collect (fun f => eval G d.shape d.id f) fs with
      | error e => rw [bind_error_eq hc] at h; exact absurd h (by simp)
      | ok out =>
          rw [bind_ok_eq hc] at h
          injection h with h
          subst h
          obtain ⟨hmap, hall⟩ := collect_ok hc
          refine ⟨?_, ?_⟩
          · rw [List.flatMap_eq_nil_iff]
            constructor
            · intro hnil f hft
              have hfs : f ∈ fs := (mem_focusList hf).mpr hft
              rw [← hmap] at hfs
              obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hfs
              rw [← hq1]
              exact (eval_conforms_iff (hall q hq)).mp (hnil q hq)
            · intro hconf q hq
              refine (eval_conforms_iff (hall q hq)).mpr (hconf q.1 ?_)
              refine (mem_focusList hf).mp ?_
              rw [← hmap]
              exact List.mem_map.mpr ⟨q, hq, rfl⟩
          · intro r hr
            obtain ⟨q, hq, hrq⟩ := List.mem_flatMap.mp hr
            exact eval_results_licensed (hall q hq) r hrq

/-- **The report is sound and complete.** `validate` returns an empty report exactly
when every node targeted by every declaration conforms to that declaration's shape,
and every result it does return blames a node that really fails the constraint it is
blamed for.

The hypothesis matters: this says nothing about a run that refused. A refusal is
reported as a refusal by `ShaclMain.lean`, never as `conforms`. -/
theorem validate_spec {G : Graph} :
    ∀ {ds : List ShapeDecl} {rs : List Result}, validate G ds = .ok rs →
      (rs = [] ↔ ∀ d ∈ ds, ∀ f, Targeted G d f → Conf G d.shape f) ∧
        (∀ r ∈ rs, ¬ Conf G r.blamed r.blamedNode)
  | [], rs, h => by
      rw [validate] at h
      injection h with h
      subst h
      exact ⟨Iff.intro (fun _ d hd => absurd hd (by simp)) (fun _ => rfl), by simp⟩
  | d :: ds, rs, h => by
      rw [validate] at h
      cases ha : evalDecl G d with
      | error e => rw [bind_error_eq ha] at h; exact absurd h (by simp)
      | ok a =>
          rw [bind_ok_eq ha] at h
          cases hb : validate G ds with
          | error e => rw [bind_error_eq hb] at h; exact absurd h (by simp)
          | ok b =>
              rw [bind_ok_eq hb] at h
              injection h with h
              subst h
              obtain ⟨ha1, ha2⟩ := evalDecl_spec ha
              obtain ⟨hb1, hb2⟩ := validate_spec hb
              refine ⟨?_, ?_⟩
              · rw [List.append_eq_nil_iff]
                constructor
                · rintro ⟨hna, hnb⟩ e he
                  rcases List.mem_cons.mp he with rfl | he
                  · exact ha1.mp hna
                  · exact hb1.mp hnb e he
                · intro hall
                  exact ⟨ha1.mpr (hall d (List.mem_cons_self ..)),
                    hb1.mpr (fun e he => hall e (List.mem_cons_of_mem _ he))⟩
              · intro r hr
                rcases List.mem_append.mp hr with hr | hr
                · exact ha2 r hr
                · exact hb2 r hr

/-! ## Axioms, pinned

The same three the derivation checker in `lean/OOCert/` depends on, except where a
theorem genuinely needs fewer, in which case the pin says so. A `sorry` or a
`native_decide` anywhere under these theorems changes the list and fails the
build. -/

/-- info: 'Shacl.eval_conforms_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_conforms_iff

/-- info: 'Shacl.eval_results_licensed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_results_licensed

/-- info: 'Shacl.validate_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validate_spec

/-- info: 'Shacl.mem_focusNodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_focusNodes

-- The path semantics: the enumeration and the specification are the same set.
-- `sh:minCount` and everything else that counts value nodes rests on this one.
/-- info: 'Shacl.mem_valueNodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_valueNodes

-- The pattern matcher decides the pattern relation. A strict SUBSET of the
-- footprint above, pinned at what it actually is: the matcher and its proof never
-- reach `Classical.choice`.
/-- info: 'Shacl.regexMatchB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms regexMatchB_iff

/-- info: 'Shacl.mem_qualifyingNodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_qualifyingNodes

end Shacl
