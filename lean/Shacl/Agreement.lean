import Shacl.Eval

/-!
# The evaluator agrees with the specification

Two theorems, both from one induction over the shape.

`eval_conforms_iff`  the evaluator reports no results exactly when the focus node
                     conforms. Soundness AND completeness of the verdict, for every
                     component covered.

`eval_results_licensed`  every result the evaluator reports names a constraint and
                     a node, and that node really does fail that constraint
                     according to the specification. Soundness of the report and not
                     only of the boolean.

Both are conditional on `eval` having returned `.ok`. When it refuses there is
nothing to be sound about, and the refusal is reported rather than rounded into a
verdict.

## This has been seen to fail

Replacing the refusal in `evalCompare` with `.ok []`, so that a comparison the term
model cannot make is reported as CONFORMING rather than declined, does not compile:

```text
error: Shacl/Agreement.lean:319:49: unsolved goals
  hc : cmpTerms c f = none
  h : Except.ok [] = Except.ok rs
  ⊢ ¬rs = []
```

That is the whole point of the exercise. `Conf` says a node whose comparison is
unknown does not conform, so an evaluator that answers `conforms` there cannot be
proved to agree with it, and the build stops. An evaluator that refuses can.

## What is NOT claimed

* Nothing here says the specification in `Spec.lean` IS the W3C Recommendation.
  That is a reading of prose and no proof can establish it. The measurement in
  `tests/shacl_core_verified_test.rs` is what tests that reading: it runs this
  specification against the Working Group's own suite and counts the
  disagreements.
* Nothing here says the compiler from RDF to `Shape` is correct. It is outside the
  theorem on purpose, it fails closed, and its refusals show up as undetermined.
* `sh:resultPath`, `sh:value` and `sh:resultSeverity` on a result are not covered by
  the licensing theorem. It pins `blamed` and `blamedNode`, which are what make a
  result true or false; the other fields are presentation.
* **Completeness is claimed for the VERDICT, not for the result list.** `sh:and`,
  `sh:or`, `sh:not`, `sh:node` and `sh:xone` each report ONE result for a whole
  failing subtree, which is what the Recommendation asks for, so "one result per
  failing atomic constraint" is neither claimed nor true. What is claimed is that the
  report is empty exactly when the node conforms, which is the property a consumer of
  `sh:conforms` relies on.
* **The property-pair constraints report one result per focus node, where the
  Recommendation asks for one per offending value.** `sh:equals`, `sh:disjoint`,
  `sh:lessThan` and `sh:lessThanOrEquals` are the four; see `violationPair` in
  `Shacl/Eval.lean`. The verdict is unaffected and every result produced is licensed,
  but a consumer counting results will count fewer than a fully conforming validator
  would. `sh:closed` does report one per offending triple.
-/
namespace Shacl

/-! ## Plumbing -/

theorem bind_ok_eq {α β} {x : Except Refusal α} {a : α} (h : x = .ok a)
    (g : α → Except Refusal β) : (x >>= g) = g a := by rw [h]; rfl

theorem bind_error_eq {α β} {x : Except Refusal α} {e : Refusal} (h : x = .error e)
    (g : α → Except Refusal β) : (x >>= g) = .error e := by rw [h]; rfl

/-- Everything `check` decides, in one place: the result list is empty exactly when
the decision was `true`, and when it is not empty it holds exactly the one result it
was given. -/
theorem check_spec {b : Bool} {r : Result} {rs : List Result} (h : check b r = .ok rs) :
    (rs = [] ↔ b = true) ∧ (∀ x ∈ rs, x = r) := by
  cases b with
  | true =>
      rw [check, if_pos rfl] at h
      injection h with h
      subst h
      exact ⟨Iff.intro (fun _ => rfl) (fun _ => rfl), by simp⟩
  | false =>
      rw [check] at h
      simp only [Bool.false_eq_true, if_false] at h
      injection h with h
      subst h
      refine ⟨Iff.intro (fun hn => absurd hn (by simp)) (fun hn => absurd hn (by simp)), ?_⟩
      intro x hx
      simpa using hx

/-- The shape every leaf constraint takes: a decision whose truth is exactly the
specification's condition, and, when it is false, one result blaming that very
constraint at that very node. Stating it once keeps most cases of the induction
below to three lines each, and keeps the licensing argument from being retyped once
per constraint with a chance to drift. -/
theorem leafCase {G : Graph} {b : Bool} {r : Result} {rs : List Result} {s : Shape} {f : Term}
    (h : check b r = .ok rs) (hb : b = true ↔ Conf G s f)
    (hbl : r.blamed = s) (hbn : r.blamedNode = f) :
    (rs = [] ↔ Conf G s f) ∧ (∀ x ∈ rs, ¬ Conf G x.blamed x.blamedNode) := by
  obtain ⟨h1, h2⟩ := check_spec h
  have hiff : rs = [] ↔ Conf G s f := Iff.trans h1 hb
  refine ⟨hiff, ?_⟩
  intro x hx
  rw [h2 x hx, hbl, hbn]
  intro hc
  have hnil : rs = [] := hiff.mpr hc
  subst hnil
  exact absurd hx (by simp)

/-- `leafCase` for a constraint that can produce MORE than one result, where every
result blames the same node for the same constraint. `sh:closed` is the only one:
the Recommendation asks for a result per offending triple. -/
theorem leafCaseMany {G : Graph} {rs : List Result} {s : Shape} {f : Term}
    (hiff : rs = [] ↔ Conf G s f) (hall : ∀ x ∈ rs, x.blamed = s ∧ x.blamedNode = f) :
    (rs = [] ↔ Conf G s f) ∧ (∀ x ∈ rs, ¬ Conf G x.blamed x.blamedNode) := by
  refine ⟨hiff, ?_⟩
  intro x hx
  obtain ⟨h1, h2⟩ := hall x hx
  rw [h1, h2]
  intro hc
  have hnil : rs = [] := hiff.mpr hc
  subst hnil
  exact absurd hx (by simp)

theorem contains_eq_false_iff_not_mem {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    l.contains a = false ↔ a ∉ l := by
  constructor
  · intro h hm
    rw [List.contains_iff_mem.mpr hm] at h
    exact absurd h (by simp)
  · intro h
    by_cases hc : l.contains a = true
    · exact absurd (List.contains_iff_mem.mp hc) h
    · simpa using hc

theorem mem_closedOffenders {G : Graph} {allowed : List Term} {f : Term} {t : Triple} :
    t ∈ closedOffenders G allowed f ↔ (t ∈ G ∧ t.s = f ∧ t.p ∉ allowed) := by
  rw [closedOffenders, List.mem_filter]
  constructor
  · rintro ⟨hG, hb⟩
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
      contains_eq_false_iff_not_mem] at hb
    exact ⟨hG, hb.1, hb.2⟩
  · rintro ⟨hG, hs, hp⟩
    refine ⟨hG, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', contains_eq_false_iff_not_mem]
    exact ⟨hs, hp⟩

theorem closedResults_nil_iff {G : Graph} {allowed : List Term} {src : Term} {s : Shape}
    {f : Term} :
    closedResults G allowed src s f = [] ↔ ∀ p o, (⟨f, p, o⟩ : Triple) ∈ G → p ∈ allowed := by
  rw [closedResults, List.map_eq_nil_iff, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h p o hG
    by_cases hp : p ∈ allowed
    · exact hp
    · exact absurd (mem_closedOffenders.mpr ⟨hG, rfl, hp⟩) (h ⟨f, p, o⟩)
  · intro h t ht
    obtain ⟨hG, hs, hp⟩ := mem_closedOffenders.mp ht
    refine hp (h t.p t.o ?_)
    have ht' : (⟨f, t.p, t.o⟩ : Triple) = t := by rw [← hs]
    rw [ht']
    exact hG

theorem liftValue_blamed (f : Term) (pa : Path) (v : Term) (r : Result) :
    (liftValue f pa v r).blamed = r.blamed := by
  rw [liftValue]; split <;> rfl

theorem liftValue_blamedNode (f : Term) (pa : Path) (v : Term) (r : Result) :
    (liftValue f pa v r).blamedNode = r.blamedNode := by
  rw [liftValue]; split <;> rfl

/-- `collect` returns one entry per input node, in order, each holding exactly what
the evaluator returned at that node. -/
theorem collect_ok {k : Term → Except Refusal (List Result)} :
    ∀ {l : List Term} {out : List (Term × List Result)}, collect k l = .ok out →
      out.map Prod.fst = l ∧ ∀ q ∈ out, k q.1 = .ok q.2
  | [], out, h => by
      rw [collect] at h; injection h with h; subst h; exact ⟨rfl, by simp⟩
  | v :: vs, out, h => by
      rw [collect] at h
      cases hk : k v with
      | error e => rw [bind_error_eq hk] at h; exact absurd h (by simp)
      | ok r =>
          rw [bind_ok_eq hk] at h
          cases hc : collect k vs with
          | error e => rw [bind_error_eq hc] at h; exact absurd h (by simp)
          | ok rest =>
              rw [bind_ok_eq hc] at h
              injection h with h
              subst h
              obtain ⟨h1, h2⟩ := collect_ok hc
              refine ⟨by simpa using h1, ?_⟩
              intro q hq
              rcases List.mem_cons.mp hq with rfl | hq
              · exact hk
              · exact h2 q hq

/-! ## The decision procedures, each matched to the proposition it decides -/

/-- Counting a duplicate-free enumeration of the nodes with some property decides
"there are at least `n` such nodes". The backward direction is the pigeonhole: any
duplicate-free list of such nodes is a subset of the enumeration, so it cannot be
longer. Stated for an arbitrary property because `sh:minCount` and
`sh:qualifiedMinCount` differ only in what the property is. -/
theorem count_ge_iff {L : List Term} {Q : Term → Prop} {n : Nat}
    (hnd : L.Nodup) (hmem : ∀ v, v ∈ L ↔ Q v) :
    n ≤ L.length ↔ ∃ l : List Term, l.Nodup ∧ (∀ v ∈ l, Q v) ∧ n ≤ l.length := by
  constructor
  · intro h
    exact ⟨L, hnd, fun v hv => (hmem v).mp hv, h⟩
  · rintro ⟨l, hl, hm, hlen⟩
    exact Nat.le_trans hlen
      (List.Nodup.length_le_of_subset hl (fun v hv => (hmem v).mpr (hm v hv)))

theorem count_le_iff {L : List Term} {Q : Term → Prop} {n : Nat}
    (hnd : L.Nodup) (hmem : ∀ v, v ∈ L ↔ Q v) :
    L.length ≤ n ↔ ∀ l : List Term, l.Nodup → (∀ v ∈ l, Q v) → l.length ≤ n := by
  constructor
  · intro h l hl hm
    exact Nat.le_trans
      (List.Nodup.length_le_of_subset hl (fun v hv => (hmem v).mpr (hm v hv))) h
  · intro h
    exact h L hnd (fun v hv => (hmem v).mp hv)

theorem minCount_iff {G : Graph} {pa : Path} {f : Term} {n : Nat} :
    n ≤ (valueNodes G pa f).length ↔
      ∃ l : List Term, l.Nodup ∧ (∀ v ∈ l, IsValue G pa f v) ∧ n ≤ l.length :=
  count_ge_iff nodup_valueNodes (fun _ => mem_valueNodes)

theorem maxCount_iff {G : Graph} {pa : Path} {f : Term} {n : Nat} :
    (valueNodes G pa f).length ≤ n ↔
      ∀ l : List Term, l.Nodup → (∀ v ∈ l, IsValue G pa f v) → l.length ≤ n :=
  count_le_iff nodup_valueNodes (fun _ => mem_valueNodes)

/-! ## The qualified value shape

`collect` has already run the inner shape at every value node, so the qualifying
nodes are read off its output rather than recomputed. The two lemmas below are what
turn that output into the set the counting lemmas above need. -/

theorem nodup_qualifyingNodes {out : List (Term × List Result)} {L : List Term}
    (hmap : out.map Prod.fst = L) (hnd : L.Nodup) : (qualifyingNodes out).Nodup := by
  rw [qualifyingNodes]
  refine List.Nodup.sublist ?_ (hmap ▸ hnd)
  exact List.Sublist.map _ List.filter_sublist

theorem mem_qualifyingNodes {G : Graph} {q : Shape} {pa : Path} {f : Term}
    {out : List (Term × List Result)} (hmap : out.map Prod.fst = valueNodes G pa f)
    (hconf : ∀ p ∈ out, (p.2 = [] ↔ Conf G q p.1)) {v : Term} :
    v ∈ qualifyingNodes out ↔ (IsValue G pa f v ∧ Conf G q v) := by
  rw [qualifyingNodes, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [List.mem_filter] at hp
    obtain ⟨hpo, he⟩ := hp
    refine ⟨?_, (hconf p hpo).mp (List.isEmpty_iff.mp he)⟩
    apply mem_valueNodes.mp
    rw [← hmap]
    exact List.mem_map.mpr ⟨p, hpo, rfl⟩
  · rintro ⟨hv, hc⟩
    have hin : v ∈ out.map Prod.fst := by rw [hmap]; exact mem_valueNodes.mpr hv
    obtain ⟨p, hp, hp1⟩ := List.mem_map.mp hin
    refine ⟨p, ?_, hp1⟩
    rw [List.mem_filter]
    refine ⟨hp, ?_⟩
    rw [List.isEmpty_iff]
    exact (hconf p hp).mpr (by rw [hp1]; exact hc)

/-- The `sh:class` decision is exactly SHACL instancehood, given a closed
superclass set. Soundness comes from the iteration, completeness from the closure
check. -/
theorem klass_iff {G : Graph} {c f : Term} {S : List Term} (hcl : subClosure G c = some S) :
    (typesOf G f).any (fun t => S.contains t) = true ↔ IsInstance G c f := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, hS⟩
    exact ⟨t, mem_typesOf.mp ht, subClosure_sound hcl t (List.contains_iff_mem.mp hS)⟩
  · rintro ⟨t, hG, hsc⟩
    exact ⟨t, mem_typesOf.mpr hG, List.contains_iff_mem.mpr (subClosure_complete hcl hsc)⟩

/-- `sh:datatype`, including the refusal. Stated for an arbitrary graph because the
constraint does not read the graph at all: it is a question about the term. -/
theorem evalDatatype_spec {G : Graph} {d src f : Term} {rs : List Result}
    (h : evalDatatype d src f = .ok rs) :
    (rs = [] ↔ Conf G (.datatype d) f) ∧ (∀ x ∈ rs, ¬ Conf G x.blamed x.blamedNode) := by
  rw [evalDatatype] at h
  cases hl : asLiteral f with
  | none =>
      simp only [hl] at h
      refine leafCase h ?_ rfl rfl
      constructor
      · intro hb; exact absurd hb (by simp)
      · rintro ⟨l, hl', -, -⟩
        rw [hl] at hl'
        exact absurd hl' (by simp)
  | some l =>
      simp only [hl] at h
      by_cases hd : l.dt = d
      · rw [if_pos hd] at h
        cases hx : lexOK l with
        | none => simp only [hx] at h; exact absurd h (by simp)
        | some b =>
            simp only [hx] at h
            refine leafCase h ?_ rfl rfl
            constructor
            · intro hb
              exact ⟨l, hl, hd, by rw [hx, hb]⟩
            · rintro ⟨l', hl', -, hok⟩
              rw [hl] at hl'
              injection hl' with e
              subst e
              exact Option.some.inj (hx.symm.trans hok)
      · rw [if_neg hd] at h
        refine leafCase h ?_ rfl rfl
        constructor
        · intro hb; exact absurd hb (by simp)
        · rintro ⟨l', hl', hdt, -⟩
          rw [hl] at hl'
          injection hl' with e
          subst e
          exact absurd hdt hd

/-- The four value-range constraints at once. The hypothesis `hb` is what ties a
particular constraint to a particular set of accepted orders, and it is discharged
by `Iff.rfl` at each use because `Spec.lean` states those four clauses in exactly
this form. -/
theorem evalCompare_spec {G : Graph} {ok : List Cmp} {comp : Term} {s : Shape}
    {c src f : Term} {rs : List Result}
    (h : evalCompare ok comp s c src f = .ok rs) (hb : Conf G s f ↔ CmpIs ok c f) :
    (rs = [] ↔ Conf G s f) ∧ (∀ x ∈ rs, ¬ Conf G x.blamed x.blamedNode) := by
  rw [evalCompare] at h
  cases hc : cmpTerms c f with
  | none => simp only [hc] at h; exact absurd h (by simp)
  | some k =>
      simp only [hc] at h
      refine leafCase h ?_ rfl rfl
      rw [hb, CmpIs]
      constructor
      · intro hk
        exact ⟨k, hc, List.contains_iff_mem.mp hk⟩
      · rintro ⟨k', hk', hm⟩
        rw [hc] at hk'
        injection hk' with e
        subst e
        exact List.contains_iff_mem.mpr hm

/-- Every constraint that asks a question about the string a value node denotes, at
once: the two lengths and `sh:pattern`. Includes the blank-node rule and the refusal
on an escaped spelling. -/
theorem evalStr_spec {G : Graph} {P : List Char → Bool} {Q : List Char → Prop} {comp : Term}
    {s : Shape} {src f : Term} {rs : List Result}
    (h : evalStr P comp s src f = .ok rs) (hPQ : ∀ cs, P cs = true ↔ Q cs)
    (hb : Conf G s f ↔ StrProp f Q) :
    (rs = [] ↔ Conf G s f) ∧ (∀ x ∈ rs, ¬ Conf G x.blamed x.blamedNode) := by
  rw [evalStr] at h
  cases hs : strRep f with
  | chars cs =>
      simp only [hs] at h
      refine leafCase h ?_ rfl rfl
      rw [hb, StrProp]
      constructor
      · intro hp
        exact ⟨cs, hs, (hPQ _).mp hp⟩
      · rintro ⟨cs', hs', hq⟩
        rw [hs] at hs'
        injection hs' with e
        subst e
        exact (hPQ _).mpr hq
  | noString =>
      simp only [hs] at h
      refine leafCase h ?_ rfl rfl
      rw [hb, StrProp]
      constructor
      · intro hp; exact absurd hp (by simp)
      · rintro ⟨cs, hs', -⟩
        rw [hs] at hs'
        exact absurd hs' (by simp)
  | unknown => simp only [hs] at h; exact absurd h (by simp)

/-- The two length constraints, as the special case where the question is about the
number of characters. -/
theorem evalLength_spec {G : Graph} {P : Nat → Bool} {Q : Nat → Prop} {comp : Term}
    {s : Shape} {src f : Term} {rs : List Result}
    (h : evalLength P comp s src f = .ok rs) (hPQ : ∀ n, P n = true ↔ Q n)
    (hb : Conf G s f ↔ StrLen f Q) :
    (rs = [] ↔ Conf G s f) ∧ (∀ x ∈ rs, ¬ Conf G x.blamed x.blamedNode) :=
  evalStr_spec (by rw [evalLength] at h; exact h) (fun cs => hPQ cs.length) hb

/-! ## The pattern matcher decides the pattern relation

`mem_reRem` is the whole content: the remainders the matcher enumerates are exactly
the remainders the relation admits. Both directions, by induction on the pattern. -/

theorem mem_reRem {fold : Bool} : ∀ (items : List Item) (s r : List Char),
    r ∈ reRem fold items s ↔ ItemsMatch fold items s r
  | [], s, r => by
      rw [reRem.eq_def, ItemsMatch]
      simp [eq_comm]
  | it :: rest, s, r => by
      rw [reRem.eq_def, ItemsMatch]
      cases hq : it.quant with
      | one =>
          simp only [hq]
          cases s with
          | nil => simp
          | cons c s' =>
              by_cases ha : itemAdmits fold it c = true
              · simp only [ha, if_pos]
                rw [mem_reRem rest s' r]
                constructor
                · intro h; exact ⟨c, s', rfl, ha, h⟩
                · rintro ⟨c', s'', he, -, h⟩
                  injection he with e1 e2
                  subst e1
                  subst e2
                  exact h
              · simp only [Bool.not_eq_true] at ha
                simp only [ha, Bool.false_eq_true, if_false, List.not_mem_nil, false_iff]
                rintro ⟨c', s'', he, ha', -⟩
                injection he with e1 e2
                subst e1
                rw [ha] at ha'
                exact absurd ha' (by simp)
      | star =>
          simp only [hq]
          rw [List.mem_flatMap]
          constructor
          · rintro ⟨k, hk, hr⟩
            rw [List.mem_filter, List.mem_range] at hk
            obtain ⟨-, hall⟩ := hk
            refine ⟨s.take k, s.drop k, (List.take_append_drop k s).symm, ?_,
              (mem_reRem rest _ r).mp hr⟩
            intro c hc
            exact (List.all_eq_true.mp hall) c hc
          · rintro ⟨pre, s', hcat, hall, hm⟩
            refine ⟨pre.length, ?_, ?_⟩
            · rw [List.mem_filter, List.mem_range]
              constructor
              · subst hcat
                simp
                omega
              · rw [List.all_eq_true]
                intro c hc
                refine hall c ?_
                rw [hcat] at hc
                simpa using hc
            · rw [hcat]
              simpa using (mem_reRem rest s' r).mpr hm

theorem mem_suffixesOf : ∀ {s t : List Char}, t ∈ suffixesOf s ↔ ∃ pre, s = pre ++ t
  | [], t => by
      rw [suffixesOf, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨[], rfl⟩
      · rintro ⟨pre, h⟩
        exact (List.append_eq_nil_iff.mp h.symm).2
  | c :: s, t => by
      rw [suffixesOf, List.mem_cons, mem_suffixesOf]
      constructor
      · rintro (rfl | ⟨pre, rfl⟩)
        · exact ⟨[], rfl⟩
        · exact ⟨c :: pre, rfl⟩
      · rintro ⟨pre, h⟩
        cases pre with
        | nil => exact Or.inl (by simpa using h.symm)
        | cons a pre' =>
            refine Or.inr ⟨pre', ?_⟩
            injection h with h1 h2

theorem matchFrom_iff {re : Regex} {t : List Char} :
    ((reRem re.fold re.items t).any fun r => !re.anchorEnd || r.isEmpty) = true ↔
      ∃ r, ItemsMatch re.fold re.items t r ∧ (re.anchorEnd = true → r = []) := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨r, hr, hb⟩
    refine ⟨r, (mem_reRem _ _ _).mp hr, ?_⟩
    intro he
    rw [he] at hb
    exact List.isEmpty_iff.mp (by simpa using hb)
  · rintro ⟨r, hm, he⟩
    refine ⟨r, (mem_reRem _ _ _).mpr hm, ?_⟩
    cases hae : re.anchorEnd with
    | true => simp [he hae]
    | false => simp

/-- **The matcher decides the pattern relation**, anchors and search included. -/
theorem regexMatchB_iff {re : Regex} {s : List Char} :
    regexMatchB re s = true ↔ RegexMatch re s := by
  rw [regexMatchB, List.any_eq_true, RegexMatch]
  constructor
  · rintro ⟨t, ht, hb⟩
    obtain ⟨r, hm, he⟩ := matchFrom_iff.mp hb
    by_cases hs : re.anchorStart = true
    · rw [if_pos hs, List.mem_singleton] at ht
      subst ht
      exact ⟨[], t, r, rfl, fun _ => rfl, hm, he⟩
    · rw [if_neg hs] at ht
      obtain ⟨pre, hpre⟩ := mem_suffixesOf.mp ht
      exact ⟨pre, t, r, hpre, fun h => absurd h hs, hm, he⟩
  · rintro ⟨pre, suf, r, hcat, hps, hm, he⟩
    refine ⟨suf, ?_, matchFrom_iff.mpr ⟨r, hm, he⟩⟩
    by_cases hs : re.anchorStart = true
    · rw [if_pos hs, List.mem_singleton]
      have hp : pre = [] := hps hs
      subst hp
      simpa using hcat.symm
    · rw [if_neg hs]
      exact mem_suffixesOf.mpr ⟨pre, hcat⟩

/-! ## The property-pair constraints -/

theorem cmpPair_ok {ok : List Cmp} {v w : Term} {b : Bool} (h : cmpPair ok v w = .ok b) :
    b = true ↔ CmpIs ok v w := by
  rw [cmpPair] at h
  cases hc : cmpTerms v w with
  | none => simp only [hc] at h; exact absurd h (by simp)
  | some k =>
      simp only [hc] at h
      injection h with h
      subst h
      rw [CmpIs]
      constructor
      · intro hk; exact ⟨k, hc, List.contains_iff_mem.mp hk⟩
      · rintro ⟨k', hk', hm⟩
        rw [hc] at hk'
        injection hk' with e
        subst e
        exact List.contains_iff_mem.mpr hm

theorem cmpRow_ok {ok : List Cmp} {v : Term} :
    ∀ {ws : List Term} {b : Bool}, cmpRow ok v ws = .ok b → (b = true ↔ ∀ w ∈ ws, CmpIs ok v w)
  | [], b, h => by rw [cmpRow] at h; injection h with h; subst h; simp
  | w :: ws, b, h => by
      rw [cmpRow] at h
      cases ha : cmpPair ok v w with
      | error e => rw [bind_error_eq ha] at h; exact absurd h (by simp)
      | ok a =>
          rw [bind_ok_eq ha] at h
          cases hb : cmpRow ok v ws with
          | error e => rw [bind_error_eq hb] at h; exact absurd h (by simp)
          | ok b' =>
              rw [bind_ok_eq hb] at h
              injection h with h
              subst h
              rw [Bool.and_eq_true, cmpPair_ok ha, cmpRow_ok hb]
              constructor
              · rintro ⟨h1, h2⟩ u hu
                rcases List.mem_cons.mp hu with rfl | hu
                · exact h1
                · exact h2 u hu
              · intro hall
                exact ⟨hall w (List.mem_cons_self ..),
                  fun u hu => hall u (List.mem_cons_of_mem _ hu)⟩

theorem cmpGrid_ok {ok : List Cmp} :
    ∀ {vs ws : List Term} {b : Bool}, cmpGrid ok vs ws = .ok b →
      (b = true ↔ ∀ v ∈ vs, ∀ w ∈ ws, CmpIs ok v w)
  | [], _, b, h => by rw [cmpGrid] at h; injection h with h; subst h; simp
  | v :: vs, ws, b, h => by
      rw [cmpGrid] at h
      cases ha : cmpRow ok v ws with
      | error e => rw [bind_error_eq ha] at h; exact absurd h (by simp)
      | ok a =>
          rw [bind_ok_eq ha] at h
          cases hb : cmpGrid ok vs ws with
          | error e => rw [bind_error_eq hb] at h; exact absurd h (by simp)
          | ok b' =>
              rw [bind_ok_eq hb] at h
              injection h with h
              subst h
              rw [Bool.and_eq_true, cmpRow_ok ha, cmpGrid_ok hb]
              constructor
              · rintro ⟨h1, h2⟩ u hu
                rcases List.mem_cons.mp hu with rfl | hu
                · exact h1
                · exact h2 u hu
              · intro hall
                exact ⟨hall v (List.mem_cons_self ..),
                  fun u hu => hall u (List.mem_cons_of_mem _ hu)⟩

theorem equals_iff {G : Graph} {pa : Option Path} {q f : Term} :
    ((valueNodesOrSelf G pa f).all (fun v => (valueNodes G (.pred q) f).contains v) &&
     (valueNodes G (.pred q) f).all (fun w => (valueNodesOrSelf G pa f).contains w)) = true ↔
      ∀ v, IsValueOrSelf G pa f v ↔ (⟨f, q, v⟩ : Triple) ∈ G := by
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩ v
    constructor
    · intro hv
      exact mem_valueNodes.mp
        (List.contains_iff_mem.mp (h1 v (mem_valueNodesOrSelf.mpr hv)))
    · intro hv
      exact mem_valueNodesOrSelf.mp
        (List.contains_iff_mem.mp (h2 v (mem_valueNodes.mpr hv)))
  · intro h
    refine ⟨?_, ?_⟩
    · intro v hv
      exact List.contains_iff_mem.mpr
        (mem_valueNodes.mpr ((h v).mp (mem_valueNodesOrSelf.mp hv)))
    · intro w hw
      exact List.contains_iff_mem.mpr
        (mem_valueNodesOrSelf.mpr ((h w).mpr (mem_valueNodes.mp hw)))

theorem disjoint_iff {G : Graph} {pa : Option Path} {q f : Term} :
    ((valueNodesOrSelf G pa f).all (fun v => !((valueNodes G (.pred q) f).contains v))) = true ↔
      ∀ v, IsValueOrSelf G pa f v → (⟨f, q, v⟩ : Triple) ∉ G := by
  rw [List.all_eq_true]
  constructor
  · intro h v hv hG
    have hm : v ∈ valueNodes G (Path.pred q) f := mem_valueNodes.mpr hG
    have hc : (valueNodes G (Path.pred q) f).contains v = true := List.contains_iff_mem.mpr hm
    have hb := h v (mem_valueNodesOrSelf.mpr hv)
    rw [hc] at hb
    exact absurd hb (by simp)
  · intro h v hv
    by_cases hc : (valueNodes G (Path.pred q) f).contains v = true
    · have hG : (⟨f, q, v⟩ : Triple) ∈ G := mem_valueNodes.mp (List.contains_iff_mem.mp hc)
      exact absurd hG (h v (mem_valueNodesOrSelf.mp hv))
    · simp only [Bool.not_eq_true] at hc
      rw [hc]
      simp

theorem languageIn_iff {tags : List String} {f : Term} :
    (match langOf f with
     | none => false
     | some t => tags.any (fun r => langMatches r t)) = true ↔
      ∃ t, langOf f = some t ∧ ∃ r ∈ tags, langMatches r t = true := by
  cases h : langOf f with
  | none => simp
  | some t => simp [List.any_eq_true]

theorem uniqueLangB_iff {vs : List Term} :
    uniqueLangB vs = true ↔
      ∀ v ∈ vs, ∀ w ∈ vs, v ≠ w → (langOf v = none ∨ langOf v ≠ langOf w) := by
  rw [uniqueLangB]
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
    Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · intro h v hv w hw hne
    rcases h v hv w hw with he | hn | hd
    · exact absurd he hne
    · exact Or.inl hn
    · exact Or.inr hd
  · intro h v hv w hw
    by_cases hvw : v = w
    · exact Or.inl hvw
    · rcases h v hv w hw hvw with hn | hd
      · exact Or.inr (Or.inl hn)
      · exact Or.inr (Or.inr hd)

/-! ## The two theorems -/

/-- Both halves at once, because the `forAll` case needs the verdict half of the
induction hypothesis and the licensing case needs the other. -/
theorem eval_agrees (G : Graph) (s : Shape) :
    ∀ (src f : Term) (rs : List Result), eval G s src f = .ok rs →
      (rs = [] ↔ Conf G s f) ∧ (∀ r ∈ rs, ¬ Conf G r.blamed r.blamedNode) := by
  induction s with
  | top =>
      intro src f rs h
      rw [eval] at h
      injection h with h
      subst h
      exact ⟨Iff.intro (fun _ => trivial) (fun _ => rfl), by simp⟩
  | bot =>
      intro src f rs h
      rw [eval] at h
      exact leafCase h (Iff.intro (fun hb => absurd hb (by simp)) (fun hc => hc.elim)) rfl rfl
  | klass c =>
      intro src f rs h
      rw [eval, evalKlass] at h
      cases hcl : subClosure G c with
      | none => simp only [hcl] at h; exact absurd h (by simp)
      | some S =>
          simp only [hcl] at h
          exact leafCase h (klass_iff hcl) rfl rfl
  | datatype d =>
      intro src f rs h
      rw [eval] at h
      exact evalDatatype_spec h
  | nodeKind k =>
      intro src f rs h
      rw [eval] at h
      exact leafCase h nodeKindOK_iff rfl rfl
  | hasValue v =>
      intro src f rs h
      rw [eval] at h
      exact leafCase h beq_iff_eq rfl rfl
  | inSet vs =>
      intro src f rs h
      rw [eval] at h
      exact leafCase h List.contains_iff_mem rfl rfl
  | minInclusive c =>
      intro src f rs h
      rw [eval] at h
      exact evalCompare_spec h Iff.rfl
  | maxInclusive c =>
      intro src f rs h
      rw [eval] at h
      exact evalCompare_spec h Iff.rfl
  | minExclusive c =>
      intro src f rs h
      rw [eval] at h
      exact evalCompare_spec h Iff.rfl
  | maxExclusive c =>
      intro src f rs h
      rw [eval] at h
      exact evalCompare_spec h Iff.rfl
  | minLength n =>
      intro src f rs h
      rw [eval] at h
      exact evalLength_spec h (fun _ => decide_eq_true_iff) Iff.rfl
  | maxLength n =>
      intro src f rs h
      rw [eval] at h
      exact evalLength_spec h (fun _ => decide_eq_true_iff) Iff.rfl
  | pattern re =>
      intro src f rs h
      rw [eval] at h
      exact evalStr_spec h (fun _ => regexMatchB_iff) Iff.rfl
  | languageIn tags =>
      intro src f rs h
      rw [eval] at h
      exact leafCase h languageIn_iff rfl rfl
  | equals pa q =>
      intro src f rs h
      rw [eval] at h
      exact leafCase h equals_iff rfl rfl
  | disjoint pa q =>
      intro src f rs h
      rw [eval] at h
      exact leafCase h disjoint_iff rfl rfl
  | lessThan pa q =>
      intro src f rs h
      rw [eval] at h
      cases hg : cmpGrid [Cmp.lt] (valueNodesOrSelf G pa f) (valueNodes G (.pred q) f) with
      | error e => rw [bind_error_eq hg] at h; exact absurd h (by simp)
      | ok b =>
          rw [bind_ok_eq hg] at h
          refine leafCase h ?_ rfl rfl
          rw [cmpGrid_ok hg]
          constructor
          · intro hall v w hv hw
            exact hall v (mem_valueNodesOrSelf.mpr hv) w (mem_valueNodes.mpr hw)
          · intro hall v hv w hw
            exact hall v w (mem_valueNodesOrSelf.mp hv) (mem_valueNodes.mp hw)
  | lessThanOrEq pa q =>
      intro src f rs h
      rw [eval] at h
      cases hg : cmpGrid [Cmp.lt, Cmp.eq] (valueNodesOrSelf G pa f)
          (valueNodes G (.pred q) f) with
      | error e => rw [bind_error_eq hg] at h; exact absurd h (by simp)
      | ok b =>
          rw [bind_ok_eq hg] at h
          refine leafCase h ?_ rfl rfl
          rw [cmpGrid_ok hg]
          constructor
          · intro hall v w hv hw
            exact hall v (mem_valueNodesOrSelf.mpr hv) w (mem_valueNodes.mpr hw)
          · intro hall v hv w hw
            exact hall v w (mem_valueNodesOrSelf.mp hv) (mem_valueNodes.mp hw)
  | qualifiedMin pa q n ihq =>
      intro src f rs h
      rw [eval] at h
      cases hc : collect (fun v => eval G q src v) (valueNodes G pa f) with
      | error e => rw [bind_error_eq hc] at h; exact absurd h (by simp)
      | ok out =>
          rw [bind_ok_eq hc] at h
          obtain ⟨hmap, hall⟩ := collect_ok hc
          have hconf : ∀ p ∈ out, (p.2 = [] ↔ Conf G q p.1) :=
            fun p hp => (ihq src p.1 p.2 (hall p hp)).1
          refine leafCase h ?_ rfl rfl
          exact Iff.trans decide_eq_true_iff
            (count_ge_iff (nodup_qualifyingNodes hmap nodup_valueNodes)
              (fun _ => mem_qualifyingNodes hmap hconf))
  | qualifiedMax pa q n ihq =>
      intro src f rs h
      rw [eval] at h
      cases hc : collect (fun v => eval G q src v) (valueNodes G pa f) with
      | error e => rw [bind_error_eq hc] at h; exact absurd h (by simp)
      | ok out =>
          rw [bind_ok_eq hc] at h
          obtain ⟨hmap, hall⟩ := collect_ok hc
          have hconf : ∀ p ∈ out, (p.2 = [] ↔ Conf G q p.1) :=
            fun p hp => (ihq src p.1 p.2 (hall p hp)).1
          refine leafCase h ?_ rfl rfl
          exact Iff.trans decide_eq_true_iff
            (count_le_iff (nodup_qualifyingNodes hmap nodup_valueNodes)
              (fun _ => mem_qualifyingNodes hmap hconf))
  | closed allowed =>
      intro src f rs h
      rw [eval] at h
      injection h with h
      subst h
      refine leafCaseMany closedResults_nil_iff ?_
      intro x hx
      rw [closedResults, List.mem_map] at hx
      obtain ⟨t, -, hxt⟩ := hx
      rw [← hxt]
      exact ⟨rfl, rfl⟩
  | report comp a iha =>
      intro src f rs h
      rw [eval] at h
      cases ha : eval G a src f with
      | error e => rw [bind_error_eq ha] at h; exact absurd h (by simp)
      | ok ra =>
          rw [bind_ok_eq ha] at h
          obtain ⟨ha1, -⟩ := iha src f ra ha
          refine leafCase h ?_ rfl rfl
          rw [List.isEmpty_iff]
          exact ha1
  | uniqueLang pa =>
      intro src f rs h
      rw [eval] at h
      refine leafCase h ?_ rfl rfl
      rw [uniqueLangB_iff]
      constructor
      · intro hall v w hv hw hne
        exact hall v (mem_valueNodesOrSelf.mpr hv) w (mem_valueNodesOrSelf.mpr hw) hne
      · intro hall v hv w hw hne
        exact hall v w (mem_valueNodesOrSelf.mp hv) (mem_valueNodesOrSelf.mp hw) hne
  | minCount pa n =>
      intro src f rs h
      rw [eval] at h
      exact leafCase h (Iff.trans decide_eq_true_iff minCount_iff) rfl rfl
  | maxCount pa n =>
      intro src f rs h
      rw [eval] at h
      exact leafCase h (Iff.trans decide_eq_true_iff maxCount_iff) rfl rfl
  | hasValueOn pa v =>
      intro src f rs h
      rw [eval] at h
      exact leafCase h (Iff.trans List.contains_iff_mem mem_valueNodes) rfl rfl
  | named src' a ih =>
      intro src f rs h
      rw [eval] at h
      exact ih src' f rs h
  | both a b iha ihb =>
      intro src f rs h
      rw [eval] at h
      cases ha : eval G a src f with
      | error e => rw [bind_error_eq ha] at h; exact absurd h (by simp)
      | ok ra =>
          rw [bind_ok_eq ha] at h
          cases hb : eval G b src f with
          | error e => rw [bind_error_eq hb] at h; exact absurd h (by simp)
          | ok rb =>
              rw [bind_ok_eq hb] at h
              injection h with h
              subst h
              obtain ⟨ha1, ha2⟩ := iha src f ra ha
              obtain ⟨hb1, hb2⟩ := ihb src f rb hb
              refine ⟨?_, ?_⟩
              · rw [List.append_eq_nil_iff]
                exact and_congr ha1 hb1
              · intro r hr
                rcases List.mem_append.mp hr with hr | hr
                · exact ha2 r hr
                · exact hb2 r hr
  | andC a b iha ihb =>
      intro src f rs h
      rw [eval] at h
      cases ha : eval G a src f with
      | error e => rw [bind_error_eq ha] at h; exact absurd h (by simp)
      | ok ra =>
          rw [bind_ok_eq ha] at h
          cases hb : eval G b src f with
          | error e => rw [bind_error_eq hb] at h; exact absurd h (by simp)
          | ok rb =>
              rw [bind_ok_eq hb] at h
              obtain ⟨ha1, -⟩ := iha src f ra ha
              obtain ⟨hb1, -⟩ := ihb src f rb hb
              refine leafCase h ?_ rfl rfl
              rw [Bool.and_eq_true, List.isEmpty_iff, List.isEmpty_iff]
              exact and_congr ha1 hb1
  | orC a b iha ihb =>
      intro src f rs h
      rw [eval] at h
      cases ha : eval G a src f with
      | error e => rw [bind_error_eq ha] at h; exact absurd h (by simp)
      | ok ra =>
          rw [bind_ok_eq ha] at h
          cases hb : eval G b src f with
          | error e => rw [bind_error_eq hb] at h; exact absurd h (by simp)
          | ok rb =>
              rw [bind_ok_eq hb] at h
              obtain ⟨ha1, -⟩ := iha src f ra ha
              obtain ⟨hb1, -⟩ := ihb src f rb hb
              refine leafCase h ?_ rfl rfl
              rw [Bool.or_eq_true, List.isEmpty_iff, List.isEmpty_iff]
              exact or_congr ha1 hb1
  | notC a iha =>
      intro src f rs h
      rw [eval] at h
      cases ha : eval G a src f with
      | error e => rw [bind_error_eq ha] at h; exact absurd h (by simp)
      | ok ra =>
          rw [bind_ok_eq ha] at h
          obtain ⟨ha1, -⟩ := iha src f ra ha
          refine leafCase h ?_ rfl rfl
          rw [Bool.not_eq_true', List.isEmpty_eq_false_iff]
          exact not_congr ha1
  | nodeC a iha =>
      intro src f rs h
      rw [eval] at h
      cases ha : eval G a src f with
      | error e => rw [bind_error_eq ha] at h; exact absurd h (by simp)
      | ok ra =>
          rw [bind_ok_eq ha] at h
          obtain ⟨ha1, -⟩ := iha src f ra ha
          refine leafCase h ?_ rfl rfl
          rw [List.isEmpty_iff]
          exact ha1
  | forAll pa a iha =>
      intro src f rs h
      rw [eval] at h
      cases hc : collect (fun v => eval G a src v) (valueNodes G pa f) with
      | error e => rw [bind_error_eq hc] at h; exact absurd h (by simp)
      | ok out =>
          rw [bind_ok_eq hc] at h
          injection h with h
          subst h
          obtain ⟨hmap, hall⟩ := collect_ok hc
          refine ⟨?_, ?_⟩
          · rw [List.flatMap_eq_nil_iff]
            constructor
            · intro hnil v hv
              have hvn : v ∈ out.map Prod.fst := by
                rw [hmap]; exact mem_valueNodes.mpr hv
              obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hvn
              obtain ⟨hq2, -⟩ := iha src q.1 q.2 (hall q hq)
              rw [← hq1]
              exact hq2.mp (List.map_eq_nil_iff.mp (hnil q hq))
            · intro hconf q hq
              rw [List.map_eq_nil_iff]
              obtain ⟨hq2, -⟩ := iha src q.1 q.2 (hall q hq)
              refine hq2.mpr (hconf q.1 ?_)
              apply mem_valueNodes.mp
              rw [← hmap]
              exact List.mem_map.mpr ⟨q, hq, rfl⟩
          · intro r hr
            obtain ⟨q, hq, hrq⟩ := List.mem_flatMap.mp hr
            obtain ⟨r₀, hr₀, hlift⟩ := List.mem_map.mp hrq
            obtain ⟨-, hq3⟩ := iha src q.1 q.2 (hall q hq)
            rw [← hlift, liftValue_blamed, liftValue_blamedNode]
            exact hq3 r₀ hr₀

/-- **Soundness and completeness of the verdict.** The evaluator reports no results
exactly when the specification says the focus node conforms. -/
theorem eval_conforms_iff {G : Graph} {s : Shape} {src f : Term} {rs : List Result}
    (h : eval G s src f = .ok rs) : rs = [] ↔ Conf G s f :=
  (eval_agrees G s src f rs h).1

/-- **Soundness of the report.** Every result the evaluator produces blames a node
that really does fail the constraint it is blamed for. -/
theorem eval_results_licensed {G : Graph} {s : Shape} {src f : Term} {rs : List Result}
    (h : eval G s src f = .ok rs) : ∀ r ∈ rs, ¬ Conf G r.blamed r.blamedNode :=
  (eval_agrees G s src f rs h).2

/-- The `sh:sourceShape` label cannot change a verdict. Cheap to state, and it is
the one structural property a reader would otherwise have to take on trust when
reading `eval`, which threads that label through every case. -/
theorem conf_named (G : Graph) (src : Term) (a : Shape) (f : Term) :
    Conf G (.named src a) f ↔ Conf G a f := Iff.rfl

end Shacl
