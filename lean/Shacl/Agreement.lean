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
  `sh:or`, `sh:not` and `sh:node` each report ONE result for a whole failing
  subtree, which is what the Recommendation asks for, so "one result per failing
  atomic constraint" is neither claimed nor true. What is claimed is that the report
  is empty exactly when the node conforms, which is the property a consumer of
  `sh:conforms` relies on.
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
constraint at that very node. Stating it once keeps eleven cases of the induction
below to three lines each, and keeps the licensing argument from being retyped
eleven times with a chance to drift. -/
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

theorem nodup_valueNodes {G : Graph} {pa : Path} {f : Term} :
    (valueNodes G pa f).Nodup := by
  rw [valueNodes]; exact nodup_dedup _

/-- Counting the deduplicated value nodes decides "there are at least `n` distinct
value nodes". The backward direction is the pigeonhole: any duplicate-free list of
value nodes is a subset of the enumeration, so it cannot be longer. -/
theorem minCount_iff {G : Graph} {pa : Path} {f : Term} {n : Nat} :
    n ≤ (valueNodes G pa f).length ↔
      ∃ l : List Term, l.Nodup ∧ (∀ v ∈ l, IsValue G pa f v) ∧ n ≤ l.length := by
  constructor
  · intro h
    exact ⟨valueNodes G pa f, nodup_valueNodes, fun _ hv => mem_valueNodes.mp hv, h⟩
  · rintro ⟨l, hnd, hmem, hn⟩
    exact Nat.le_trans hn
      (List.Nodup.length_le_of_subset hnd (fun _ hv => mem_valueNodes.mpr (hmem _ hv)))

theorem maxCount_iff {G : Graph} {pa : Path} {f : Term} {n : Nat} :
    (valueNodes G pa f).length ≤ n ↔
      ∀ l : List Term, l.Nodup → (∀ v ∈ l, IsValue G pa f v) → l.length ≤ n := by
  constructor
  · intro h l hnd hmem
    exact Nat.le_trans
      (List.Nodup.length_le_of_subset hnd (fun _ hv => mem_valueNodes.mpr (hmem _ hv))) h
  · intro h
    exact h _ nodup_valueNodes (fun _ hv => mem_valueNodes.mp hv)

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
