import Shacl.Spec

/-!
# The evaluator

An executable function from a graph, a shape and a focus node to either a list of
validation results or a refusal to answer. `Shacl/Agreement.lean` proves it agrees
with `Shacl/Spec.lean`.

## The third answer

`eval` returns `Except Refusal (List Result)`, and the error side is not a crash.
It is the evaluator declining to decide, in the four places where deciding would
mean guessing:

* a literal carries the datatype a `sh:datatype` constraint asks for, and this
  development does not know that datatype's lexical space, so it cannot say whether
  the literal is well formed;
* a value-range or property-pair constraint has to order two terms and `cmpTerms`
  knows no rule that orders them. Note that this is NOT the case where SPARQL's `<`
  raises a type error: that one is a verdict and produces a violation;
* a length or pattern constraint has to read the string a spelling denotes and the
  spelling carries a backslash escape, which nothing here decodes;
* the `rdfs:subClassOf` closure did not reach a fixpoint inside the iteration
  budget, so the set of superclasses computed is not known to be complete.

All four are reported by name. A refusal propagates: one undecidable constraint
makes the whole run undetermined rather than letting the rest of the report imply a
verdict the undecided part could have overturned. The alternative, answering
`conforms` because the hard constraint was skipped, is the failure mode this
repository exists to catch.

The last refusal has never been observed to fire: `subIter` runs `|G| + 1`
rounds and the closure of a subclass graph with `|G|` edges settles in at most
`|G|`. It is a guard against an argument, not against a measurement, and the guard
is cheap enough to keep. The first three all fire against the W3C suite or against
the fixtures in `tests/fixtures/shaclcore/`.

## Performance

Everything is lists and linear scans. The subclass closure is recomputed for each
`sh:class` constraint at each focus node. That is quadratic in the graph and fine
for the graphs a shapes test uses; it is not a validator for a large store, and
nothing here pretends otherwise.
-/
namespace Shacl

/-! ## Small list utilities -/

/-- Duplicate-free version of a list, keeping the last occurrence of each element.
`List.eraseDups` is in core but carries no `Nodup` lemma there, and the counting
constraints need one. -/
def dedup [DecidableEq α] : List α → List α
  | [] => []
  | a :: l =>
    let d := dedup l
    if a ∈ d then d else a :: d

theorem mem_dedup [DecidableEq α] {a : α} : ∀ {l : List α}, a ∈ dedup l ↔ a ∈ l
  | [] => by simp [dedup]
  | b :: l => by
    simp only [dedup]
    by_cases h : b ∈ dedup l
    · simp only [h, if_pos]
      constructor
      · intro ha; exact List.mem_cons_of_mem _ (mem_dedup.mp ha)
      · intro ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact h
        · exact mem_dedup.mpr ha
    · simp only [h, if_neg, not_false_iff]
      constructor
      · intro ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mem_dedup.mp ha)
      · intro ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mem_dedup.mpr ha)

theorem nodup_dedup [DecidableEq α] : ∀ (l : List α), (dedup l).Nodup
  | [] => by simp [dedup]
  | a :: l => by
    simp only [dedup]
    by_cases h : a ∈ dedup l
    · simp only [h, if_pos]; exact nodup_dedup l
    · simp only [h, if_neg, not_false_iff]
      exact List.nodup_cons.mpr ⟨h, nodup_dedup l⟩

/-! ## Reading the graph -/

/-- The value nodes of `f` along `pa`, without duplicates.

The recursion is on the PATH, not on the graph, so it terminates for the same
reason a path is finite. That is the whole reason `sh:zeroOrMorePath` is not a
constructor: it would need a fixpoint over the graph instead. -/
def valueNodes (G : Graph) : Path → Term → List Term
  | .pred p, f => dedup ((G.filter (fun t => t.s == f && t.p == p)).map Triple.o)
  | .inv p, f => dedup ((G.filter (fun t => t.p == p && t.o == f)).map Triple.s)
  | .seq a b, f => dedup ((valueNodes G a f).flatMap (fun m => valueNodes G b m))
  | .alt a b, f => dedup (valueNodes G a f ++ valueNodes G b f)
  | .zeroOrOne a, f => dedup (f :: valueNodes G a f)

theorem mem_valueNodes {G : Graph} : ∀ {pa : Path} {f v : Term},
    v ∈ valueNodes G pa f ↔ IsValue G pa f v
  | .pred p, f, v => by
      rw [valueNodes, mem_dedup, List.mem_map]
      constructor
      · rintro ⟨t, ht, hv⟩
        rw [List.mem_filter] at ht
        obtain ⟨hG, hsel⟩ := ht
        simp only [Bool.and_eq_true, beq_iff_eq] at hsel
        cases t
        simp_all [IsValue]
      · intro h
        refine ⟨⟨f, p, v⟩, ?_, rfl⟩
        rw [List.mem_filter]
        exact ⟨h, by simp⟩
  | .inv p, f, v => by
      rw [valueNodes, mem_dedup, List.mem_map]
      constructor
      · rintro ⟨t, ht, hv⟩
        rw [List.mem_filter] at ht
        obtain ⟨hG, hsel⟩ := ht
        simp only [Bool.and_eq_true, beq_iff_eq] at hsel
        cases t
        simp_all [IsValue]
      · intro h
        refine ⟨⟨v, p, f⟩, ?_, rfl⟩
        rw [List.mem_filter]
        exact ⟨h, by simp⟩
  | .seq a b, f, v => by
      rw [valueNodes, mem_dedup, List.mem_flatMap]
      constructor
      · rintro ⟨m, hm, hv⟩
        exact ⟨m, mem_valueNodes.mp hm, mem_valueNodes.mp hv⟩
      · rintro ⟨m, hm, hv⟩
        exact ⟨m, mem_valueNodes.mpr hm, mem_valueNodes.mpr hv⟩
  | .alt a b, f, v => by
      rw [valueNodes, mem_dedup, List.mem_append]
      constructor
      · rintro (h | h)
        · exact Or.inl (mem_valueNodes.mp h)
        · exact Or.inr (mem_valueNodes.mp h)
      · rintro (h | h)
        · exact Or.inl (mem_valueNodes.mpr h)
        · exact Or.inr (mem_valueNodes.mpr h)
  | .zeroOrOne a, f, v => by
      rw [valueNodes, mem_dedup, List.mem_cons]
      constructor
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr (mem_valueNodes.mp h)
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr (mem_valueNodes.mpr h)

theorem nodup_valueNodes {G : Graph} {pa : Path} {f : Term} : (valueNodes G pa f).Nodup := by
  cases pa <;> (rw [valueNodes]; exact nodup_dedup _)

/-- The value nodes of a shape that may or may not carry a path. -/
def valueNodesOrSelf (G : Graph) : Option Path → Term → List Term
  | none, f => [f]
  | some pa, f => valueNodes G pa f

theorem mem_valueNodesOrSelf {G : Graph} {pa : Option Path} {f v : Term} :
    v ∈ valueNodesOrSelf G pa f ↔ IsValueOrSelf G pa f v := by
  cases pa with
  | none => simp [valueNodesOrSelf, IsValueOrSelf]
  | some p => exact mem_valueNodes

theorem nodup_valueNodesOrSelf {G : Graph} {pa : Option Path} {f : Term} :
    (valueNodesOrSelf G pa f).Nodup := by
  cases pa with
  | none => simp [valueNodesOrSelf]
  | some p => rw [valueNodesOrSelf]; exact nodup_valueNodes

/-- Every `rdf:type` value of `x`. Duplicates are harmless here: only membership is
ever asked. -/
def typesOf (G : Graph) (x : Term) : List Term :=
  (G.filter (fun t => t.s == x && t.p == V.type)).map Triple.o

theorem mem_typesOf {G : Graph} {x t : Term} :
    t ∈ typesOf G x ↔ (⟨x, V.type, t⟩ : Triple) ∈ G := by
  rw [typesOf, List.mem_map]
  constructor
  · rintro ⟨u, hu, hv⟩
    rw [List.mem_filter] at hu
    obtain ⟨hG, hsel⟩ := hu
    simp only [Bool.and_eq_true, beq_iff_eq] at hsel
    cases u
    simp_all
  · intro h
    refine ⟨⟨x, V.type, t⟩, ?_, rfl⟩
    rw [List.mem_filter]
    exact ⟨h, by simp⟩

/-! ## The subclass closure

`subClosure G c` computes the set of classes that are `rdfs:subClassOf*` of `c`,
by iterating a one-step expansion and then CHECKING that the result is closed. The
check is what makes both halves of the agreement provable: soundness follows from
the iteration, completeness follows from closure alone by induction on the
`SubClassStar` derivation, and neither needs an argument about how many rounds are
enough. -/

/-- One round: every `x` with `x rdfs:subClassOf y` for a `y` already in `S`. -/
def subStep (G : Graph) (S : List Term) : List Term :=
  dedup (S ++ (G.filter (fun t => t.p == V.subClassOf && S.contains t.o)).map Triple.s)

/-- Iterate, stopping early once a round adds nothing. -/
def subIter (G : Graph) : Nat → List Term → List Term
  | 0, S => S
  | n + 1, S =>
    let S' := subStep G S
    if S'.length ≤ S.length then S else subIter G n S'

/-- Is `S` closed under the one-step expansion? Decidable, and the whole reason the
completeness half needs no counting argument. -/
def subClosed (G : Graph) (S : List Term) : Bool :=
  G.all (fun t => !(t.p == V.subClassOf) || !(S.contains t.o) || S.contains t.s)

/-- Hand back a set only if it is closed. Separated out so that `subClosure`'s
equation is a single application and the proofs below can `split` on the check
without first having to reduce a `let`. -/
def closeIf (G : Graph) (S : List Term) : Option (List Term) :=
  if subClosed G S then some S else none

/-- The superclass-closed set containing `c`, or `none` when the iteration budget
ran out before a closed set was reached. -/
def subClosure (G : Graph) (c : Term) : Option (List Term) :=
  closeIf G (subIter G (G.length + 1) [c])

theorem mem_subStep {G : Graph} {S : List Term} {x : Term} :
    x ∈ subStep G S ↔ (x ∈ S ∨ ∃ y, (⟨x, V.subClassOf, y⟩ : Triple) ∈ G ∧ y ∈ S) := by
  rw [subStep, mem_dedup, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨t, ht, hv⟩)
    · exact Or.inl h
    · rw [List.mem_filter] at ht
      obtain ⟨hG, hsel⟩ := ht
      simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hsel
      cases t
      simp_all
      exact Or.inr ⟨_, by simp_all, hsel.2⟩
  · rintro (h | ⟨y, hG, hy⟩)
    · exact Or.inl h
    · refine Or.inr ⟨⟨x, V.subClassOf, y⟩, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨hG, by simp [hy]⟩

theorem subset_subStep {G : Graph} {S : List Term} : S ⊆ subStep G S :=
  fun _ h => mem_subStep.mpr (Or.inl h)

theorem subset_subIter {G : Graph} : ∀ (n : Nat) (S : List Term), S ⊆ subIter G n S
  | 0, _ => fun _ h => h
  | n + 1, S => by
    simp only [subIter]
    by_cases h : (subStep G S).length ≤ S.length
    · simp only [h, if_pos]; exact fun _ hx => hx
    · simp only [h, if_neg, not_false_iff]
      exact fun _ hx => subset_subIter n _ (subset_subStep hx)

/-- Everything the iteration produces really is a subclass of the seed. -/
theorem subIter_sound {G : Graph} (P : Term → Prop)
    (hstep : ∀ x y, (⟨x, V.subClassOf, y⟩ : Triple) ∈ G → P y → P x) :
    ∀ (n : Nat) (S : List Term), (∀ x ∈ S, P x) → ∀ x ∈ subIter G n S, P x
  | 0, _, h => h
  | n + 1, S, h => by
    simp only [subIter]
    by_cases hb : (subStep G S).length ≤ S.length
    · simp only [hb, if_pos]; exact h
    · simp only [hb, if_neg, not_false_iff]
      refine subIter_sound P hstep n _ ?_
      intro x hx
      rcases mem_subStep.mp hx with hx | ⟨y, hG, hy⟩
      · exact h x hx
      · exact hstep x y hG (h y hy)

/-- The closure test does what its name says: in a closed set, a subclass edge into
the set drags its subject in. This is the ONLY thing the completeness half needs,
which is why the iteration count never has to be justified. -/
theorem subClosed_step {G : Graph} {S : List Term} (h : subClosed G S = true) {a b : Term}
    (hG : (⟨a, V.subClassOf, b⟩ : Triple) ∈ G) (hb : b ∈ S) : a ∈ S := by
  rw [subClosed, List.all_eq_true] at h
  have hc : (!(V.subClassOf == V.subClassOf) || !(S.contains b) || S.contains a) = true :=
    h _ hG
  rw [beq_self_eq_true, Bool.not_true, Bool.false_or, List.contains_iff_mem.mpr hb,
    Bool.not_true, Bool.false_or] at hc
  exact List.contains_iff_mem.mp hc

/-- `subClosure` hands back exactly the iterate, and only when it is closed. -/
theorem subClosure_eq {G : Graph} {c : Term} {S : List Term}
    (h : subClosure G c = some S) :
    S = subIter G (G.length + 1) [c] ∧ subClosed G S = true := by
  rw [subClosure, closeIf] at h
  by_cases hc : subClosed G (subIter G (G.length + 1) [c]) = true
  · rw [if_pos hc] at h
    injection h with h
    exact ⟨h.symm, h ▸ hc⟩
  · rw [if_neg hc] at h
    exact absurd h (by simp)

theorem subClosure_sound {G : Graph} {c : Term} {S : List Term}
    (h : subClosure G c = some S) : ∀ x ∈ S, SubClassStar G x c := by
  obtain ⟨rfl, _⟩ := subClosure_eq h
  refine subIter_sound (fun x => SubClassStar G x c) (fun _ _ hG hy => .step hG hy) _ _ ?_
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  exact .refl _

/-- In a closed set, membership follows the subclass chain downwards. Induction on
the derivation, with no reference to how the set was built. -/
theorem closed_star {G : Graph} {S : List Term} (hclosed : subClosed G S = true) :
    ∀ {x c : Term}, SubClassStar G x c → c ∈ S → x ∈ S := by
  intro x c hx
  induction hx with
  | refl _ => exact id
  | step hG _ ih => exact fun hc => subClosed_step hclosed hG (ih hc)

theorem subClosure_complete {G : Graph} {c : Term} {S : List Term}
    (h : subClosure G c = some S) : ∀ {x}, SubClassStar G x c → x ∈ S := by
  obtain ⟨hS, hclosed⟩ := subClosure_eq h
  have hseed : c ∈ S := by
    rw [hS]; exact subset_subIter _ _ (List.mem_singleton_self c)
  intro x hx
  exact closed_star hclosed hx hseed

/-! ## Results and refusals -/

/-- One validation result. `focus`, `path`, `value`, `source` and `component` are
the five fields the SHACL report vocabulary uses (`sh:focusNode`, `sh:resultPath`,
`sh:value`, `sh:sourceShape`, `sh:sourceConstraintComponent`).

`blamed` and `blamedNode` are not part of any report. They record WHICH constraint
failed and at WHICH node, so that "this result is justified" is a statement that
can be written down and proved: see `eval_results_licensed`. Without them the
soundness theorem could only be about the conformance boolean, and a validator that
reports the right boolean with the wrong results is not much of a validator. -/
structure Result where
  focus : Term
  path : Option Path
  value : Option Term
  source : Term
  component : Term
  blamed : Shape
  blamedNode : Term
deriving Repr

/-- Why the evaluator declined to answer. -/
inductive Refusal where
  /-- A `sh:datatype` constraint matched a literal whose datatype's lexical space
  this development does not know, so well-formedness is undecided. -/
  | unknownLexicalSpace (dt : Term) (lex : String)
  /-- The `rdfs:subClassOf` iteration did not reach a closed set in budget. -/
  | subclassClosureNotReached (c : Term)
  /-- A value-range or property-pair constraint had to compare two terms by value
  and `cmpTerms` declined. Note that this is NOT the case where SPARQL raises a
  type error: that one is comparable-by-refusal, reported as a violation. -/
  | unknownComparison (a b : Term)
  /-- A length constraint had to count the characters of the string a spelling
  denotes, and the spelling carries a backslash escape that nothing here decodes. -/
  | escapedLexicalForm (t : Term)
deriving Repr

def Refusal.describe : Refusal → String
  | .unknownLexicalSpace dt lex =>
      s!"sh:datatype: the lexical space of {dt} is not implemented, so \"{lex}\" cannot be judged well formed"
  | .subclassClosureNotReached c =>
      s!"sh:class: the rdfs:subClassOf closure of {c} did not settle within the iteration budget"
  | .unknownComparison a b =>
      s!"value comparison: no rule this development implements orders {a} against {b}, and \
         SPARQL's type-error case is not known to apply either, so no order is claimed"
  | .escapedLexicalForm t =>
      s!"string length: {t} carries a backslash escape and escapes are never decoded here, so \
         the length of the string it denotes is unknown"

/-- A result blaming the focus node itself. -/
def violation (src comp : Term) (s : Shape) (f : Term) : Result :=
  { focus := f, path := none, value := some f, source := src, component := comp,
    blamed := s, blamedNode := f }

/-- A result blaming a path rather than a single value: the set constraints
(`sh:minCount`, `sh:maxCount`, `sh:hasValue` on a property shape) are about the
value nodes as a whole, so they carry `sh:resultPath` and no `sh:value`. -/
def violationOn (src comp : Term) (s : Shape) (f : Term) (pa : Path) : Result :=
  { focus := f, path := some pa, value := none, source := src, component := comp,
    blamed := s, blamedNode := f }

/-- A result blaming the value-node SET of a shape that may or may not carry a
path. The property-pair constraints and `sh:uniqueLang` are about the set, so they
name the path when there is one and carry no `sh:value`.

**One result per focus node, not one per offending value.** The Recommendation asks
for a separate result for each value node that breaks `sh:equals`, `sh:disjoint`,
`sh:lessThan` or `sh:lessThanOrEquals`, each carrying that value in `sh:value`.
This validator reports one. The verdict is unaffected and the result it does
produce is licensed by `eval_results_licensed`, but a consumer counting results
will count fewer than a fully conforming validator would. Named here rather than
discovered. -/
def violationPair (src comp : Term) (s : Shape) (f : Term) (pa : Option Path) : Result :=
  { focus := f, path := pa, value := none, source := src, component := comp,
    blamed := s, blamedNode := f }

/-- Decide a leaf constraint: no results when it holds, exactly one when it does not. -/
def check (b : Bool) (r : Result) : Except Refusal (List Result) :=
  if b then .ok [] else .ok [r]

/-- Re-aim a result produced at a value node so that it is reported against the
focus node, with the path and the value filled in.

Only results that do not already carry a path are re-aimed. A result that has one
came from a property shape nested inside this one and already names its own focus
node, which is the value node here; SHACL reports it unchanged. -/
def liftValue (f : Term) (pa : Path) (v : Term) (r : Result) : Result :=
  if r.path.isNone then { r with focus := f, path := some pa, value := some v } else r

/-- Evaluate a shape at each of a list of nodes, keeping the pairing so the caller
can say which node produced which results. Any refusal aborts. -/
def collect (k : Term → Except Refusal (List Result)) :
    List Term → Except Refusal (List (Term × List Result))
  | [] => .ok []
  | v :: vs => do
      let r ← k v
      let rest ← collect k vs
      .ok ((v, r) :: rest)

/-! ## The leaf decisions, each paired with the proposition it decides -/

def nodeKindOK (k : NodeKind) (f : Term) : Bool :=
  match kindOf f with
  | some κ => k.admits κ
  | none => false

theorem nodeKindOK_iff {k : NodeKind} {f : Term} :
    nodeKindOK k f = true ↔ ∃ κ, kindOf f = some κ ∧ k.admits κ = true := by
  rw [nodeKindOK]
  cases h : kindOf f with
  | none => simp
  | some κ => simp

def evalKlass (G : Graph) (c src f : Term) : Except Refusal (List Result) :=
  match subClosure G c with
  | none => .error (.subclassClosureNotReached c)
  | some S => check ((typesOf G f).any (fun t => S.contains t)) (violation src C.klass (.klass c) f)

def evalDatatype (d src f : Term) : Except Refusal (List Result) :=
  match asLiteral f with
  | none => check false (violation src C.datatype (.datatype d) f)
  | some l =>
      if l.dt = d then
        match lexOK l with
        | none => .error (.unknownLexicalSpace l.dt l.lex)
        | some b => check b (violation src C.datatype (.datatype d) f)
      else check false (violation src C.datatype (.datatype d) f)

/-- The four value-range constraints, which differ only in which orders they
accept. A comparison the term model declines to make is a refusal; a comparison it
reports as a SPARQL type error is a violation, because the Recommendation asks
whether the SPARQL expression returns true and a type error does not. -/
def evalCompare (ok : List Cmp) (comp : Term) (s : Shape) (c src f : Term) :
    Except Refusal (List Result) :=
  match cmpTerms c f with
  | none => .error (.unknownComparison c f)
  | some k => check (ok.contains k) (violation src comp s f)

/-- Any constraint that asks a question about the string a value node denotes. A
blank node fails all of them, which is what the Recommendation says in as many
words for `sh:minLength` and `sh:maxLength` and what the approved tests
`core/node/minLength-001` and `core/node/pattern-001` both require. -/
def evalStr (P : List Char → Bool) (comp : Term) (s : Shape) (src f : Term) :
    Except Refusal (List Result) :=
  match strRep f with
  | .chars cs => check (P cs) (violation src comp s f)
  | .noString => check false (violation src comp s f)
  | .unknown => .error (.escapedLexicalForm f)

/-- The two length constraints. -/
def evalLength (P : Nat → Bool) (comp : Term) (s : Shape) (src f : Term) :
    Except Refusal (List Result) :=
  evalStr (fun cs => P cs.length) comp s src f

/-! ## Deciding a pattern

`reRem items s` is the set of REMAINDERS the items can leave after consuming a
prefix of `s`. Reading the answer as a set of remainders rather than as a boolean is
what makes the anchored and unanchored cases one function: `$` asks whether the
empty remainder is among them, and its absence asks whether there is any remainder
at all. -/

def reRem (fold : Bool) : (items : List Item) → (s : List Char) → List (List Char)
  | [], s => [s]
  | it :: rest, s =>
      match it.quant with
      | .one =>
          match s with
          | [] => []
          | c :: s' => if itemAdmits fold it c then reRem fold rest s' else []
      | .star =>
          ((List.range (s.length + 1)).filter
            (fun k => (s.take k).all (fun c => itemAdmits fold it c))).flatMap
              (fun k => reRem fold rest (s.drop k))
  termination_by items => items.length
  decreasing_by all_goals simp

/-- Every suffix of a string, longest first, including the empty one. These are the
positions an unanchored search may start at. -/
def suffixesOf : List Char → List (List Char)
  | [] => [[]]
  | c :: s => (c :: s) :: suffixesOf s

def regexMatchB (re : Regex) (s : List Char) : Bool :=
  (if re.anchorStart then [s] else suffixesOf s).any fun t =>
    (reRem re.fold re.items t).any fun r => !re.anchorEnd || r.isEmpty

/-! ## The two property-pair comparisons

`sh:lessThan` and `sh:lessThanOrEquals` compare every value node against every
value of the other property, so a single unknown comparison anywhere in that grid
makes the whole constraint undetermined. The traversal below binds BOTH halves
before combining them, so a refusal in any cell propagates whatever the other cells
decided: the answer cannot depend on which cell was reached first. -/

def cmpPair (ok : List Cmp) (v w : Term) : Except Refusal Bool :=
  match cmpTerms v w with
  | none => .error (.unknownComparison v w)
  | some k => .ok (ok.contains k)

def cmpRow (ok : List Cmp) (v : Term) : List Term → Except Refusal Bool
  | [] => .ok true
  | w :: ws => do
      let a ← cmpPair ok v w
      let b ← cmpRow ok v ws
      .ok (a && b)

def cmpGrid (ok : List Cmp) : List Term → List Term → Except Refusal Bool
  | [], _ => .ok true
  | v :: vs, ws => do
      let a ← cmpRow ok v ws
      let b ← cmpGrid ok vs ws
      .ok (a && b)

/-- The triples at a value node whose predicate the closed shape does not allow. -/
def closedOffenders (G : Graph) (allowed : List Term) (f : Term) : List Triple :=
  G.filter (fun t => t.s == f && !(allowed.contains t.p))

/-- One result per offending triple, each naming the predicate that was not allowed
and the object that was reached through it, which is what the Recommendation asks
for. All of them blame the same node and the same constraint. -/
def closedResults (G : Graph) (allowed : List Term) (src : Term) (s : Shape) (f : Term) :
    List Result :=
  (closedOffenders G allowed f).map fun t =>
    { focus := f, path := some (.pred t.p), value := some t.o, source := src,
      component := C.closed, blamed := s, blamedNode := f }

/-- The value nodes that conformed, out of what `collect` returned. -/
def qualifyingNodes (out : List (Term × List Result)) : List Term :=
  (out.filter (fun p => p.2.isEmpty)).map Prod.fst

/-- No two distinct value nodes carry the same language tag. -/
def uniqueLangB (vs : List Term) : Bool :=
  vs.all (fun v => vs.all (fun w =>
    (v == w) || ((langOf v).isNone || !(decide (langOf v = langOf w)))))

/-! ## The evaluator -/

def eval (G : Graph) : Shape → Term → Term → Except Refusal (List Result)
  | .top, _, _ => .ok []
  | .bot, src, f => check false (violation src C.bot .bot f)
  | .klass c, src, f => evalKlass G c src f
  | .datatype d, src, f => evalDatatype d src f
  | .nodeKind k, src, f => check (nodeKindOK k f) (violation src C.nodeKind (.nodeKind k) f)
  | .hasValue v, src, f => check (f == v) (violation src C.hasValue (.hasValue v) f)
  | .inSet vs, src, f => check (vs.contains f) (violation src C.inSet (.inSet vs) f)
  | .minInclusive c, src, f => evalCompare [.lt, .eq] C.minInclusive (.minInclusive c) c src f
  | .maxInclusive c, src, f => evalCompare [.gt, .eq] C.maxInclusive (.maxInclusive c) c src f
  | .minExclusive c, src, f => evalCompare [.lt] C.minExclusive (.minExclusive c) c src f
  | .maxExclusive c, src, f => evalCompare [.gt] C.maxExclusive (.maxExclusive c) c src f
  | .minLength n, src, f =>
      evalLength (fun len => decide (n ≤ len)) C.minLength (.minLength n) src f
  | .maxLength n, src, f =>
      evalLength (fun len => decide (len ≤ n)) C.maxLength (.maxLength n) src f
  | .pattern re, src, f =>
      evalStr (fun cs => regexMatchB re cs) C.pattern (.pattern re) src f
  | .languageIn tags, src, f =>
      check (match langOf f with
             | none => false
             | some t => tags.any (fun r => langMatches r t))
        (violation src C.languageIn (.languageIn tags) f)
  | .equals pa q, src, f =>
      check ((valueNodesOrSelf G pa f).all (fun v => (valueNodes G (.pred q) f).contains v) &&
             (valueNodes G (.pred q) f).all (fun w => (valueNodesOrSelf G pa f).contains w))
        (violationPair src C.equals (.equals pa q) f pa)
  | .disjoint pa q, src, f =>
      check ((valueNodesOrSelf G pa f).all
              (fun v => !((valueNodes G (.pred q) f).contains v)))
        (violationPair src C.disjoint (.disjoint pa q) f pa)
  | .lessThan pa q, src, f => do
      let b ← cmpGrid [.lt] (valueNodesOrSelf G pa f) (valueNodes G (.pred q) f)
      check b (violationPair src C.lessThan (.lessThan pa q) f pa)
  | .lessThanOrEq pa q, src, f => do
      let b ← cmpGrid [.lt, .eq] (valueNodesOrSelf G pa f) (valueNodes G (.pred q) f)
      check b (violationPair src C.lessThanOrEq (.lessThanOrEq pa q) f pa)
  | .uniqueLang pa, src, f =>
      check (uniqueLangB (valueNodesOrSelf G pa f))
        (violationPair src C.uniqueLang (.uniqueLang pa) f pa)
  | .closed allowed, src, f => .ok (closedResults G allowed src (.closed allowed) f)
  | .qualifiedMin pa q n, src, f => do
      let out ← collect (fun v => eval G q src v) (valueNodes G pa f)
      check (decide (n ≤ (qualifyingNodes out).length))
        (violationOn src C.qualifiedMin (.qualifiedMin pa q n) f pa)
  | .qualifiedMax pa q n, src, f => do
      let out ← collect (fun v => eval G q src v) (valueNodes G pa f)
      check (decide ((qualifyingNodes out).length ≤ n))
        (violationOn src C.qualifiedMax (.qualifiedMax pa q n) f pa)
  | .minCount pa n, src, f =>
      check (decide (n ≤ (valueNodes G pa f).length))
        (violationOn src C.minCount (.minCount pa n) f pa)
  | .maxCount pa n, src, f =>
      check (decide ((valueNodes G pa f).length ≤ n))
        (violationOn src C.maxCount (.maxCount pa n) f pa)
  | .hasValueOn pa v, src, f =>
      check ((valueNodes G pa f).contains v)
        (violationOn src C.hasValue (.hasValueOn pa v) f pa)
  | .named src' a, _, f => eval G a src' f
  | .both a b, src, f => do
      let ra ← eval G a src f
      let rb ← eval G b src f
      .ok (ra ++ rb)
  | .andC a b, src, f => do
      let ra ← eval G a src f
      let rb ← eval G b src f
      check (ra.isEmpty && rb.isEmpty) (violation src C.andC (.andC a b) f)
  | .orC a b, src, f => do
      let ra ← eval G a src f
      let rb ← eval G b src f
      check (ra.isEmpty || rb.isEmpty) (violation src C.orC (.orC a b) f)
  | .notC a, src, f => do
      let ra ← eval G a src f
      check (!ra.isEmpty) (violation src C.notC (.notC a) f)
  | .nodeC a, src, f => do
      let ra ← eval G a src f
      check ra.isEmpty (violation src C.nodeC (.nodeC a) f)
  | .report comp a, src, f => do
      let ra ← eval G a src f
      check ra.isEmpty (violation src comp (.report comp a) f)
  | .forAll pa a, src, f => do
      let out ← collect (fun v => eval G a src v) (valueNodes G pa f)
      .ok (out.flatMap (fun q => q.2.map (liftValue f pa q.1)))

/-! ## Targets, and the whole report

A validator that evaluates the right shape at the wrong nodes is wrong, so the
target computation is inside the theorem too. -/

/-- The focus nodes one target declaration selects. `sh:targetClass` needs the same
subclass closure `sh:class` does, and refuses in the same way. -/
def focusNodes (G : Graph) : Target → Except Refusal (List Term)
  | .node n => .ok [n]
  | .klass c =>
      match subClosure G c with
      | none => .error (.subclassClosureNotReached c)
      | some S =>
          .ok (dedup ((G.filter (fun tr => tr.p == V.type && S.contains tr.o)).map Triple.s))
  | .subjectsOf p => .ok (dedup ((G.filter (fun tr => tr.p == p)).map Triple.s))
  | .objectsOf p => .ok (dedup ((G.filter (fun tr => tr.p == p)).map Triple.o))

/-- The union of several target declarations, without duplicates. A node named by
two declarations of one shape is validated once; SHACL's target is a set. -/
def focusList (G : Graph) : List Target → Except Refusal (List Term)
  | [] => .ok []
  | t :: ts => do
      let a ← focusNodes G t
      let b ← focusList G ts
      .ok (dedup (a ++ b))

/-- A shape with its identity and its targets, which is what a shapes graph
actually carries. -/
structure ShapeDecl where
  id : Term
  targets : List Target
  shape : Shape
deriving Repr

/-- Validate one declaration: every node any of its targets selects, against its
shape, reported under its own IRI. -/
def evalDecl (G : Graph) (d : ShapeDecl) : Except Refusal (List Result) := do
  let fs ← focusList G d.targets
  let out ← collect (fun f => eval G d.shape d.id f) fs
  .ok (out.flatMap (fun q => q.2))

/-- The whole report: every declaration in the shapes graph. -/
def validate (G : Graph) : List ShapeDecl → Except Refusal (List Result)
  | [] => .ok []
  | d :: ds => do
      let a ← evalDecl G d
      let b ← validate G ds
      .ok (a ++ b)

/-- What the report is about: `f` is targeted by `d`. -/
def Targeted (G : Graph) (d : ShapeDecl) (f : Term) : Prop :=
  ∃ t ∈ d.targets, IsFocus G t f

end Shacl
