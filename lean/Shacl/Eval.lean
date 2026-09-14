import Shacl.Spec

/-!
# The evaluator

An executable function from a graph, a shape and a focus node to either a list of
validation results or a refusal to answer. `Shacl/Agreement.lean` proves it agrees
with `Shacl/Spec.lean`.

## The third answer

`eval` returns `Except Refusal (List Result)`, and the error side is not a crash.
It is the evaluator declining to decide, in the two places where deciding would
mean guessing:

* a literal carries the datatype a `sh:datatype` constraint asks for, and this
  development does not know that datatype's lexical space, so it cannot say whether
  the literal is well formed;
* the `rdfs:subClassOf` closure did not reach a fixpoint inside the iteration
  budget, so the set of superclasses computed is not known to be complete.

Both are reported by name. A refusal propagates: one undecidable constraint makes
the whole run undetermined rather than letting the rest of the report imply a
verdict the undecided part could have overturned. The alternative, answering
`conforms` because the hard constraint was skipped, is the failure mode this
repository exists to catch.

The second refusal has never been observed to fire: `subIter` runs `|G| + 1`
rounds and the closure of a subclass graph with `|G|` edges settles in at most
`|G|`. It is a guard against an argument, not against a measurement, and the guard
is cheap enough to keep.

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

/-- The value nodes of `f` along `pa`, without duplicates. -/
def valueNodes (G : Graph) (pa : Path) (f : Term) : List Term :=
  dedup ((G.filter (pa.sel f)).map pa.val)

theorem mem_valueNodes {G : Graph} {pa : Path} {f v : Term} :
    v ∈ valueNodes G pa f ↔ IsValue G pa f v := by
  rw [valueNodes, mem_dedup, List.mem_map]
  cases pa with
  | pred p =>
    constructor
    · rintro ⟨t, ht, hv⟩
      rw [List.mem_filter] at ht
      obtain ⟨hG, hsel⟩ := ht
      simp only [Path.sel, Bool.and_eq_true, beq_iff_eq] at hsel
      simp only [Path.val] at hv
      cases t
      simp_all [IsValue]
    · intro h
      refine ⟨⟨f, p, v⟩, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨h, by simp [Path.sel]⟩
  | inv p =>
    constructor
    · rintro ⟨t, ht, hv⟩
      rw [List.mem_filter] at ht
      obtain ⟨hG, hsel⟩ := ht
      simp only [Path.sel, Bool.and_eq_true, beq_iff_eq] at hsel
      simp only [Path.val] at hv
      cases t
      simp_all [IsValue]
    · intro h
      refine ⟨⟨v, p, f⟩, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨h, by simp [Path.sel]⟩

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
deriving Repr

def Refusal.describe : Refusal → String
  | .unknownLexicalSpace dt lex =>
      s!"sh:datatype: the lexical space of {dt} is not implemented, so \"{lex}\" cannot be judged well formed"
  | .subclassClosureNotReached c =>
      s!"sh:class: the rdfs:subClassOf closure of {c} did not settle within the iteration budget"

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

/-- Decide a leaf constraint: no results when it holds, exactly one when it does not. -/
def check (b : Bool) (r : Result) : Except Refusal (List Result) :=
  if b then .ok [] else .ok [r]

/-- Re-aim a result produced at a value node so that it is reported against the
focus node, with the path and the value filled in.

Only results that do not already carry a path are re-aimed. A result that has one
came from a property shape nested inside this one and already names its own focus
node, which is the value node here; SHACL reports it unchanged. -/
def liftValue (f : Term) (pa : Path) (v : Term) (r : Result) : Result :=
  { r with focus := f, path := some pa, value := some v }

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

/-! ## The evaluator -/

def eval (G : Graph) : Shape → Term → Term → Except Refusal (List Result)
  | .top, _, _ => .ok []
  | .bot, src, f => check false (violation src C.bot .bot f)
  | .klass c, src, f => evalKlass G c src f
  | .datatype d, src, f => evalDatatype d src f
  | .nodeKind k, src, f => check (nodeKindOK k f) (violation src C.nodeKind (.nodeKind k) f)
  | .hasValue v, src, f => check (f == v) (violation src C.hasValue (.hasValue v) f)
  | .inSet vs, src, f => check (vs.contains f) (violation src C.inSet (.inSet vs) f)
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
