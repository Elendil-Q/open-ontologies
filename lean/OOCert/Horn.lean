import OOCert.Rules
import OOCert.Witness

/-!
# User-supplied Horn rules, and one theorem for all of them

`Rules.lean` hardcodes twenty rules and `Soundness.lean` proves one lemma per
rule against a condition in `Semantics.lean`. That does not scale to rules the
user writes, which is what RIF Core, Datalog and SWRL are.

This file adds a second rule family to the certificate. A rule is a first-order
Horn sentence over triple patterns,

    forall x1..xn.  B1 and ... and Bk  ->  H

and a certificate step cites a rule by its index in a rule set `R`, a
substitution, and the premises it used. No new semantic condition is added:
`SatRule I r` is defined from `Interp.sat`, which already exists. The rule is an
ASSUMPTION the certificate carries, not a fact about OWL vocabulary, and that is
what makes one theorem cover every rule at once.

## Two readings of "the interpretation satisfies the rule", and which one is used

`SatRuleFO` is the honest first-order reading: variables range over DOMAIN
ELEMENTS. `SatRule` is the term reading: variables range over TERMS, and the
rule is satisfied when every ground instance is. `SatRuleFO.to_SatRule` proves
the first implies the second (take the valuation `I.iota` composed with the
substitution).

The checker is proved sound against `SatRule`, the WEAKER hypothesis. That is
deliberate and it is the opposite of the usual trade: a weaker hypothesis admits
MORE interpretations, so "every such interpretation satisfies t" is a STRONGER
claim. `horn_certificate_sound_fo` then derives the first-order statement as a
corollary, so a user who means the first-order rule is covered a fortiori.

What the term reading costs is nothing on the soundness side and everything on
the side nobody is claiming: it gives no converse, and a countermodel to
`SatRule` is not automatically a countermodel to the first-order rule.

## Variables in predicate position

`Interp` has one ternary `iext` over the domain, so a property is a domain
element like any other. A variable may therefore stand in predicate position
and the language stays first-order. Eighteen of the twenty built-in rules,
`rdfs7` and `prp-trp` among them, are Horn rules of exactly this shape.
-/
namespace OOCert

abbrev Var := String

/-- A position in a triple pattern: a fixed term, or a variable. -/
inductive Pat
  | const : Term → Pat
  | var : Var → Pat
deriving DecidableEq, Repr

/-- A triple pattern. Any of the three positions may be a variable. -/
structure AtomPat where
  s : Pat
  p : Pat
  o : Pat
deriving DecidableEq, Repr

/-- `forall vars. body -> head`, with the quantifier left implicit: every
variable occurring anywhere in the rule is universally quantified. -/
structure RulePattern where
  name : String
  body : List AtomPat
  head : AtomPat
deriving Repr

/-- A substitution is total. Totality is free here and removes a whole class of
"unbound variable" failure: the semantic side quantifies over every total
substitution, so a junk value for a variable the rule never mentions changes
nothing. -/
abbrev Subst := Var → Term

def Pat.inst (sigma : Subst) : Pat → Term
  | .const c => c
  | .var v => sigma v

def AtomPat.inst (sigma : Subst) (a : AtomPat) : Triple :=
  ⟨a.s.inst sigma, a.p.inst sigma, a.o.inst sigma⟩

/-! ## The two satisfaction relations -/

/-- Term reading: every ground instance of the rule holds. -/
def SatRule (I : Interp) (r : RulePattern) : Prop :=
  ∀ sigma : Subst,
    (∀ a ∈ r.body, I.sat (AtomPat.inst sigma a)) → I.sat (AtomPat.inst sigma r.head)

def Pat.denote (I : Interp) (v : Var → I.D) : Pat → I.D
  | .const c => I.ι c
  | .var x => v x

def AtomPat.holds (I : Interp) (v : Var → I.D) (a : AtomPat) : Prop :=
  I.iext (a.p.denote I v) (a.s.denote I v) (a.o.denote I v)

/-- First-order reading: variables range over domain elements. -/
def SatRuleFO (I : Interp) (r : RulePattern) : Prop :=
  ∀ v : Var → I.D, (∀ a ∈ r.body, a.holds I v) → r.head.holds I v

theorem denote_inst (I : Interp) (sigma : Subst) (q : Pat) :
    q.denote I (fun x => I.ι (sigma x)) = I.ι (q.inst sigma) := by
  cases q <;> rfl

theorem holds_inst (I : Interp) (sigma : Subst) (a : AtomPat) :
    a.holds I (fun x => I.ι (sigma x)) ↔ I.sat (AtomPat.inst sigma a) := by
  unfold AtomPat.holds Interp.sat AtomPat.inst
  simp only [denote_inst]

/-- The first-order reading implies the term reading. This is the whole reason
the checker may be proved against the term reading and still speak about
genuine first-order rules. -/
theorem SatRuleFO.to_SatRule {I : Interp} {r : RulePattern}
    (h : SatRuleFO I r) : SatRule I r := by
  intro sigma hb
  refine (holds_inst I sigma r.head).mp (h (fun x => I.ι (sigma x)) ?_)
  intro a ha
  exact (holds_inst I sigma a).mpr (hb a ha)

/-! ## Entailment relative to a rule set -/

/-- `G, R ⊨ t`: every interpretation that models `G` and satisfies every rule of
`R` satisfies `t`. Note that `Model I G` still carries the RDF semantic
conditions, so this is entailment over the RDF-conditioned model class, not pure
first-order entailment from `G ∪ R`. Pure first-order entailment implies it, not
the other way round. -/
def ModelR (G : List Triple) (R : List RulePattern) (I : Interp) : Prop :=
  Model I G ∧ ∀ r ∈ R, SatRule I r

def EntailsR (G : List Triple) (R : List RulePattern) (t : Triple) : Prop :=
  EntailsIn (ModelR G R) t

theorem EntailsR.of_entails {G : List Triple} {R : List RulePattern} {t : Triple}
    (h : Entails G t) : EntailsR G R t := fun I hI => h I hI.1

theorem EntailsR.of_mem {G : List Triple} {R : List RulePattern} {t : Triple}
    (h : t ∈ G) : EntailsR G R t := fun _ hI => hI.1.facts t h

/-! ## The checker -/

/-- Indexing written out rather than borrowed, so the membership lemma below is
local and the file does not move with the standard library. -/
def nth? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => nth? as n

theorem nth?_mem {α : Type} {l : List α} :
    ∀ {n : Nat} {a : α}, nth? l n = some a → a ∈ l := by
  induction l with
  | nil => intro n a h; cases n <;> simp [nth?] at h
  | cons b bs ih =>
    intro n a h
    cases n with
    | zero =>
      simp only [nth?, Option.some.injEq] at h
      subst h
      exact List.Mem.head bs
    | succ m => exact List.Mem.tail _ (ih h)

/-- A step that cites a user rule. `binds` is the substitution the engine used,
written out; `premises` are the triples it matched, in the rule's body order. -/
structure HornStep where
  rule : Nat
  binds : List (Var × Term)
  premises : List Triple
  conclusion : Triple
deriving Repr

/-- A cited binding list read as a total substitution. The default for a
variable the list does not mention is the variable's own name, and it is
UNREACHABLE on any variable the cited rule mentions, because `checkHornStep`
refuses a binding that does not cover them: see `bindingWellFormed` and
`lookup_eq_substOf_of_covers`. The total form is kept because the semantic side
quantifies over total substitutions, not because any value it invents is
meaningful. -/
def substOf (l : List (Var × Term)) : Subst := fun v => (List.lookup v l).getD v

/-! ## The binding list as a data structure

Decision 0008. A binding list is DATA before it is a substitution, and a
certificate whose binding is malformed is refused rather than repaired.

Two shapes are refused, and both were found by running this checker and the
independent Isabelle/HOL one over 1,718 certificates and comparing:

* a REPEATED KEY, because the value of the variable would then be decided by
  the tie-break inside whatever lookup function a checker happens to use.
  `List.lookup` here is first-wins, while `dict()` and `HashMap::from_iter`
  elsewhere are last-wins, and a certificate whose meaning depends on that is
  not evidence of anything;
* an INCOMPLETE BINDING, because `substOf`'s default would otherwise mint a
  term out of a variable's NAME in the rule file and put it in the conclusion.

A binding for a variable the rule never mentions is NOT refused. It cannot make
a step mean two things, because it is never consulted, and refusing it would be
a tidiness rule rather than a determinacy one. -/

def Pat.varList : Pat → List Var
  | .const _ => []
  | .var v => [v]

/-- Every variable the pattern mentions, with repeats. Deduplicating would cost
a `DecidableEq` pass and buy nothing: every use is under `List.all` or a
membership, and neither can see a repeat. -/
def AtomPat.varList (a : AtomPat) : List Var :=
  a.s.varList ++ a.p.varList ++ a.o.varList

/-- Every variable the rule mentions, body AND head. The head matters: a rule
whose head carries a variable its body never binds is the sharp case, and it is
the one where the silent default fabricated a term. -/
def RulePattern.varList (r : RulePattern) : List Var :=
  (r.body.map AtomPat.varList).flatten ++ r.head.varList

/-- No key occurs twice. Written out rather than borrowed so that it is a
`Bool` the witness file can `decide`, and so this file does not move with the
standard library. -/
def keysDistinct : List (Var × Term) → Bool
  | [] => true
  | (v, _) :: rest => rest.all (fun p => p.1 != v) && keysDistinct rest

/-- Every variable the cited rule mentions has a binding. -/
def bindsCover (r : RulePattern) (l : List (Var × Term)) : Bool :=
  r.varList.all (fun v => (List.lookup v l).isSome)

/-- The binding list is well formed FOR THE CITED RULE. Not a property of the
list alone: coverage is relative to the rule, which is why this is checked after
the rule has been looked up and not at parse time. -/
def bindingWellFormed (r : RulePattern) (l : List (Var × Term)) : Bool :=
  keysDistinct l && bindsCover r l

/-- With distinct keys, `List.lookup`'s first-wins tie-break stops deciding
anything: the value is the one the certificate wrote. This is the whole content
of refusing a repeated key, and it is why the refusal is not a taste. -/
theorem lookup_eq_of_mem_of_keysDistinct :
    ∀ {l : List (Var × Term)}, keysDistinct l = true →
      ∀ {v : Var} {t : Term}, (v, t) ∈ l → List.lookup v l = some t := by
  intro l
  induction l with
  | nil => intro _ v t hm; simp at hm
  | cons p rest ih =>
    obtain ⟨w, u⟩ := p
    intro hd v t hm
    simp only [keysDistinct, Bool.and_eq_true] at hd
    obtain ⟨hne, hrest⟩ := hd
    rcases List.mem_cons.mp hm with heq | hmem
    · have hv : v = w := congrArg Prod.fst heq
      have ht : t = u := congrArg Prod.snd heq
      subst hv; subst ht
      simp [List.lookup]
    · have hvw : ¬ v = w := by
        intro h
        subst h
        have := List.all_eq_true.mp hne (v, t) hmem
        simp at this
      have hbeq : (v == w) = false := by
        cases hb : v == w with
        | false => rfl
        | true => exact absurd (eq_of_beq hb) hvw
      simp only [List.lookup, hbeq]
      exact ih hrest hmem

/-- On every variable the rule mentions, the total substitution's value is the
value the binding list actually supplies. The default is never reached, so
`substOf` and a PARTIAL lookup agree everywhere the checker looks. -/
theorem lookup_eq_substOf_of_covers {r : RulePattern} {l : List (Var × Term)}
    (h : bindsCover r l = true) {v : Var} (hv : v ∈ r.varList) :
    List.lookup v l = some (substOf l v) := by
  have hs := List.all_eq_true.mp h v hv
  unfold substOf
  cases hl : List.lookup v l with
  | none => rw [hl] at hs; simp at hs
  | some t => simp

theorem Pat.inst_congr {sigma tau : Subst} {q : Pat}
    (h : ∀ v ∈ q.varList, sigma v = tau v) : q.inst sigma = q.inst tau := by
  cases q with
  | const c => rfl
  | var x => exact h x (by simp [Pat.varList])

theorem AtomPat.inst_congr {sigma tau : Subst} {a : AtomPat}
    (h : ∀ v ∈ a.varList, sigma v = tau v) : a.inst sigma = a.inst tau := by
  unfold AtomPat.varList at h
  unfold AtomPat.inst
  rw [Pat.inst_congr (fun v hv => h v (by simp [List.mem_append, hv])),
      Pat.inst_congr (fun v hv => h v (by simp [List.mem_append, hv])),
      Pat.inst_congr (fun v hv => h v (by simp [List.mem_append, hv]))]

theorem mem_varList_of_mem_body {r : RulePattern} {a : AtomPat} (ha : a ∈ r.body)
    {v : Var} (hv : v ∈ a.varList) : v ∈ r.varList :=
  List.mem_append_left _ (List.mem_flatten.mpr ⟨a.varList, List.mem_map_of_mem ha, hv⟩)

theorem mem_varList_of_mem_head {r : RulePattern} {v : Var} (hv : v ∈ r.head.varList) :
    v ∈ r.varList :=
  List.mem_append_right _ hv

/-- **The format decision, as a theorem.** Once the binding list is well formed
for the cited rule, EVERY total substitution that extends it instantiates that
rule the same way. So a checker that carries the binding as a partial map and
one that carries it as a total function with a default are reading the same
certificate, and the certificate has one meaning rather than one per checker.
Nothing below depends on this: it is the statement the differential could not
make for itself. -/
theorem wellFormed_determines_instantiation {r : RulePattern} {l : List (Var × Term)}
    (h : bindingWellFormed r l = true) {sigma : Subst}
    (hext : ∀ v t, List.lookup v l = some t → sigma v = t) :
    r.body.map (AtomPat.inst sigma) = r.body.map (AtomPat.inst (substOf l)) ∧
      AtomPat.inst sigma r.head = AtomPat.inst (substOf l) r.head := by
  simp only [bindingWellFormed, Bool.and_eq_true] at h
  have agree : ∀ v ∈ r.varList, sigma v = substOf l v := fun v hv =>
    hext v _ (lookup_eq_substOf_of_covers h.2 hv)
  refine ⟨List.map_congr_left ?_, AtomPat.inst_congr ?_⟩
  · intro a ha
    exact AtomPat.inst_congr (fun v hv => agree v (mem_varList_of_mem_body ha hv))
  · intro v hv
    exact agree v (mem_varList_of_mem_head hv)

/-- Check one Horn step. Three things are contracted, not two.

The BINDING must be well formed for the cited rule (decision 0008): distinct
keys, and a binding for every variable the rule mentions.

The PREMISE ORDER is part of the contract: the premise list must be the body
instantiated, in order. A certificate with the right triples in the wrong order
is rejected, which is a false alarm and never a false pass.

Both refusals are strictness and neither carries soundness content. That is the
point. `checkHornStep_sound` holds with or without them, because `EntailsR`
quantifies over every total substitution; what they buy is that the certificate
means ONE thing, which is not something a soundness theorem can say. -/
def checkHornStep (R : List RulePattern) (k : Triple → Bool) (st : HornStep) : Bool :=
  match nth? R st.rule with
  | none => false
  | some r =>
      bindingWellFormed r st.binds &&
      decide (st.premises = r.body.map (AtomPat.inst (substOf st.binds))) &&
      st.premises.all k &&
      decide (st.conclusion = AtomPat.inst (substOf st.binds) r.head)

/-- THE THEOREM, one step. No case analysis on the rule: there is nothing to
case on.

The statement is unchanged by decision 0008, and so is the proof below the first
line: the well-formedness conjunct is destructured and DISCARDED. That is the
honest accounting. Adding a check makes `checkHornStep = true` a stronger
hypothesis, so this theorem cannot have been weakened to accommodate it, and the
new refusals earn their place somewhere a soundness theorem cannot look:
`wellFormed_determines_instantiation` above, and `HornWitness.lean` for the
evidence that the checker still accepts anything at all. -/
theorem checkHornStep_sound {G : List Triple} {R : List RulePattern} {k : Triple → Bool}
    {st : HornStep} (hk : ∀ t, k t = true → EntailsR G R t)
    (h : checkHornStep R k st = true) : EntailsR G R st.conclusion := by
  unfold checkHornStep at h
  revert h
  cases hr : nth? R st.rule with
  | none => intro h; simp at h
  | some r =>
    intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨_hwf, hprem⟩, hall⟩, hconc⟩ := h
    intro I hI
    obtain ⟨M, hR⟩ := hI
    have hrmem : r ∈ R := nth?_mem hr
    have hbody : ∀ a ∈ r.body, I.sat (AtomPat.inst (substOf st.binds) a) := by
      intro a ha
      have hmem : AtomPat.inst (substOf st.binds) a ∈ st.premises := by
        rw [hprem]
        exact List.mem_map_of_mem ha
      exact hk _ (List.all_eq_true.mp hall _ hmem) I ⟨M, hR⟩
    rw [hconc]
    exact hR r hrmem (substOf st.binds) hbody

/-! ## Certificates

The same discipline `checkAll` uses: steps are checked in order, and a premise
counts as known when it is asserted in `G` or was concluded by an EARLIER step.
Nothing else changes, and in particular no step may cite itself. -/

def checkHornAll (inG : Triple → Bool) (R : List RulePattern) :
    List HornStep → Std.HashSet Triple → Bool
  | [], _ => true
  | st :: rest, derived =>
      checkHornStep R (fun t => inG t || derived.contains t) st &&
      checkHornAll inG R rest (derived.insert st.conclusion)

/-- The Horn checker. `G` is the asserted graph, `R` the rule set the
certificate is relative to, `steps` the certificate. -/
def checkHornCert (G : List Triple) (R : List RulePattern) (steps : List HornStep) : Bool :=
  let gset := Std.HashSet.ofList G
  checkHornAll (fun t => gset.contains t) R steps ∅

theorem checkHornAll_sound {G : List Triple} {R : List RulePattern} {inG : Triple → Bool}
    (hG : ∀ t, inG t = true → t ∈ G) :
    ∀ (steps : List HornStep) (derived : Std.HashSet Triple),
      (∀ t, derived.contains t = true → EntailsR G R t) →
      checkHornAll inG R steps derived = true →
      ∀ st ∈ steps, EntailsR G R st.conclusion := by
  intro steps
  induction steps with
  | nil => intro _ _ _ st hst; simp at hst
  | cons st rest ih =>
    intro derived hD h st' hst'
    simp only [checkHornAll, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hk : ∀ t, (inG t || derived.contains t) = true → EntailsR G R t := by
      intro t ht
      simp only [Bool.or_eq_true] at ht
      rcases ht with hx | hx
      · exact EntailsR.of_mem (hG t hx)
      · exact hD t hx
    have hst : EntailsR G R st.conclusion := checkHornStep_sound hk h1
    have hD' : ∀ t, (derived.insert st.conclusion).contains t = true → EntailsR G R t := by
      intro t ht
      rw [Std.HashSet.contains_insert] at ht
      simp only [Bool.or_eq_true, beq_iff_eq] at ht
      rcases ht with rfl | ht
      · exact hst
      · exact hD t ht
    rcases List.mem_cons.mp hst' with rfl | hmem
    · exact hst
    · exact ih _ hD' h2 st' hmem

/-- **The generic theorem.** One statement, every user-supplied Horn rule at
once. There is no per-rule lemma and no per-rule arm: the rule set is a
parameter, and the rule it cites is discharged by the hypothesis the certificate
carries. -/
theorem horn_certificate_sound (G : List Triple) (R : List RulePattern) (steps : List HornStep)
    (h : checkHornCert G R steps = true) : ∀ st ∈ steps, EntailsR G R st.conclusion := by
  unfold checkHornCert at h
  refine checkHornAll_sound (G := G) (R := R)
    (inG := fun t => (Std.HashSet.ofList G).contains t) ?_ steps ∅ ?_ h
  · intro t ht
    rw [Std.HashSet.contains_ofList] at ht
    simpa using ht
  · intro t ht
    simp at ht

/-- The same theorem stated for the honest first-order reading of the rules,
which is what a user who writes RIF Core or SWRL means. It is a corollary and
not a separate proof, because `SatRuleFO` implies `SatRule`. -/
theorem horn_certificate_sound_fo (G : List Triple) (R : List RulePattern) (steps : List HornStep)
    (h : checkHornCert G R steps = true) :
    ∀ st ∈ steps, ∀ I : Interp, Model I G → (∀ r ∈ R, SatRuleFO I r) → I.sat st.conclusion := by
  intro st hst I M hR
  exact horn_certificate_sound G R steps h st hst I ⟨M, fun r hr => (hR r hr).to_SatRule⟩


/-! The axiom tripwire, as `Soundness.lean` has one. A `sorry` or a
`native_decide` anywhere under these theorems fails the build here. -/
/-- info: 'OOCert.SatRuleFO.to_SatRule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SatRuleFO.to_SatRule

/-- info: 'OOCert.wellFormed_determines_instantiation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms wellFormed_determines_instantiation

/-- info: 'OOCert.lookup_eq_of_mem_of_keysDistinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lookup_eq_of_mem_of_keysDistinct

/-- info: 'OOCert.horn_certificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms horn_certificate_sound

/-- info: 'OOCert.horn_certificate_sound_fo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms horn_certificate_sound_fo

end OOCert
