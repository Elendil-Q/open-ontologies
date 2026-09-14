import OOCert.W3C
import OOCert.Witness

/-!
# A LIVE conforming model, and the first non-entailment that is about the specification

`W3C.lean` derives fourteen arms from quoted specification cells. That result is
worth nothing until something exhibits a `W3CModel`, and it is worth very little
if the thing that exhibits one is degenerate. This file builds a model that is
not, and uses it twice.

## Why `saturated` is not enough

`Witness.lean`'s `saturated` (domain `Unit`, every relation total) satisfies
`W3C` with `IP := fun _ => True`: every field holds because both sides of every
equality are all of `Unit`. So bare satisfiability of `W3C` is one theorem and
it says nothing, because such a model distinguishes no condition from any other
and refutes nothing. `W3CModel.toModel` proved over an unsatisfiable or a
degenerate `W3C` would be a theorem about nothing that LOOKED better than the
assumption it replaced, which is a strictly worse defect than the one being
repaired. The gate is therefore a NON-DEGENERATE model, and `live_is_live`
below compiles the liveness facts into the build so that the next person to
shorten this graph to fix a `decide` timeout breaks it rather than hollowing it
out silently.

| liveness fact | why it is the gate |
|---|---|
| `IC` has three members and does not swallow the carrier | the conditions are about classes, there are some, and not everything is one |
| `ICEXT(C1)` is the whole domain | a class extension is not empty |
| `ICEXT(C2)` is a PROPER subset of it | two distinct non-trivial extensions, so `sc_fwd` and `sc_bwd` have something to separate |
| `ICEXT(Y)` is empty and `sc_bwd` still does not collapse | the `IC` conjunct of trap T2 doing its job |
| `ICEXT(owl:Restriction)` is a PROPER subset of `IC` | Table 5.2's subset read as a subset and not as an equality |
| `IEXT(p2)` is non-empty | `dom_bwd` and `rng_bwd` are discharged over a relation with a pair in it, not vacuously |

That last row is the one neither formalisation had. The second kernel's
`isabelle/OO_NonVacuity.thy` claims at its own summary that `c_dom_bwd` and
`c_rng_bwd` are live in its model M3, while M3's proofs of those two derive
`False` from their antecedents and an inline comment in the same file says so.
Its M3 therefore exercises the two backward halves VACUOUSLY.
`live_dom_bwd_is_exercised` and `live_rng_bwd_is_exercised` discharge the
`forall x y` clause over `IEXT(p2) = {(alice, bob)}` instead.

## The model

Carrier: two individuals `alice` and `bob`; the five terms `avfPremises`
mentions, as `c1`, `c2`, `filler`, `p1`, `p2`; the vocabulary denotations that
have to be told apart, as `ty`, `sco`, `spo`, `dm`, `rg`, `avf`, `onp`, `cls`,
`restr`; and one junk element `other` absorbing every remaining IRI. Seventeen
elements.

THREE rows are chosen and the conditions determine everything else.

* `IEXT(p1) := empty`, `IEXT(p2) := {(alice, bob)}`, `ICEXT(filler) := empty`.
* `avf_eq` then forces `ICEXT(c1)` to be the whole carrier, because nothing has
  a `p1`-successor at all, and `ICEXT(c2)` to be the carrier minus `alice`,
  because `alice` has the `p2`-successor `bob` and `bob` is not in
  `ICEXT(filler)`.
* So `ICEXT(c1)` is not contained in `ICEXT(c2)`, and `sc_fwd` makes
  `(c1, c2)` in `IEXT(rdfs:subClassOf)` IMPOSSIBLE. That is the refutation.
* And `ICEXT(c2)` IS contained in `ICEXT(c1)`, so `sc_bwd` FORCES
  `(c2, c1)` into `IEXT(rdfs:subClassOf)`, which is what `scm-avf2` draws. The
  witness confirms both halves of the pair, where the Herbrand witness in
  `Witness.lean` asserts one and leaves the other out by hand.
* `IC := {c1, c2, filler}` through `ICEXT(rdfs:Class)`, and
  `ICEXT(owl:Restriction) := {c1, c2}`, a PROPER subset of `IC` per Table 5.2.
  `owl:Restriction` itself is kept out of `IC`, so `sc_bwd` raises no obligation
  about it.
* `sp_bwd`, `dom_bwd` and `rng_bwd` then force the rest of
  `IEXT(rdfs:subPropertyOf)`, `IEXT(rdfs:domain)` and `IEXT(rdfs:range)`, and
  those three tables are a FIXPOINT rather than a free choice: each is defined
  in terms of the others, because `rdfs:subPropertyOf`, `rdfs:domain` and
  `rdfs:range` are themselves members of `IP` and so are subject to the very
  conditions they carry. The tables below are that fixpoint, reached in two
  iterations. `(p2, p1)` is NOT in `IEXT(rdfs:subPropertyOf)`, because
  `IEXT(p2)` is not contained in `IEXT(p1)`, and the domain and range tables
  DIFFER, by exactly `(p2, c2)` and `(ty, c2)`, which is the model separating
  the two rows of Table 5.8 rather than satisfying them both by accident.

The fixpoint is why several entries look strange at first reading.
`rdfs:domain` has `rdfs:subClassOf` in its subject position, for instance. That
is forced, not chosen: `rdfs:subClassOf` is in `IP`, `c1` is in `IC`, every
subject of `IEXT(rdfs:subClassOf)` lies in `ICEXT(c1)` because `ICEXT(c1)` is
everything, and Table 5.8's `rdfs:domain` row is an `iff`. RDF has no sortal
separation, and this is what that costs.

## `IP`, and why these nine

`IP` must contain every element with a non-empty extension, or the structure is
not the image of any conforming interpretation under the bridge in `W3C.lean`
(there, `iext p x y := IP p and (x, y) in IEXT p`, so a pair in an extension
implies its predicate is in `IP`). `live_is_bridge_coherent` checks that below.

The nine are `p1`, `p2` and the seven vocabulary denotations that carry pairs,
and every one of them is in `IP` in any conforming interpretation:

* `owl:allValuesFrom` and `owl:onProperty` by RBS Table 5.3 directly, whose
  second column reads "in IP" for both.
* `rdf:type` by RDF 1.1 Semantics' RDF axiomatic triple
  `rdf:type rdf:type rdf:Property .` together with RBS Table 5.2's row
  `rdf:Property | in IC | = IP`.
* `rdfs:domain`, `rdfs:range` and `rdfs:subPropertyOf` by the RDFS axiomatic
  triples `rdfs:domain rdfs:domain rdf:Property .`,
  `rdfs:range rdfs:domain rdf:Property .` and
  `rdfs:subPropertyOf rdfs:domain rdf:Property .`, each read through the same
  Table 5.2 row.
* `rdfs:subClassOf` by the RDFS axiomatic triple
  `rdfs:subClassOf rdfs:domain rdfs:Class .`, whose truth puts
  `I(rdfs:subClassOf)` into `IP` through the forward direction of Table 5.8's
  `rdfs:domain` row.
* `p1` and `p2` because `onp_typ` demands it of both.

## WHAT THIS WITNESS DOES NOT ESTABLISH, and it is less than it looks

It establishes `not W3CEntails avfPremises (C1, rdfs:subClassOf, C2)`. That is
strictly stronger than the existing Herbrand result, which is about the Lean's
much larger `Conditions` class, and the refuting structure here satisfies
Table 5.8 in both directions, Table 5.6's `allValuesFrom` equality, and the
typing rows of Tables 5.2 and 5.3, none of which any Herbrand witness in this
repository does.

**It is NOT a proof that the triple is not OWL 2 RDF-Based entailed, and nobody
should write that sentence.** Positive transfer runs outward and negative
transfer does not. `W3CModel`'s class is strictly LARGER than the bridge image
of the conforming interpretations, because `W3C` deliberately omits every row no
rule consumes, so a refutation here does not rule out that every genuinely
conforming interpretation satisfies the triple. Concretely, this model violates
at least these rows of RBS Table 5.2, all of which a conforming interpretation
must satisfy:

* `owl:Thing | in IC | = IR`. Here `owl:Thing` denotes `other`, whose class
  extension is empty and is not the carrier.
* `rdf:Property | in IC | = IP`. Here `rdf:Property` also denotes `other`, so
  its class extension is empty rather than the nine-element `IP`.
* `rdfs:Resource | in IC | = IR`, and the RDF and RDFS axiomatic triple tables
  themselves, which are simply absent.

Closing that gap means formalising Table 5.2's forty-odd rows, the axiomatic
triple tables, and the parts of the universe from Table 5.1, and then rebuilding
this model over them. That is a different project, and the honest report is that
this witness gets closer to the specification than anything else here and does
not arrive.

## What it leaves untouched

It does NOT rehabilitate the other non-entailment results.
`Witness.lean`'s `the_old_svf_derivation_is_not_entailed`,
`an_unlisted_individual_is_not_entailed`,
`membership_in_one_member_does_not_give_the_intersection`,
`not_everything_is_entailed`, `Mixed.lean`'s `mix_not_absolutely_entailed`,
`Refute.lean`'s `not_unsat_of_joint_model` and `RefuteWitness.lean`'s
`feed_is_not_refuted` are all discharged by Herbrand or saturated
interpretations, and none of those is a `W3CModel`. The obstruction is recorded
at each of them and at `Semantics.lean`'s safety paragraph.
-/
namespace OOCert

/-! ## The carrier -/

/-- The seventeen elements. `other` absorbs every IRI the model does not need to
tell apart, and its extension and class extension are both empty, which is what
makes every condition over a vocabulary term not named here hold vacuously. -/
inductive LiveD where
  /-- An individual with a `p2`-successor, and the only element outside
  `ICEXT(c2)`. -/
  | alice
  /-- Its `p2`-successor, and the witness that `ICEXT(c2)` is not empty. -/
  | bob
  /-- `C1`, which `avfPremises` makes the universal restriction on `p1`. -/
  | c1
  /-- `C2`, which `avfPremises` makes the universal restriction on `p2`. -/
  | c2
  /-- `Y`, the shared filler, with an EMPTY class extension. -/
  | filler
  /-- `p1`, with an empty property extension. -/
  | p1
  /-- `p2`, with the single pair `(alice, bob)`. -/
  | p2
  /-- `rdf:type`, whose extension IS `ICEXT`. -/
  | ty
  /-- `rdfs:subClassOf`. -/
  | sco
  /-- `rdfs:subPropertyOf`. -/
  | spo
  /-- `rdfs:domain`. -/
  | dm
  /-- `rdfs:range`. -/
  | rg
  /-- `owl:allValuesFrom`. -/
  | avf
  /-- `owl:onProperty`. -/
  | onp
  /-- `rdfs:Class`, whose class extension IS `IC` (Table 5.2, "= IC"). -/
  | cls
  /-- `owl:Restriction`, whose class extension is a PROPER subset of `IC`
  (Table 5.2 writes a subset, never an equality, and this model makes the
  inclusion strict). -/
  | restr
  /-- Every other IRI. -/
  | other
deriving DecidableEq, Repr

namespace LiveD

/-- The carrier as a list, so that quantification over it is decidable without
Mathlib's `Fintype`. -/
def all : List LiveD :=
  [alice, bob, c1, c2, filler, p1, p2, ty, sco, spo, dm, rg, avf, onp, cls, restr, other]

theorem mem_all (w : LiveD) : w ∈ all := by cases w <;> decide

/-- Universal quantification over the carrier is decidable. Every condition
below is settled by `decide` through this instance, so the model is an
executable fact and not a tactic script that might be proving something else. -/
instance decForall (p : LiveD → Prop) [DecidablePred p] : Decidable (∀ w, p w) :=
  decidable_of_iff (∀ w ∈ all, p w) ⟨fun h w => h w (mem_all w), fun h w _ => h w⟩

/-- And so is existential quantification, which `svf_eq` needs on its right-hand
side. -/
instance decExists (p : LiveD → Prop) [DecidablePred p] : Decidable (∃ w, p w) :=
  decidable_of_iff (∃ w ∈ all, p w)
    ⟨fun ⟨w, _, h⟩ => ⟨w, h⟩, fun ⟨w, h⟩ => ⟨w, mem_all w, h⟩⟩

end LiveD

/-! ## The interpretation -/

/-- The denotation table. Everything absent from it denotes `other`, so
`owl:someValuesFrom`, `owl:hasValue`, `owl:equivalentClass`,
`owl:equivalentProperty`, `owl:sameAs`, `owl:inverseOf`,
`owl:SymmetricProperty`, `owl:TransitiveProperty`, `owl:intersectionOf`,
`owl:unionOf`, `owl:oneOf`, `owl:Thing` and `rdf:Property` all land there
together and their conditions hold vacuously. That is a choice about what this
witness is FOR: it exercises Table 5.8 in both directions and Table 5.6's
`allValuesFrom` row, and it says nothing about the rest. The last two of those
IRIs are also where the model stops being a conforming interpretation; see the
module docstring. -/
def liveTable : List (Term × LiveD) :=
  [ (V.type, .ty), (V.subClassOf, .sco), (V.subPropertyOf, .spo),
    (V.domain, .dm), (V.range, .rg),
    (V.allValuesFrom, .avf), (V.onProperty, .onp),
    (V.Class, .cls), (V.Restriction, .restr),
    (tC1, .c1), (tC2, .c2), (tY, .filler), (tp1, .p1), (tp2, .p2) ]

/-- Terms denote their table entry, or `other`. -/
def liveι (t : Term) : LiveD := (List.lookup t liveTable).getD .other

/-- `IP`. The eight elements that carry pairs, plus `p1`, which `onp_typ`
demands.

Every one of them is in `IP` in any conforming interpretation, by RBS Table 5.3
for `owl:allValuesFrom` and `owl:onProperty` and by the RDF and RDFS axiomatic
triples read through Table 5.2's `rdf:Property | = IP` row for the rest; the
citations are in the module docstring. Nothing else is in `IP`, which is what
keeps `sp_bwd`, `dom_bwd` and `rng_bwd` from forcing schema triples about
individuals. -/
def isIP : LiveD → Bool
  | .p1 | .p2 | .ty | .sco | .spo | .dm | .rg | .avf | .onp => true
  | _ => false

/-- The property extensions, as a decidable relation.

Three rows are chosen: `p1` empty, `p2` at `(alice, bob)`, and `ty` at `c1`,
`c2`, `cls` and `restr`. `sco`, `spo`, `dm` and `rg` are the FIXPOINT that
Table 5.8's two directions force from them, and the fixpoint is mutual, because
`spo`, `dm` and `rg` are themselves in `IP` and so appear on both sides of their
own conditions. Nothing here can be adjusted without the build going red. -/
def liveIext : LiveD → LiveD → LiveD → Bool
  -- ICEXT(rdfs:Class) = IC = {C1, C2, Y}. Table 5.2's "= IC" row.
  | .ty, x, .cls => x == .c1 || x == .c2 || x == .filler
  -- ICEXT(owl:Restriction) = {C1, C2}, a PROPER subset of IC. Table 5.2 writes
  -- a subset there and never an equality.
  | .ty, x, .restr => x == .c1 || x == .c2
  -- ICEXT(C1) is everything. Forced: C1 is the universal restriction on p1 and
  -- IEXT(p1) is empty.
  | .ty, _, .c1 => true
  -- ICEXT(C2) is everything but alice. Forced: C2 is the universal restriction
  -- on p2, alice has the p2-successor bob, and bob is not in ICEXT(Y).
  | .ty, x, .c2 => x != .alice
  -- ICEXT of everything else, Y included, is empty.
  | .ty, _, _ => false
  -- IEXT(rdfs:subClassOf): exactly the pairs of IC whose extensions nest.
  -- (C1, C2) is ABSENT, and that absence is the theorem at the end of the file.
  | .sco, u, v =>
      (u == .c1 && v == .c1) || (u == .c2 && (v == .c1 || v == .c2)) ||
      (u == .filler && (v == .c1 || v == .c2 || v == .filler))
  -- IEXT(rdfs:subPropertyOf): exactly the pairs of IP whose extensions nest.
  -- p1's extension is empty so it is below every property; the diagonal; and
  -- the one strict inclusion among the rest, IEXT(rdfs:domain) inside
  -- IEXT(rdfs:range), which holds because every domain pair of this model is
  -- also a range pair. (p2, p1) is ABSENT, and that kind separation is what
  -- keeps scm-avf2 antitone here.
  | .spo, u, v => (u == .p1 && isIP v) || (isIP u && u == v) || (u == .dm && v == .rg)
  -- IEXT(rdfs:domain): every p in IP and c in IC such that every subject of p
  -- lies in ICEXT(c). p1 qualifies everywhere because its extension is empty;
  -- p2 and rdf:type only at C1, because alice is a subject of both and alice is
  -- outside ICEXT(C2); the remaining six qualify at C1 and C2 because their
  -- subjects are classes and properties, never alice.
  | .dm, u, v =>
      (u == .p1 && (v == .c1 || v == .c2 || v == .filler)) ||
      ((u == .avf || u == .dm || u == .onp || u == .rg || u == .sco || u == .spo) &&
        (v == .c1 || v == .c2)) ||
      ((u == .p2 || u == .ty) && v == .c1)
  -- IEXT(rdfs:range): the same with objects for subjects, and it DIFFERS from
  -- the domain table by exactly (p2, C2) and (rdf:type, C2), because the object
  -- bob IS in ICEXT(C2) while the subject alice is not.
  | .rg, u, v =>
      (u == .p1 && (v == .c1 || v == .c2 || v == .filler)) ||
      ((u == .avf || u == .dm || u == .onp || u == .p2 || u == .rg || u == .sco ||
        u == .spo || u == .ty) && (v == .c1 || v == .c2))
  -- The graph's two restrictions.
  | .avf, u, v => (u == .c1 || u == .c2) && v == .filler
  | .onp, u, v => (u == .c1 && v == .p1) || (u == .c2 && v == .p2)
  -- The one asserted individual pair.
  | .p2, u, v => u == .alice && v == .bob
  -- Everything else, `other` and `p1` included, is empty.
  | _, _, _ => false

/-- The interpretation. -/
def live : Interp where
  D := LiveD
  ι := liveι
  iext := fun p x y => liveIext p x y = true

/-- `IP` as a predicate. A parameter of `W3C` and not a field of `Interp`, so
nothing outside this file sees it. -/
def liveIP (x : LiveD) : Prop := isIP x = true

/-- `IP` membership is decidable, which is what lets every condition mentioning
it be settled by `decide` rather than by a tactic script. -/
instance : DecidablePred liveIP := fun x => decidable_of_iff (isIP x = true) Iff.rfl

@[simp] theorem live_iext (p x y : LiveD) : live.iext p x y ↔ liveIext p x y = true := Iff.rfl
@[simp] theorem live_cext (c x : LiveD) : live.cext c x ↔ liveIext .ty x c = true := Iff.rfl
@[simp] theorem live_sc (u v : LiveD) : live.sc u v ↔ liveIext .sco u v = true := Iff.rfl
@[simp] theorem live_sp (u v : LiveD) : live.sp u v ↔ liveIext .spo u v = true := Iff.rfl
@[simp] theorem live_IC (u : LiveD) : live.IC u ↔ liveIext .ty u .cls = true := Iff.rfl

/-! ## The conditions, one decidable fact each

Each lemma is stated over `liveIext` and `liveι` directly, which is what makes
it a closed decidable proposition; `live_w3c` takes each as the corresponding
field by definitional unfolding, so nothing is restated in two places that could
drift apart. -/

theorem live_sc_fwd : ∀ a b : LiveD, liveIext .sco a b = true →
    liveIext .ty a .cls = true ∧ liveIext .ty b .cls = true ∧
    ∀ x, liveIext .ty x a = true → liveIext .ty x b = true := by decide

theorem live_sc_bwd : ∀ a b : LiveD, liveIext .ty a .cls = true → liveIext .ty b .cls = true →
    (∀ x, liveIext .ty x a = true → liveIext .ty x b = true) → liveIext .sco a b = true := by
  decide

theorem live_sp_fwd : ∀ a b : LiveD, liveIext .spo a b = true →
    liveIP a ∧ liveIP b ∧ ∀ x y, liveIext a x y = true → liveIext b x y = true := by decide

theorem live_sp_bwd : ∀ a b : LiveD, liveIP a → liveIP b →
    (∀ x y, liveIext a x y = true → liveIext b x y = true) → liveIext .spo a b = true := by decide

theorem live_dom_fwd : ∀ p c : LiveD, liveIext (liveι V.domain) p c = true →
    liveIP p ∧ liveIext .ty c .cls = true ∧
    ∀ x y, liveIext p x y = true → liveIext .ty x c = true := by decide

theorem live_dom_bwd : ∀ p c : LiveD, liveIP p → liveIext .ty c .cls = true →
    (∀ x y, liveIext p x y = true → liveIext .ty x c = true) →
    liveIext (liveι V.domain) p c = true := by decide

theorem live_rng_fwd : ∀ p c : LiveD, liveIext (liveι V.range) p c = true →
    liveIP p ∧ liveIext .ty c .cls = true ∧
    ∀ x y, liveIext p x y = true → liveIext .ty y c = true := by decide

theorem live_rng_bwd : ∀ p c : LiveD, liveIP p → liveIext .ty c .cls = true →
    (∀ x y, liveIext p x y = true → liveIext .ty y c = true) →
    liveIext (liveι V.range) p c = true := by decide

theorem live_eqc_fwd : ∀ a b : LiveD, liveIext (liveι V.equivalentClass) a b = true →
    liveIext .ty a .cls = true ∧ liveIext .ty b .cls = true ∧
    ∀ x, (liveIext .ty x a = true ↔ liveIext .ty x b = true) := by decide

theorem live_eqp_fwd : ∀ a b : LiveD, liveIext (liveι V.equivalentProperty) a b = true →
    liveIP a ∧ liveIP b ∧ ∀ x y, (liveIext a x y = true ↔ liveIext b x y = true) := by decide

theorem live_same_fwd : ∀ a b : LiveD, liveIext (liveι V.sameAs) a b = true → a = b := by decide

theorem live_inv_fwd : ∀ p q : LiveD, liveIext (liveι V.inverseOf) p q = true →
    liveIP p ∧ liveIP q ∧ ∀ x y, (liveIext p x y = true ↔ liveIext q y x = true) := by decide

theorem live_sym_fwd : ∀ p : LiveD, liveIext .ty p (liveι V.symmetricProperty) = true →
    ∀ x y, liveIext p x y = true → liveIext p y x = true := by decide

theorem live_trp_fwd : ∀ p : LiveD, liveIext .ty p (liveι V.transitiveProperty) = true →
    ∀ x y z, liveIext p x y = true → liveIext p y z = true → liveIext p x z = true := by decide

theorem live_svf_eq : ∀ z c p : LiveD, liveIext (liveι V.someValuesFrom) z c = true →
    liveIext (liveι V.onProperty) z p = true →
    ∀ x, (liveIext .ty x z = true ↔ ∃ y, liveIext p x y = true ∧ liveIext .ty y c = true) := by
  decide

theorem live_avf_eq : ∀ z c p : LiveD, liveIext (liveι V.allValuesFrom) z c = true →
    liveIext (liveι V.onProperty) z p = true →
    ∀ x, (liveIext .ty x z = true ↔ ∀ y, liveIext p x y = true → liveIext .ty y c = true) := by
  decide

theorem live_hv_eq : ∀ z a p : LiveD, liveIext (liveι V.hasValue) z a = true →
    liveIext (liveι V.onProperty) z p = true →
    ∀ x, (liveIext .ty x z = true ↔ liveIext p x a = true) := by decide

theorem live_restr_IC : ∀ x : LiveD, liveIext .ty x (liveι V.Restriction) = true →
    liveIext .ty x .cls = true := by decide

theorem live_svf_typ : ∀ z c : LiveD, liveIext (liveι V.someValuesFrom) z c = true →
    liveIext .ty z (liveι V.Restriction) = true ∧ liveIext .ty c .cls = true := by decide

theorem live_avf_typ : ∀ z c : LiveD, liveIext (liveι V.allValuesFrom) z c = true →
    liveIext .ty z (liveι V.Restriction) = true ∧ liveIext .ty c .cls = true := by decide

theorem live_onp_typ : ∀ z p : LiveD, liveIext (liveι V.onProperty) z p = true →
    liveIext .ty z (liveι V.Restriction) = true ∧ liveIP p := by decide

/-- Every asserted triple of `avfPremises` holds. -/
theorem live_facts : ∀ t ∈ avfPremises, liveIext (liveι t.p) (liveι t.s) (liveι t.o) = true := by
  decide

/-- The conditions, assembled. Each field is the decidable fact above, taken by
definitional unfolding of `Interp.sc`, `Interp.sp`, `Interp.cext` and
`Interp.IC`. -/
theorem live_w3c : W3C live liveIP where
  sc_fwd := live_sc_fwd
  sc_bwd := live_sc_bwd
  sp_fwd := live_sp_fwd
  sp_bwd := live_sp_bwd
  dom_fwd := live_dom_fwd
  dom_bwd := live_dom_bwd
  rng_fwd := live_rng_fwd
  rng_bwd := live_rng_bwd
  eqc_fwd := live_eqc_fwd
  eqp_fwd := live_eqp_fwd
  same_fwd := live_same_fwd
  inv_fwd := live_inv_fwd
  sym_fwd := live_sym_fwd
  trp_fwd := live_trp_fwd
  svf_eq := live_svf_eq
  avf_eq := live_avf_eq
  hv_eq := live_hv_eq
  restr_IC := live_restr_IC
  svf_typ := live_svf_typ
  avf_typ := live_avf_typ
  onp_typ := live_onp_typ

/-- **A conforming model of `avfPremises`.** The three list fields are vacuous
because `avfPremises` carries no `owl:intersectionOf`, `owl:unionOf` or
`owl:oneOf` triple; the model says nothing about those rows and does not pretend
to. -/
theorem live_is_a_w3c_model : W3CModel live liveIP avfPremises where
  conds := live_w3c
  facts := live_facts
  int_eq := fun c l _ hc =>
    absurd hc (not_mem_pred avfPremises V.intersectionOf (by decide) c l)
  uni_eq := fun c l _ hc => absurd hc (not_mem_pred avfPremises V.unionOf (by decide) c l)
  oneOf_eq := fun c l _ hc => absurd hc (not_mem_pred avfPremises V.oneOf (by decide) c l)

/-! ## Non-vacuity, compiled into the build

The facts the model exists to carry, in one theorem, so that a later edit that
hollows the model out fails here instead of passing quietly. Everything above
would still compile with an empty carrier and every relation false; this is what
stops that from being reported as a result.

Each is stated twice: once over `liveIext` and `liveι`, where it is a closed
decidable proposition, and once over `live`, where it is the sentence a reader
wants. The second is the first by definitional unfolding, so the two cannot
drift. -/

theorem live_is_live_raw :
    (liveIext .ty .c1 .cls = true ∧ liveIext .ty .c2 .cls = true ∧
        liveIext .ty .filler .cls = true) ∧
      (¬ liveIext .ty .restr .cls = true ∧ ¬ liveIext .ty .alice .cls = true) ∧
    (∀ x, liveIext .ty x .c1 = true) ∧
      (∀ x, liveIext .ty x .c2 = true → liveIext .ty x .c1 = true) ∧
      (liveIext .ty .alice .c1 = true ∧ ¬ liveIext .ty .alice .c2 = true ∧
        liveIext .ty .bob .c2 = true) ∧
    (∀ x, ¬ liveIext .ty x .filler = true) ∧
    (liveIext .ty .c1 (liveι V.Restriction) = true ∧
      ¬ liveIext .ty .filler (liveι V.Restriction) = true) ∧
    (∀ x y, ¬ liveIext .p1 x y = true) ∧ liveIext .p2 .alice .bob = true := by decide

/-- **The liveness gate.** `IC` has three members and does not swallow the
carrier; one class extension is the whole carrier; another is a proper subset of
it, witnessed on both sides; a third is empty; `ICEXT(owl:Restriction)` is a
proper subset of `IC`; and the one property that matters has a pair in it. -/
theorem live_is_live :
    (live.IC .c1 ∧ live.IC .c2 ∧ live.IC .filler) ∧ (¬ live.IC .restr ∧ ¬ live.IC .alice) ∧
    (∀ x, live.cext .c1 x) ∧ (∀ x, live.cext .c2 x → live.cext .c1 x) ∧
      (live.cext .c1 .alice ∧ ¬ live.cext .c2 .alice ∧ live.cext .c2 .bob) ∧
    (∀ x, ¬ live.cext .filler x) ∧
    (live.cext (live.ι V.Restriction) .c1 ∧ ¬ live.cext (live.ι V.Restriction) .filler) ∧
    (∀ x y, ¬ live.iext .p1 x y) ∧ live.iext .p2 .alice .bob :=
  live_is_live_raw

theorem live_is_bridge_coherent_raw :
    ∀ p x y : LiveD, liveIext p x y = true → liveIP p := by decide

/-- **The bridge shape, checked.** Every predicate with a pair in its extension
is in `IP`.

This is what makes the refutation at the end of the file worth more than the
Herbrand one it replaces. `W3C.lean`'s bridge reads a conforming interpretation
into an `Interp` by `iext p x y := IP p and (x, y) in IEXT p`, so a structure
with a pair under a predicate outside `IP` is not the image of any conforming
interpretation and cannot honestly refute anything about them. `W3C` does not
impose this, because no arm consumes it and imposing it would shrink the model
class for nothing; the witness satisfies it anyway, and says so here. -/
theorem live_is_bridge_coherent : ∀ p x y : LiveD, live.iext p x y → liveIP p :=
  live_is_bridge_coherent_raw

theorem live_c1_is_a_class : liveIext .ty .c1 .cls = true := by decide
theorem live_c2_is_a_class : liveIext .ty .c2 .cls = true := by decide
theorem live_p2_is_in_IP : liveIP .p2 := by decide

/-- The universally quantified clause `dom_bwd` demands, at `c1`, discharged
over the pair `(alice, bob)` and NOT by there being no pairs. -/
theorem live_p2_subjects_are_c1 :
    ∀ x y : LiveD, liveIext .p2 x y = true → liveIext .ty x .c1 = true := by decide

/-- The same clause for `rng_bwd`, at `c2`. `alice` is outside `ICEXT(c2)` and
`bob` is inside it, which is what makes the domain and range extensions
differ. -/
theorem live_p2_objects_are_c2 :
    ∀ x y : LiveD, liveIext .p2 x y = true → liveIext .ty y .c2 = true := by decide

theorem live_p2_is_not_a_domain_of_c2 : ¬ liveIext (liveι V.domain) .p2 .c2 = true := by decide

/-- `dom_bwd` is discharged over a NON-EMPTY relation: the clause it demands is
proved at `(alice, bob)` and not by there being no pairs, which is the thing the
second kernel's own witness fails to do for this condition. -/
theorem live_dom_bwd_is_exercised : live.iext (live.ι V.domain) .p2 .c1 :=
  live_w3c.dom_bwd .p2 .c1 live_p2_is_in_IP live_c1_is_a_class live_p2_subjects_are_c1

/-- `rng_bwd`, likewise, and at a class `dom_bwd` does NOT reach. The two
backward halves of Table 5.8 are separated by this model rather than satisfied
together by accident: `(p2, C2)` is in the range extension and not in the domain
extension, because `bob` is in `ICEXT(C2)` and `alice` is not. -/
theorem live_rng_bwd_is_exercised :
    live.iext (live.ι V.range) .p2 .c2 ∧ ¬ live.iext (live.ι V.domain) .p2 .c2 :=
  ⟨live_w3c.rng_bwd .p2 .c2 live_p2_is_in_IP live_c2_is_a_class live_p2_objects_are_c2,
   live_p2_is_not_a_domain_of_c2⟩

/-! ## What it refutes, and what it confirms -/

/-- **The direction the W3C table gives, over this model class.** `scm-avf2`
concludes `C2 rdfs:subClassOf C1`, and that is true in every `W3CModel` of these
premises. Transferred from the existing result rather than reproved, which is
the whole point of `W3CEntails.of_entails`. -/
theorem the_avf2_direction_the_table_gives_is_w3c_entailed :
    W3CEntails avfPremises ⟨tC2, V.subClassOf, tC1⟩ :=
  W3CEntails.of_entails the_avf2_direction_the_table_gives_is_entailed

theorem live_refutes_the_natural_direction :
    ¬ liveIext (liveι V.subClassOf) (liveι tC1) (liveι tC2) = true := by decide

/-- **And the natural-looking direction is refuted by a bridge-coherent
interpretation.**

`Witness.lean`'s `the_natural_avf2_direction_is_not_entailed` refutes the same
triple with a Herbrand interpretation, which satisfies `Conditions` and is not a
`W3CModel`: `avfWitness` contains no `rdf:type` triple at all, so `IC` is empty
there, `avf_typ` and `onp_typ` fail outright for want of an `owl:Restriction`
typing, and if those were patched in then `sp_bwd` would force `(p2, p1)` into
`rdfs:subPropertyOf`, a triple that witness does not contain. That result is
therefore about the Lean's larger `Conditions` class only.

This one is about a class much closer to the specification's: the refuting
structure satisfies Table 5.8 in both directions, Table 5.6's `allValuesFrom`
equality, Tables 5.9, 5.12 and 5.13, and the typing rows of Tables 5.2 and 5.3,
and it is bridge-coherent. A rule concluding `C1 rdfs:subClassOf C2` from these
premises, which is what copying the shape of `scm-avf1`, `scm-svf1` and
`scm-svf2` gives, would be making a claim that such a structure refutes.

**Read the module docstring before quoting this anywhere.** It is NOT a proof
that the triple fails to be OWL 2 RDF-Based entailed: `W3CModel`'s class is
larger than the conforming interpretations, because `W3C` omits every row no
rule consumes, and this model violates Table 5.2's `owl:Thing | = IR` and
`rdf:Property | = IP` rows among others. -/
theorem the_natural_avf2_direction_is_not_w3c_entailed :
    ¬ W3CEntails avfPremises ⟨tC1, V.subClassOf, tC2⟩ := fun h =>
  absurd (h live liveIP live_is_a_w3c_model) live_refutes_the_natural_direction

/-- The pair, stated together: the rule's own conclusion holds in every
`W3CModel` and the reversed one fails in this one. A checker that had `scm-avf2`
the natural way round would be accepting certificates whose conclusions this
structure makes false, and that is now a machine-checked sentence rather than an
argument in a docstring. -/
theorem scm_avf2_runs_one_way_under_the_specification :
    W3CEntails avfPremises ⟨tC2, V.subClassOf, tC1⟩ ∧
      ¬ W3CEntails avfPremises ⟨tC1, V.subClassOf, tC2⟩ :=
  ⟨the_avf2_direction_the_table_gives_is_w3c_entailed,
   the_natural_avf2_direction_is_not_w3c_entailed⟩

/-! ## And `W3CEntails` is not everything either

`live` closes one vacuity hole: `W3C` has a non-degenerate model, so
`W3CModel.toModel` is not a theorem about an empty class. The other hole is that
`W3CEntails` could hold of every triple, which would make
`certificate_w3c_sound` say nothing at all. It does not, and the cheapest
witness closes it: over the EMPTY graph every antecedent in `W3C` is false, and
`IP := fun _ => False` makes the four backward conditions vacuous too. -/

/-- The Herbrand interpretation of the empty graph is a conforming model of it,
with an empty `IP`. Bridge-coherent for free: `iext` is empty, so nothing has to
be in `IP`. -/
theorem empty_herbrand_is_a_w3c_model : W3CModel (herbrand []) (fun _ => False) [] where
  conds :=
    { sc_fwd := fun a b hab => absurd hab (not_mem_pred [] V.subClassOf (by simp) a b)
      sc_bwd := fun a b ha => absurd ha (not_typed [] V.Class (by simp) a)
      sp_fwd := fun a b hab => absurd hab (not_mem_pred [] V.subPropertyOf (by simp) a b)
      sp_bwd := fun _ _ h => absurd h (fun x => x)
      dom_fwd := fun p c hpc => absurd hpc (not_mem_pred [] V.domain (by simp) p c)
      dom_bwd := fun _ _ h => absurd h (fun x => x)
      rng_fwd := fun p c hpc => absurd hpc (not_mem_pred [] V.range (by simp) p c)
      rng_bwd := fun _ _ h => absurd h (fun x => x)
      eqc_fwd := fun a b hab => absurd hab (not_mem_pred [] V.equivalentClass (by simp) a b)
      eqp_fwd := fun a b hab => absurd hab (not_mem_pred [] V.equivalentProperty (by simp) a b)
      same_fwd := fun a b hab => absurd hab (not_mem_pred [] V.sameAs (by simp) a b)
      inv_fwd := fun p q hpq => absurd hpq (not_mem_pred [] V.inverseOf (by simp) p q)
      sym_fwd := fun p hp => absurd hp (not_typed [] V.symmetricProperty (by simp) p)
      trp_fwd := fun p hp => absurd hp (not_typed [] V.transitiveProperty (by simp) p)
      svf_eq := fun z c _ h => absurd h (not_mem_pred [] V.someValuesFrom (by simp) z c)
      avf_eq := fun z c _ h => absurd h (not_mem_pred [] V.allValuesFrom (by simp) z c)
      hv_eq := fun z a _ h => absurd h (not_mem_pred [] V.hasValue (by simp) z a)
      restr_IC := fun x hx => absurd hx (not_typed [] V.Restriction (by simp) x)
      svf_typ := fun z c h => absurd h (not_mem_pred [] V.someValuesFrom (by simp) z c)
      avf_typ := fun z c h => absurd h (not_mem_pred [] V.allValuesFrom (by simp) z c)
      onp_typ := fun z p h => absurd h (not_mem_pred [] V.onProperty (by simp) z p) }
  facts := by intro t ht; simp at ht
  int_eq := by intro c l _ hc; exact absurd hc (not_mem_pred [] V.intersectionOf (by simp) c l)
  uni_eq := by intro c l _ hc; exact absurd hc (not_mem_pred [] V.unionOf (by simp) c l)
  oneOf_eq := by intro c l _ hc; exact absurd hc (not_mem_pred [] V.oneOf (by simp) c l)

/-- **`W3CEntails` is not trivial**, so `certificate_w3c_sound` is not a theorem
about a relation that holds of everything. This is obligation (2) of
`Witness.lean`'s own header, restated over the conforming model class, and it is
the one obligation there that transfers without a new hand-built structure. -/
theorem not_everything_is_w3c_entailed :
    ¬ W3CEntails [] ⟨"<http://ex.org/a>", "<http://ex.org/b>", "<http://ex.org/c>"⟩ := by
  intro h
  have hs := h (herbrand []) (fun _ => False) empty_herbrand_is_a_w3c_model
  simp at hs

/-! ## Axioms, pinned

A `sorry` or a `native_decide` here would restore the vacuity objection this
file exists to close, and `native_decide` would add `Lean.ofReduceBool` to every
footprint below. -/

/-- info: 'OOCert.live_is_a_w3c_model' depends on axioms: [propext] -/
#guard_msgs in
#print axioms live_is_a_w3c_model

/-- info: 'OOCert.live_is_live' depends on axioms: [propext] -/
#guard_msgs in
#print axioms live_is_live

/-- info: 'OOCert.live_is_bridge_coherent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms live_is_bridge_coherent

/-- info: 'OOCert.live_dom_bwd_is_exercised' depends on axioms: [propext] -/
#guard_msgs in
#print axioms live_dom_bwd_is_exercised

/-- info: 'OOCert.live_rng_bwd_is_exercised' depends on axioms: [propext] -/
#guard_msgs in
#print axioms live_rng_bwd_is_exercised

/-- info: 'OOCert.scm_avf2_runs_one_way_under_the_specification' depends on axioms: [propext] -/
#guard_msgs in
#print axioms scm_avf2_runs_one_way_under_the_specification

/-- info: 'OOCert.not_everything_is_w3c_entailed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_everything_is_w3c_entailed

end OOCert
