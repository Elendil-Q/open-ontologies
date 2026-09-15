import OOCert.W3C
import OOCert.Witness

/-!
# A LIVE `W3CModel`, and the non-entailments that are about the specification

`W3C.lean` derives fourteen arms from quoted specification cells. That result is
worth nothing until something exhibits a `W3CModel`, and it is worth very little
if the thing that exhibits one is degenerate. This file builds a model that is
not, and it collects every non-entailment in the repository that is about the
`W3CModel` class rather than about `Semantics.lean`'s weaker `Conditions`.

## Why `saturated` is not enough

`Witness.lean`'s `saturated` (domain `Unit`, every relation total) satisfies
`W3C` with `IP := fun _ => True`: every field holds because both sides of every
equality are all of `Unit`. So bare satisfiability of `W3C` is one theorem and
it says nothing, because such a model distinguishes no condition from any other
and refutes nothing. `W3CModel.toModel` proved over an unsatisfiable or a
degenerate `W3C` would be a theorem about nothing that LOOKED better than the
assumption it replaced, which is a strictly worse defect than the one being
repaired. The gate is therefore a NON-DEGENERATE model, and `live_is_live`,
`live_exercises_every_arm` and `live_leaves_exactly_these_five_vacuous` below
compile the liveness facts, their limits and the exact list of exceptions into
the build, so that the next person to shorten this graph to fix a `decide`
timeout breaks it rather than hollowing it out silently.

## The first version of this file was vacuous where it mattered most, and this is the repair

`live` had seventeen elements, `IEXT(p1)` was EMPTY and `ICEXT(Y)` was EMPTY,
and both emptinesses were written into the liveness gate as though they were
features of the model rather than holes in it. Two consequences, in ascending
order of seriousness.

Nine of the twenty-one fields of `W3C` held because nothing was in the extension
their antecedent reads, and SIX of the fourteen arms rested entirely on those
nine: `scm-eqc1` and `scm-eqp1` with two conclusions each, on `eqc_fwd` and
`eqp_fwd`; `scm-svf1` and `scm-svf2`, on `svf_eq` and `svf_typ`.
`owl:equivalentClass`, `owl:equivalentProperty`, `owl:someValuesFrom`,
`owl:hasValue`, `owl:sameAs`, `owl:inverseOf`, `owl:SymmetricProperty` and
`owl:TransitiveProperty` all denoted the same junk element, whose extensions were
empty.

Worse, the refutation the file exists to deliver was vacuous at its own
load-bearing premise. `avfPremises` asserts `p1 rdfs:subPropertyOf p2`, and in a
model with `IEXT(p1)` empty that triple holds because `sp_bwd`'s inclusion clause
has nothing to check. A refutation whose premise is satisfied for want of
anything to test establishes almost nothing, and the emptiness of `IEXT(p1)` was
a conjunct of `live_is_live`, which is the theorem whose job is to catch exactly
that.

The model below is the repair. `carl` is a third individual: `IEXT(p1)` is
`{(alice, carl)}` and `ICEXT(Y)` is `{carl}`, so `IEXT(p1)` is non-empty and a
PROPER subset of `IEXT(p2)`, and `p1 rdfs:subPropertyOf p2` holds here for a
reason. `A2`, `S1`, `S2`, `S3` and `q` are five further elements carrying the
`owl:allValuesFrom`, `owl:someValuesFrom`, `owl:equivalentClass` and
`owl:equivalentProperty` configurations that the six dead arms need.
`live_exercises_every_arm` applies all fourteen derivations at concrete instances
of this model, which is a strictly stronger gate than any field being non-empty.

## What is still vacuous, and it is exactly the fields that carry no arm

Five of the twenty-one fields still hold because nothing is in the extension
their antecedent reads: `same_fwd`, `sym_fwd`, `trp_fwd`, `inv_fwd` and `hv_eq`.
`live_leaves_exactly_these_five_vacuous` is that list as a theorem, so that it
cannot drift from the tables. None of the five carries any of the fourteen arms:
`Soundness.lean` takes all five out of `Conditions` by projection.

`same_fwd` cannot be exercised non-trivially by ANY model, and that is the
specification's doing. RBS reads `(a₁, a₂) ∈ IEXT(I(owl:sameAs))` **iff**
`a₁ = a₂`, so the only pairs a conforming interpretation may put there are
diagonal and the only instance of the field is `a = a`. The other four are
ordinary omissions that could be closed and are not: each needs its own
vocabulary element plus a property or a restriction to hold it, and every
condition here is quantified over the carrier three or four times, so the
`decide` cost grows as the fourth power of the carrier. Twenty-six elements
already cost about thirty seconds. The honest report is that these four are not
exercised, not that they cannot be.

## The model

Carrier: three individuals `alice`, `bob` and `carl`; seven classes, of which
six are restrictions; three properties; twelve vocabulary denotations that have
to be told apart; and one junk element `other` absorbing every remaining IRI.
Twenty-six elements.

ELEVEN rows are chosen and the conditions determine the other ten.

* `IEXT(p1) = IEXT(q) := {(alice, carl)}`, `IEXT(p2) := {(alice, bob),
  (alice, carl)}`, `ICEXT(Y) := {carl}`.
* `owl:allValuesFrom` puts `C1 = ∀p1.Y`, `C2 = ∀p2.Y` and `A2 = ∀p2.C1`;
  `owl:someValuesFrom` puts `S1 = ∃p2.Y`, `S2 = ∃p2.C1` and `S3 = ∃p1.Y`;
  `owl:equivalentClass` relates `S1` and `S2`, whose class extensions are equal;
  `owl:equivalentProperty` relates `p1` and `q`, whose property extensions are
  equal.
* `avf_eq` then forces `ICEXT(C1)` to be the whole carrier, because `alice`'s
  only `p1`-successor is `carl` and `carl` IS in `ICEXT(Y)`, and `ICEXT(C2)` to
  be the carrier minus `alice`, because `alice` also has the `p2`-successor `bob`
  and `bob` is not.
* So `ICEXT(C1)` is not contained in `ICEXT(C2)`, and `sc_fwd` makes
  `(C1, C2)` in `IEXT(rdfs:subClassOf)` IMPOSSIBLE. That is the refutation.
* And `ICEXT(C2)` IS contained in `ICEXT(C1)`, so `sc_bwd` FORCES
  `(C2, C1)` into `IEXT(rdfs:subClassOf)`, which is what `scm-avf2` draws. The
  witness confirms both halves of the pair, where the Herbrand witness in
  `Witness.lean` asserts one and leaves the other out by hand.
* `svf_eq` forces `ICEXT(S1) = ICEXT(S2) = ICEXT(S3) = {alice}`.
* `IC := {C1, C2, A2, Y, S1, S2, S3}` through `ICEXT(rdfs:Class)`, and
  `ICEXT(owl:Restriction)` is the six restrictions, a PROPER subset of `IC`
  per Table 5.2, because `Y` is a class and not a restriction.
  `owl:Restriction` itself is kept out of `IC`, so `sc_bwd` raises no obligation
  about it.
* `sc_bwd`, `sp_bwd`, `dom_bwd` and `rng_bwd` then force the whole of
  `IEXT(rdfs:subClassOf)`, `IEXT(rdfs:subPropertyOf)`, `IEXT(rdfs:domain)` and
  `IEXT(rdfs:range)`, and the last three are a FIXPOINT rather than a free
  choice: each is defined in terms of the others, because `rdfs:subPropertyOf`,
  `rdfs:domain` and `rdfs:range` are themselves members of `IP` and so are
  subject to the very conditions they carry. The tables below are that fixpoint.
  `(p2, p1)` is NOT in `IEXT(rdfs:subPropertyOf)`, because `IEXT(p2)` is not
  contained in `IEXT(p1)`, and the domain and range tables DIFFER, at the rows
  for `p1`, `q`, `p2` and `rdf:type`, which is the model separating the two rows
  of Table 5.8 rather than satisfying them both by accident.
  `live_rng_bwd_is_exercised` pins one such separation, `(p2, C2)`, as a
  theorem: it is in the range extension and not in the domain extension.

The fixpoint is why several entries look strange at first reading.
`rdfs:domain` has `rdfs:subClassOf` in its subject position, for instance. That
is forced, not chosen: `rdfs:subClassOf` is in `IP`, `C1` is in `IC`, every
subject of `IEXT(rdfs:subClassOf)` lies in `ICEXT(C1)` because `ICEXT(C1)` is
everything, and Table 5.8's `rdfs:domain` row is an `iff`. RDF has no sortal
separation, and this is what that costs.

## `IP`, and why these thirteen

`IP` must contain every element with a non-empty extension, or the structure is
not the image of any conforming interpretation under the bridge in `W3C.lean`
(there, `iext p x y := IP p and (x, y) in IEXT p`, so a pair in an extension
implies its predicate is in `IP`). `live_is_bridge_coherent` checks that below.
It is a property of THIS model and NOT a field of `W3CModel`, which is a
distinction an earlier draft of this file lost, at some cost; see the section on
the three transferred non-entailments below.

The thirteen are `p1`, `p2`, `q` and the ten vocabulary denotations that carry
pairs, and every one of them is in `IP` in any conforming interpretation:

* `owl:allValuesFrom`, `owl:someValuesFrom`, `owl:onProperty`,
  `owl:equivalentClass` and `owl:equivalentProperty` by RBS Table 5.3 directly,
  whose second column reads "∈ IP" for all five. The same table's third column
  gives `IEXT(I(owl:equivalentClass)) ⊆ IC × IC` and
  `IEXT(I(owl:equivalentProperty)) ⊆ IP × IP`, which this model also satisfies
  and which `W3C` does not state, because `eqc_fwd` and `eqp_fwd` get those
  memberships from Table 5.9 instead.
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
* `p1`, `p2` and `q` because `onp_typ` demands it of the first two and
  `eqp_fwd` of the third.

All five axiomatic triples were re-read in the raw HTML of
<https://www.w3.org/TR/rdf11-mt/> on 15 September 2026; they are the same five
the bridge in `W3C.lean` needs, and that file now lists them as the assumption
they are.

## WHAT THIS WITNESS DOES NOT ESTABLISH, and it is less than it looks

It establishes `not W3CEntails avfPremises (C1, rdfs:subClassOf, C2)`. That is
strictly stronger than the existing Herbrand result, which is about the Lean's
much larger `Conditions` class, and the refuting structure here satisfies
Table 5.8 in both directions, Table 5.6's `someValuesFrom` and `allValuesFrom`
equalities, Table 5.9's two rows, and the typing rows of Tables 5.2 and 5.3,
none of which the Herbrand witness in `Witness.lean` does.

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
  its class extension is empty rather than the thirteen-element `IP`.
* `rdfs:Resource | in IC | = IR`, and the RDF and RDFS axiomatic triple tables
  themselves, which are simply absent.

Closing that gap means formalising Table 5.2's forty-odd rows, the axiomatic
triple tables, and the parts of the universe from Table 5.1, and then rebuilding
this model over them. That is a different project, and the honest report is that
this witness gets closer to the specification than anything else here and does
not arrive.

## What it leaves untouched, corrected

An earlier version of this section said that this file "does NOT rehabilitate
the other non-entailment results", and listed seven, on the ground that all of
them "are discharged by Herbrand or saturated interpretations, and none of those
is a `W3CModel`". That is false, it was false of one of the seven at the moment
it was written, and the reason given for it was inverted. Four of the seven are
`W3CModel`s with their witness graphs unchanged. `not_everything_is_w3c_entailed`
was the one already proved below while the list called it open; the section after
it proves two more; `Mixed.lean` proves the fourth. The three that do not
transfer carry the field that fails, checked by `decide` rather than asserted.
-/
namespace OOCert

/-! ## The carrier -/

/-- The twenty-six elements. `other` absorbs every IRI the model does not need to
tell apart, and its extension and class extension are both empty, which is what
makes every condition over a vocabulary term not named here hold vacuously. The
five terms that stay in `other` are listed, with what it costs, under "What is
still vacuous" in the module docstring. -/
inductive LiveD where
  /-- An individual with a `p1`-successor and two `p2`-successors, and the only
  element outside `ICEXT(C2)`. -/
  | alice
  /-- A `p2`-successor of `alice` that is NOT in `ICEXT(Y)`, which is what puts
  `alice` outside `ICEXT(C2)` and makes the refutation work. -/
  | bob
  /-- A `p1`-successor of `alice` that IS in `ICEXT(Y)`. `carl` is the element
  the 15 September 2026 rebuild added: without it `IEXT(p1)` is empty, the
  premise `p1 rdfs:subPropertyOf p2` holds only because there is nothing to
  check, and `ICEXT(Y)` is empty as well. -/
  | carl
  /-- `C1`, the universal restriction `∀p1.Y` that `avfPremises` asserts. -/
  | c1
  /-- `C2`, the universal restriction `∀p2.Y`. -/
  | c2
  /-- `A2`, a second universal restriction on `p2`, with filler `C1`. It exists
  so that `scm-avf1` has two `owl:allValuesFrom` restrictions sharing a property
  to order; nothing in `avfPremises` mentions it. -/
  | a2
  /-- `Y`, the shared filler. `ICEXT(Y) = {carl}`, NOT empty. -/
  | filler
  /-- `S1`, the existential restriction `∃p2.Y`. -/
  | s1
  /-- `S2`, the existential restriction `∃p2.C1`. `S1` and `S2` order under
  `scm-svf1` because `Y` is below `C1`. -/
  | s2
  /-- `S3`, the existential restriction `∃p1.Y`. `S3` and `S1` order under
  `scm-svf2` because `p1` is below `p2`. -/
  | s3
  /-- `p1`, with the single pair `(alice, carl)`. -/
  | p1
  /-- `p2`, with `(alice, bob)` and `(alice, carl)`, so `IEXT(p1)` is a PROPER
  subset of `IEXT(p2)`. -/
  | p2
  /-- A second property with `IEXT(q) = IEXT(p1)`, exactly so that
  `owl:equivalentProperty` has a pair to relate. -/
  | q
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
  /-- `owl:someValuesFrom`. -/
  | svf
  /-- `owl:onProperty`. -/
  | onp
  /-- `owl:equivalentClass`. -/
  | eqc
  /-- `owl:equivalentProperty`. -/
  | eqp
  /-- `rdfs:Class`, whose class extension IS `IC` (Table 5.2, "= IC"). -/
  | cls
  /-- `owl:Restriction`, whose class extension is a PROPER subset of `IC`
  (Table 5.2 writes a subset, never an equality, and this model makes the
  inclusion strict: `Y` is a class and not a restriction). -/
  | restr
  /-- Every other IRI. -/
  | other
deriving DecidableEq, Repr

namespace LiveD

/-- The carrier as a list, so that quantification over it is decidable without
Mathlib's `Fintype`. -/
def all : List LiveD :=
  [alice, bob, carl, c1, c2, a2, filler, s1, s2, s3, p1, p2, q,
   ty, sco, spo, dm, rg, avf, svf, onp, eqc, eqp, cls, restr, other]

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
`owl:hasValue`, `owl:sameAs`, `owl:inverseOf`, `owl:SymmetricProperty`,
`owl:TransitiveProperty`, `owl:intersectionOf`, `owl:unionOf`, `owl:oneOf`,
`owl:Thing` and `rdf:Property` all land there together and their conditions hold
vacuously. The first five of those are the fields this witness does not
exercise, and `live_leaves_exactly_these_five_vacuous` pins that list so it
cannot drift; the last five are where the model stops being a conforming
interpretation, and the module docstring says so. -/
def liveTable : List (Term × LiveD) :=
  [ (V.type, .ty), (V.subClassOf, .sco), (V.subPropertyOf, .spo),
    (V.domain, .dm), (V.range, .rg),
    (V.allValuesFrom, .avf), (V.someValuesFrom, .svf), (V.onProperty, .onp),
    (V.equivalentClass, .eqc), (V.equivalentProperty, .eqp),
    (V.Class, .cls), (V.Restriction, .restr),
    (tC1, .c1), (tC2, .c2), (tY, .filler), (tp1, .p1), (tp2, .p2) ]

/-- Terms denote their table entry, or `other`. -/
def liveι (t : Term) : LiveD := (List.lookup t liveTable).getD .other

/-- `IP`. The thirteen elements that carry pairs.

Every one of them is in `IP` in any conforming interpretation, by RBS Table 5.3
for `owl:allValuesFrom`, `owl:someValuesFrom` and `owl:onProperty`, by Table 5.9
for `owl:equivalentClass` and `owl:equivalentProperty`, and by the RDF and RDFS
axiomatic triples read through Table 5.2's `rdf:Property | = IP` row for the
rest; the citations are in the module docstring. Nothing else is in `IP`, which
is what keeps `sp_bwd`, `dom_bwd` and `rng_bwd` from forcing schema triples about
individuals. -/
def isIP : LiveD → Bool
  | .p1 | .p2 | .q | .ty | .sco | .spo | .dm | .rg
  | .avf | .svf | .onp | .eqc | .eqp => true
  | _ => false

/-- The property extensions, as a decidable relation.

ELEVEN rows are chosen: `IEXT(p1)`, `IEXT(q)`, `IEXT(p2)`, `ICEXT(Y)`, the five
constructor tables `owl:allValuesFrom`, `owl:someValuesFrom`, `owl:onProperty`,
`owl:equivalentClass` and `owl:equivalentProperty`, and the two class extensions
`ICEXT(rdfs:Class)` and `ICEXT(owl:Restriction)` that say which elements are
classes and which are restrictions. The other TEN are determined. The class
extensions of `C1`, `C2`, `A2`, `S1`, `S2` and `S3` are FORCED by Table 5.6, and
`sco`, `spo`, `dm` and `rg` are the FIXPOINT that Table 5.8's two directions
force from all of it. The fixpoint is
mutual, because `sco`, `spo`, `dm` and `rg` are themselves in `IP` or `IC` and so
appear on both sides of their own conditions. Nothing here can be adjusted
without the build going red. -/
def liveIext : LiveD → LiveD → LiveD → Bool
  -- ICEXT(rdfs:Class) = IC = {C1, C2, A2, Y, S1, S2, S3}. Table 5.2's "= IC" row.
  | .ty, x, .cls =>
      x == .c1 || x == .c2 || x == .a2 || x == .filler || x == .s1 || x == .s2 || x == .s3
  -- ICEXT(owl:Restriction) = the six restrictions, a PROPER subset of IC: Y is a
  -- class and not a restriction. Table 5.2 writes a subset there, never an equality.
  | .ty, x, .restr =>
      x == .c1 || x == .c2 || x == .a2 || x == .s1 || x == .s2 || x == .s3
  -- ICEXT(C1) is everything. FORCED: C1 is ∀p1.Y, IEXT(p1) = {(alice, carl)} and
  -- carl IS in ICEXT(Y), so alice qualifies and nothing else has a p1-successor.
  | .ty, _, .c1 => true
  -- ICEXT(A2) is everything. FORCED: A2 is ∀p2.C1 and ICEXT(C1) is everything.
  | .ty, _, .a2 => true
  -- ICEXT(C2) is everything but alice. FORCED: C2 is ∀p2.Y and alice has the
  -- p2-successor bob, which is not in ICEXT(Y).
  | .ty, x, .c2 => x != .alice
  -- ICEXT(Y) = {carl}. NOT EMPTY, which is what makes alice's membership of
  -- ICEXT(C1) a real check rather than an empty one.
  | .ty, x, .filler => x == .carl
  -- ICEXT(S1) = ICEXT(S2) = ICEXT(S3) = {alice}. FORCED by Table 5.6's
  -- someValuesFrom row: alice reaches carl by p1 and by p2, carl is in ICEXT(Y),
  -- and ICEXT(C1) is everything.
  | .ty, x, .s1 => x == .alice
  | .ty, x, .s2 => x == .alice
  | .ty, x, .s3 => x == .alice
  -- ICEXT of everything else is empty.
  | .ty, _, _ => false
  -- IEXT(rdfs:subClassOf): exactly the pairs of IC whose extensions nest.
  -- (C1, C2) is ABSENT, and that absence is the theorem at the end of the file.
  | .sco, u, v =>
      ((u == .c1 || u == .a2) && (v == .c1 || v == .a2)) ||
      (u == .c2 && (v == .c1 || v == .a2 || v == .c2)) ||
      (u == .filler && (v == .c1 || v == .a2 || v == .c2 || v == .filler)) ||
      ((u == .s1 || u == .s2 || u == .s3) &&
        (v == .c1 || v == .a2 || v == .s1 || v == .s2 || v == .s3))
  -- IEXT(rdfs:subPropertyOf): exactly the pairs of IP whose extensions nest. The
  -- diagonal; p1 and q both ways because their extensions are equal, and both
  -- inside p2; owl:equivalentClass inside rdfs:subClassOf and
  -- owl:equivalentProperty inside rdfs:subPropertyOf, which are forced and not
  -- chosen. (p2, p1) is ABSENT, and that kind separation is what keeps scm-avf2
  -- antitone here.
  | .spo, u, v =>
      (isIP u && u == v) ||
      ((u == .p1 || u == .q) && (v == .p1 || v == .q || v == .p2)) ||
      (u == .eqc && v == .sco) ||
      (u == .eqp && v == .spo)
  -- IEXT(rdfs:domain): every p in IP and c in IC such that every subject of p
  -- lies in ICEXT(c). p1, q and p2 have the single subject alice, so they reach
  -- the three existential restrictions as well; rdf:type has every element as a
  -- subject, because ICEXT(C1) is everything, so it reaches only C1 and A2; the
  -- rest have subjects that are classes or properties and never alice.
  | .dm, u, v =>
      ((u == .p1 || u == .q || u == .p2) &&
        (v == .c1 || v == .a2 || v == .s1 || v == .s2 || v == .s3)) ||
      (u == .ty && (v == .c1 || v == .a2)) ||
      ((u == .sco || u == .spo || u == .dm || u == .rg || u == .avf || u == .svf ||
        u == .onp || u == .eqc || u == .eqp) && (v == .c1 || v == .a2 || v == .c2))
  -- IEXT(rdfs:range): the same with objects for subjects, and it DIFFERS from the
  -- domain table. p1 and q reach Y, because their only object carl is in ICEXT(Y)
  -- while their only subject alice is not; and neither reaches S1, S2 or S3,
  -- where the domain table does.
  | .rg, u, v =>
      ((u == .p1 || u == .q) && (v == .c1 || v == .a2 || v == .c2 || v == .filler)) ||
      ((u == .p2 || u == .ty || u == .sco || u == .spo || u == .dm || u == .rg ||
        u == .avf || u == .svf || u == .onp || u == .eqc || u == .eqp) &&
        (v == .c1 || v == .a2 || v == .c2))
  -- The graph's two universal restrictions, plus A2.
  | .avf, u, v =>
      (u == .c1 && v == .filler) || (u == .c2 && v == .filler) || (u == .a2 && v == .c1)
  -- The three existential restrictions.
  | .svf, u, v =>
      (u == .s1 && v == .filler) || (u == .s2 && v == .c1) || (u == .s3 && v == .filler)
  -- Each restriction is on exactly one property.
  | .onp, u, v =>
      ((u == .c1 || u == .s3) && v == .p1) ||
      ((u == .c2 || u == .a2 || u == .s1 || u == .s2) && v == .p2)
  -- Two distinct classes with the same extension, so Table 5.9's class row has a
  -- pair to work on and scm-eqc1 is exercised on something other than a diagonal.
  | .eqc, u, v => (u == .s1 && v == .s2) || (u == .s2 && v == .s1)
  -- And two distinct properties with the same extension, for scm-eqp1.
  | .eqp, u, v => (u == .p1 && v == .q) || (u == .q && v == .p1)
  -- The asserted individual pairs. IEXT(p1) is NOT empty and is a PROPER subset
  -- of IEXT(p2), which is what makes `p1 rdfs:subPropertyOf p2` hold here for a
  -- reason rather than for want of anything to check.
  | .p1, u, v => u == .alice && v == .carl
  | .q, u, v => u == .alice && v == .carl
  | .p2, u, v => u == .alice && (v == .bob || v == .carl)
  -- Everything else, `other` included, is empty.
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

theorem live_inv_fwd : ∀ p r : LiveD, liveIext (liveι V.inverseOf) p r = true →
    liveIP p ∧ liveIP r ∧ ∀ x y, (liveIext p x y = true ↔ liveIext r y x = true) := by decide

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

/-- **A `W3CModel` of `avfPremises`.** The three list fields are vacuous
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

The facts the model exists to carry, in three theorems, so that a later edit that
hollows the model out fails here instead of passing quietly. Everything above
would still compile with an empty carrier and every relation false; this is what
stops that from being reported as a result.

The first version of this section made the opposite mistake. `IEXT(p1)` was
empty and `ICEXT(Y)` was empty, and both emptinesses were written into the
liveness gate as though they were features. They are not: with `IEXT(p1)` empty
the refutation's own premise `p1 rdfs:subPropertyOf p2` holds because there is
nothing to check, which is the defect this file exists to close, one level down.
`carl` is what fixes it, and `live_is_live` now pins the inclusion as PROPER and
both extensions as NON-EMPTY.

Each fact is stated twice: once over `liveIext` and `liveι`, where it is a closed
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
    (liveIext .ty .carl .filler = true ∧ ¬ liveIext .ty .bob .filler = true) ∧
    (liveIext .ty .c1 (liveι V.Restriction) = true ∧
      ¬ liveIext .ty .filler (liveι V.Restriction) = true) ∧
    (liveIext .p1 .alice .carl = true ∧
      (∀ x y, liveIext .p1 x y = true → liveIext .p2 x y = true) ∧
      ¬ liveIext .p1 .alice .bob = true ∧ liveIext .p2 .alice .bob = true) := by decide

/-- **The liveness gate.** `IC` has three of its members named and does not
swallow the carrier; one class extension is the whole carrier; another is a
proper subset of it, witnessed on both sides; the FILLER extension is non-empty
and proper, witnessed on both sides; `ICEXT(owl:Restriction)` is a proper subset
of `IC`; and `IEXT(p1)` is NON-EMPTY and a PROPER subset of `IEXT(p2)`.

That last conjunct is the one the 15 September 2026 rebuild added and it is the
point of the rebuild. `avfPremises` asserts `p1 rdfs:subPropertyOf p2`, and in
the first version of this model that triple held only because `IEXT(p1)` was
empty. A refutation whose own premise is satisfied vacuously establishes almost
nothing, and the emptiness was written into this gate as if it were a feature. -/
theorem live_is_live :
    (live.IC .c1 ∧ live.IC .c2 ∧ live.IC .filler) ∧ (¬ live.IC .restr ∧ ¬ live.IC .alice) ∧
    (∀ x, live.cext .c1 x) ∧ (∀ x, live.cext .c2 x → live.cext .c1 x) ∧
      (live.cext .c1 .alice ∧ ¬ live.cext .c2 .alice ∧ live.cext .c2 .bob) ∧
    (live.cext .filler .carl ∧ ¬ live.cext .filler .bob) ∧
    (live.cext (live.ι V.Restriction) .c1 ∧ ¬ live.cext (live.ι V.Restriction) .filler) ∧
    (live.iext .p1 .alice .carl ∧ (∀ x y, live.iext .p1 x y → live.iext .p2 x y) ∧
      ¬ live.iext .p1 .alice .bob ∧ live.iext .p2 .alice .bob) :=
  live_is_live_raw

theorem live_is_bridge_coherent_raw :
    ∀ p x y : LiveD, liveIext p x y = true → liveIP p := by decide

/-- **The bridge shape, checked.** Every predicate with a pair in its extension
is in `IP`.

This is an EXTRA property of this model and not a requirement of `W3CModel`, and
the distinction matters: an earlier draft of this file, of `Witness.lean` and of
`Semantics.lean` used bridge coherence as though `W3CModel` demanded it, and
concluded from that that no Herbrand witness could ever be one. Four of them
are: `not_everything_is_w3c_entailed` further down this file, the two in the
section after it, and `mix_not_absolutely_w3c_entailed` in `Mixed.lean`.

What it is actually for: `W3C.lean`'s bridge reads a conforming interpretation
into an `Interp` by `iext p x y := IP p and (x, y) in IEXT p`, so a structure
with a pair under a predicate outside `IP` is not the image of any conforming
interpretation. A refutation built on one would be about a structure the bridge
cannot reach. `W3C` does not impose this, because no arm consumes it and imposing
it would shrink the model class for nothing; this witness satisfies it anyway,
and says so here. -/
theorem live_is_bridge_coherent : ∀ p x y : LiveD, live.iext p x y → liveIP p :=
  live_is_bridge_coherent_raw

/-! ### Every one of the fourteen arms fires in this model

Non-vacuity of a FIELD is weaker than non-vacuity of an ARM. A field can have
something in its extension while the derivation that consumes it never has all
its premises met at once. The twelve theorems below apply each derivation of
`W3C.lean` at a concrete instance of this model and land on a triple the tables
contain, which is the stronger statement and the one the reader wants: every arm
that used to be assumed is now discharged over premises this structure actually
satisfies.

`eqc` and `eqp` carry two arms each, so twelve theorems cover fourteen arms. -/

/-- **rdfs11**, at `C2 ⊑ C1 ⊑ A2`. -/
theorem live_arm_sc_trans : live.sc .c2 .a2 :=
  live_w3c.sc_trans .c2 .c1 .a2 (by decide : liveIext (liveι V.subClassOf) LiveD.c2 LiveD.c1 = true)
    (by decide : liveIext (liveι V.subClassOf) LiveD.c1 LiveD.a2 = true)

/-- **rdfs5**, at `p1 ⊑ q ⊑ p2`. -/
theorem live_arm_sp_trans : live.sp .p1 .p2 :=
  live_w3c.sp_trans .p1 .q .p2 (by decide : liveIext (liveι V.subPropertyOf) LiveD.p1 LiveD.q = true)
    (by decide : liveIext (liveι V.subPropertyOf) LiveD.q LiveD.p2 = true)

/-- **scm-eqc1**, both conclusions, at the two existential restrictions `S1` and
`S2`, which are distinct elements with the same class extension. -/
theorem live_arm_eqc : live.sc .s1 .s2 ∧ live.sc .s2 .s1 :=
  live_w3c.eqc .s1 .s2 (by decide : liveIext (liveι V.equivalentClass) LiveD.s1 LiveD.s2 = true)

/-- **scm-eqp1**, both conclusions, at `p1` and `q`, which are distinct
properties with the same extension. -/
theorem live_arm_eqp : live.sp .p1 .q ∧ live.sp .q .p1 :=
  live_w3c.eqp .p1 .q (by decide : liveIext (liveι V.equivalentProperty) LiveD.p1 LiveD.q = true)

/-- **scm-svf1**, at `∃p2.Y ⊑ ∃p2.C1`, ordered because `Y ⊑ C1`. -/
theorem live_arm_svf_sc : live.sc .s1 .s2 :=
  live_w3c.svf_sc .s1 .s2 .p2 .filler .c1
    (by decide : liveIext (liveι V.someValuesFrom) LiveD.s1 LiveD.filler = true)
    (by decide : liveIext (liveι V.onProperty) LiveD.s1 LiveD.p2 = true)
    (by decide : liveIext (liveι V.someValuesFrom) LiveD.s2 LiveD.c1 = true)
    (by decide : liveIext (liveι V.onProperty) LiveD.s2 LiveD.p2 = true)
    (by decide : liveIext (liveι V.subClassOf) LiveD.filler LiveD.c1 = true)

/-- **scm-svf2**, at `∃p1.Y ⊑ ∃p2.Y`, ordered because `p1 ⊑ p2`. -/
theorem live_arm_svf_sp : live.sc .s3 .s1 :=
  live_w3c.svf_sp .s3 .s1 .p1 .p2 .filler
    (by decide : liveIext (liveι V.someValuesFrom) LiveD.s3 LiveD.filler = true)
    (by decide : liveIext (liveι V.onProperty) LiveD.s3 LiveD.p1 = true)
    (by decide : liveIext (liveι V.someValuesFrom) LiveD.s1 LiveD.filler = true)
    (by decide : liveIext (liveι V.onProperty) LiveD.s1 LiveD.p2 = true)
    (by decide : liveIext (liveι V.subPropertyOf) LiveD.p1 LiveD.p2 = true)

/-- **scm-avf1**, at `∀p2.Y ⊑ ∀p2.C1`, ordered because `Y ⊑ C1`. A universal
restriction is MONOTONE in its filler, which is why this runs the same way round
as the two above. -/
theorem live_arm_avf_sc : live.sc .c2 .a2 :=
  live_w3c.avf_sc .c2 .a2 .p2 .filler .c1
    (by decide : liveIext (liveι V.allValuesFrom) LiveD.c2 LiveD.filler = true)
    (by decide : liveIext (liveι V.onProperty) LiveD.c2 LiveD.p2 = true)
    (by decide : liveIext (liveι V.allValuesFrom) LiveD.a2 LiveD.c1 = true)
    (by decide : liveIext (liveι V.onProperty) LiveD.a2 LiveD.p2 = true)
    (by decide : liveIext (liveι V.subClassOf) LiveD.filler LiveD.c1 = true)

/-- **scm-avf2**, at the premises of `avfPremises` themselves, and the conclusion
is REVERSED: `C2 ⊑ C1` and not `C1 ⊑ C2`. This is the arm the whole file is
about. -/
theorem live_arm_avf_sp : live.sc .c2 .c1 :=
  live_w3c.avf_sp .c1 .c2 .p1 .p2 .filler
    (by decide : liveIext (liveι V.allValuesFrom) LiveD.c1 LiveD.filler = true)
    (by decide : liveIext (liveι V.onProperty) LiveD.c1 LiveD.p1 = true)
    (by decide : liveIext (liveι V.allValuesFrom) LiveD.c2 LiveD.filler = true)
    (by decide : liveIext (liveι V.onProperty) LiveD.c2 LiveD.p2 = true)
    (by decide : liveIext (liveι V.subPropertyOf) LiveD.p1 LiveD.p2 = true)

/-- **scm-dom1**, widening `p1`'s domain from `S1` to `S2`. -/
theorem live_arm_dom_sc : live.iext (live.ι V.domain) .p1 .s2 :=
  live_w3c.dom_sc .p1 .s1 .s2 (by decide : liveIext (liveι V.domain) LiveD.p1 LiveD.s1 = true)
    (by decide : liveIext (liveι V.subClassOf) LiveD.s1 LiveD.s2 = true)

/-- **scm-dom2**, inheriting `p2`'s domain `S1` down to the subproperty `p1`. -/
theorem live_arm_dom_sp : live.iext (live.ι V.domain) .p1 .s1 :=
  live_w3c.dom_sp .p1 .p2 .s1 (by decide : liveIext (liveι V.domain) LiveD.p2 LiveD.s1 = true)
    (by decide : liveIext (liveι V.subPropertyOf) LiveD.p1 LiveD.p2 = true)

/-- **scm-rng1**, widening `p1`'s range from `Y` to `C1`. -/
theorem live_arm_rng_sc : live.iext (live.ι V.range) .p1 .c1 :=
  live_w3c.rng_sc .p1 .filler .c1 (by decide : liveIext (liveι V.range) LiveD.p1 LiveD.filler = true)
    (by decide : liveIext (liveι V.subClassOf) LiveD.filler LiveD.c1 = true)

/-- **scm-rng2**, inheriting `p2`'s range `C2` down to the subproperty `p1`. -/
theorem live_arm_rng_sp : live.iext (live.ι V.range) .p1 .c2 :=
  live_w3c.rng_sp .p1 .p2 .c2 (by decide : liveIext (liveι V.range) LiveD.p2 LiveD.c2 = true)
    (by decide : liveIext (liveι V.subPropertyOf) LiveD.p1 LiveD.p2 = true)

/-- **All fourteen, in one statement**, so that a later edit that quietly stops
exercising one fails here. -/
theorem live_exercises_every_arm :
    live.sc .c2 .a2 ∧ live.sp .p1 .p2 ∧
    (live.sc .s1 .s2 ∧ live.sc .s2 .s1) ∧ (live.sp .p1 .q ∧ live.sp .q .p1) ∧
    live.sc .s1 .s2 ∧ live.sc .s3 .s1 ∧ live.sc .c2 .a2 ∧ live.sc .c2 .c1 ∧
    live.iext (live.ι V.domain) .p1 .s2 ∧ live.iext (live.ι V.domain) .p1 .s1 ∧
    live.iext (live.ι V.range) .p1 .c1 ∧ live.iext (live.ι V.range) .p1 .c2 :=
  ⟨live_arm_sc_trans, live_arm_sp_trans, live_arm_eqc, live_arm_eqp,
   live_arm_svf_sc, live_arm_svf_sp, live_arm_avf_sc, live_arm_avf_sp,
   live_arm_dom_sc, live_arm_dom_sp, live_arm_rng_sc, live_arm_rng_sp⟩

/-! ### And what is still vacuous, named rather than left to be discovered

Five of the twenty-one fields of `W3C` still hold in this model because nothing
is in the extension their antecedent reads. Both halves of that sentence are
theorems: `live_fires_the_other_sixteen` exhibits a satisfied antecedent for each
of the other sixteen, and `live_leaves_exactly_these_five_vacuous` names the five.
Sixteen plus five is twenty-one, so neither number can drift from the tables
without the build going red. The five are exactly the fields that carry NONE of
the fourteen arms: `Soundness.lean` consumes `same_fwd`,
`sym_fwd`, `trp_fwd`, `inv_fwd` and `hv_eq` through projections out of
`Conditions`, never through a derivation.

`same_fwd` is the one that cannot be exercised non-trivially at all, and that is
the specification's doing rather than this model's: RBS Table 5.9's first row
reads `( a₁ , a₂ ) ∈ IEXT(I(owl:sameAs))` **iff** `a₁ = a₂`, so the only pairs
any conforming interpretation can put in that extension are diagonal ones and the
only instance of the field is `a = a`.

The other four are ordinary omissions and could be closed, at a price this file
declines to pay: each needs its own vocabulary element plus a property or a
restriction to hold it, and every condition here is quantified over the carrier
three or four times, so the `decide` cost is quartic in the number of elements.
Twenty-six elements already cost about ten seconds. The honest report is that
these four are not exercised, not that they cannot be. -/

/-- **The other sixteen fields fire**, one satisfied antecedent each, so that
"exactly these five" below is earned rather than asserted. Sixteen plus five is
the twenty-one fields of `W3C`.

`sc_fwd`, `sp_fwd`, `dom_fwd`, `rng_fwd`, `eqc_fwd`, `eqp_fwd`, `svf_eq`,
`svf_typ`, `avf_eq`, `avf_typ`, `onp_typ` and `restr_IC` are given a pair in the
extension their antecedent reads; `sc_bwd`, `sp_bwd`, `dom_bwd` and `rng_bwd` are
given the whole antecedent, guards and universally quantified clause together,
because those are the four whose hypotheses can be met for want of anything to
check and were. -/
theorem live_fires_the_other_sixteen_raw :
    liveIext .sco .c2 .c1 = true ∧
    (liveIext .ty .c2 .cls = true ∧ liveIext .ty .c1 .cls = true ∧
      ∀ x, liveIext .ty x .c2 = true → liveIext .ty x .c1 = true) ∧
    liveIext .spo .p1 .p2 = true ∧
    (liveIP .p1 ∧ liveIP .p2 ∧
      ∀ x y, liveIext .p1 x y = true → liveIext .p2 x y = true) ∧
    liveIext (liveι V.domain) .p2 .c1 = true ∧
    (liveIP .p2 ∧ liveIext .ty .c1 .cls = true ∧
      ∀ x y, liveIext .p2 x y = true → liveIext .ty x .c1 = true) ∧
    liveIext (liveι V.range) .p2 .c2 = true ∧
    (liveIP .p2 ∧ liveIext .ty .c2 .cls = true ∧
      ∀ x y, liveIext .p2 x y = true → liveIext .ty y .c2 = true) ∧
    liveIext (liveι V.equivalentClass) .s1 .s2 = true ∧
    liveIext (liveι V.equivalentProperty) .p1 .q = true ∧
    (liveIext (liveι V.someValuesFrom) .s1 .filler = true ∧
      liveIext (liveι V.onProperty) .s1 .p2 = true) ∧
    (liveIext (liveι V.allValuesFrom) .c1 .filler = true ∧
      liveIext (liveι V.onProperty) .c1 .p1 = true) ∧
    liveIext .ty .c1 (liveι V.Restriction) = true := by decide

/-- The same sixteen over `live`, by definitional unfolding. -/
theorem live_fires_the_other_sixteen :
    live.sc .c2 .c1 ∧
    (live.IC .c2 ∧ live.IC .c1 ∧ ∀ x, live.cext .c2 x → live.cext .c1 x) ∧
    live.sp .p1 .p2 ∧
    (liveIP .p1 ∧ liveIP .p2 ∧ ∀ x y, live.iext .p1 x y → live.iext .p2 x y) ∧
    live.iext (live.ι V.domain) .p2 .c1 ∧
    (liveIP .p2 ∧ live.IC .c1 ∧ ∀ x y, live.iext .p2 x y → live.cext .c1 x) ∧
    live.iext (live.ι V.range) .p2 .c2 ∧
    (liveIP .p2 ∧ live.IC .c2 ∧ ∀ x y, live.iext .p2 x y → live.cext .c2 y) ∧
    live.iext (live.ι V.equivalentClass) .s1 .s2 ∧
    live.iext (live.ι V.equivalentProperty) .p1 .q ∧
    (live.iext (live.ι V.someValuesFrom) .s1 .filler ∧
      live.iext (live.ι V.onProperty) .s1 .p2) ∧
    (live.iext (live.ι V.allValuesFrom) .c1 .filler ∧
      live.iext (live.ι V.onProperty) .c1 .p1) ∧
    live.cext (live.ι V.Restriction) .c1 :=
  live_fires_the_other_sixteen_raw

theorem live_leaves_exactly_these_five_vacuous_raw :
    (∀ a b : LiveD, ¬ liveIext (liveι V.sameAs) a b = true) ∧
    (∀ p : LiveD, ¬ liveIext .ty p (liveι V.symmetricProperty) = true) ∧
    (∀ p : LiveD, ¬ liveIext .ty p (liveι V.transitiveProperty) = true) ∧
    (∀ p r : LiveD, ¬ liveIext (liveι V.inverseOf) p r = true) ∧
    (∀ z a : LiveD, ¬ liveIext (liveι V.hasValue) z a = true) := by decide

/-- **The five fields this witness does not exercise**, pinned. Each carries none
of the fourteen arms. Everything else in `W3C` has something in its extension
here, and `live_exercises_every_arm` shows every arm firing. -/
theorem live_leaves_exactly_these_five_vacuous :
    (∀ a b : LiveD, ¬ live.iext (live.ι V.sameAs) a b) ∧
    (∀ p : LiveD, ¬ live.cext (live.ι V.symmetricProperty) p) ∧
    (∀ p : LiveD, ¬ live.cext (live.ι V.transitiveProperty) p) ∧
    (∀ p r : LiveD, ¬ live.iext (live.ι V.inverseOf) p r) ∧
    (∀ z a : LiveD, ¬ live.iext (live.ι V.hasValue) z a) :=
  live_leaves_exactly_these_five_vacuous_raw

theorem live_c1_is_a_class : liveIext .ty .c1 .cls = true := by decide
theorem live_c2_is_a_class : liveIext .ty .c2 .cls = true := by decide
theorem live_p2_is_in_IP : liveIP .p2 := by decide

/-- The universally quantified clause `dom_bwd` demands, at `C1`, discharged
over the pairs of `p2` and NOT by there being no pairs. -/
theorem live_p2_subjects_are_c1 :
    ∀ x y : LiveD, liveIext .p2 x y = true → liveIext .ty x .c1 = true := by decide

/-- The same clause for `rng_bwd`, at `C2`. `alice` is outside `ICEXT(C2)` and
both of her `p2`-successors are inside it, which is what makes the domain and
range extensions differ. -/
theorem live_p2_objects_are_c2 :
    ∀ x y : LiveD, liveIext .p2 x y = true → liveIext .ty y .c2 = true := by decide

theorem live_p2_is_not_a_domain_of_c2 : ¬ liveIext (liveι V.domain) .p2 .c2 = true := by decide

/-- `dom_bwd` is discharged over a NON-EMPTY relation: the clause it demands is
proved at `p2`'s two pairs and not by there being no pairs, which is the thing the
second kernel's own witness fails to do for this condition. -/
theorem live_dom_bwd_is_exercised : live.iext (live.ι V.domain) .p2 .c1 :=
  live_w3c.dom_bwd .p2 .c1 live_p2_is_in_IP live_c1_is_a_class live_p2_subjects_are_c1

/-- `rng_bwd`, likewise, and at a class `dom_bwd` does NOT reach. The two
backward halves of Table 5.8 are separated by this model rather than satisfied
together by accident: `(p2, C2)` is in the range extension and not in the domain
extension, because both of `alice`'s `p2`-successors are in `ICEXT(C2)` and
`alice` herself is not. -/
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
`W3CModel`: `avfWitness` contains no `rdf:type` triple at all, so every class
extension is empty there and `avf_typ` and `onp_typ` fail for want of an
`owl:Restriction` typing, `onp_typ` failing a second time on its `IP p` conjunct,
which the empty `IP` cannot supply. Unlike the four non-entailments this file and
`Mixed.lean` transfer, this one genuinely needed a structure built for it. That
is why the structure below exists; it is not a general fact about Herbrand
witnesses, which an earlier version of this paragraph turned it into.

This one is about a class much closer to the specification's: the refuting
structure satisfies Table 5.8 in both directions, Table 5.6's `someValuesFrom`
and `allValuesFrom` equalities, Tables 5.9, 5.12 and 5.13, and the typing rows of
Tables 5.2 and 5.3, and it is bridge-coherent. Every one of the fourteen arms
fires in it at a concrete instance (`live_exercises_every_arm`), and the premise
`p1 rdfs:subPropertyOf p2` holds because `IEXT(p1)` is a proper non-empty subset
of `IEXT(p2)` rather than because `IEXT(p1)` is empty, which is what the first
version of this model got wrong. A rule concluding `C1 rdfs:subClassOf C2` from
these premises, which is what copying the shape of `scm-avf1`, `scm-svf1` and
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

/-! ## The degenerate model, proved rather than asserted

`Witness.lean` says in English, beside `saturated_is_a_model`, that `saturated`
also satisfies the conditions in `W3C.lean`. An unproved claim in a docstring is
the defect this whole file exists to remove, so it is a theorem here. -/

/-- **`W3C` is satisfiable trivially, and that is exactly why bare satisfiability
is not the gate.** `saturated` has domain `Unit` and every relation total, so
both sides of every equality in `W3C` are all of `Unit` and every field holds
without saying anything. It distinguishes no condition from any other and
refutes nothing.

Note what it does NOT extend to. `W3CModel` would additionally demand
`oneOf_eq`, and that fails here whenever the graph carries an `owl:oneOf` triple
whose list is EMPTY: the left side is `ICEXT(c)`, which is all of `Unit`, and the
right side is `∃ m ∈ [], x = I(m)`, which is false. Table 5.5's equality forces an
empty enumeration to denote the empty class, and a model in which every class is
the whole universe cannot do that. `Conditions.oneOf` carries only the `⊇` half
and so never notices. That is the same asymmetry recorded at `Model.oneOf` in
`Semantics.lean`, seen from the other side. -/
theorem saturated_meets_the_w3c_conditions : W3C saturated (fun _ => True) where
  sc_fwd := fun _ _ _ => ⟨trivial, trivial, fun _ _ => trivial⟩
  sc_bwd := fun _ _ _ _ _ => trivial
  sp_fwd := fun _ _ _ => ⟨trivial, trivial, fun _ _ _ => trivial⟩
  sp_bwd := fun _ _ _ _ _ => trivial
  dom_fwd := fun _ _ _ => ⟨trivial, trivial, fun _ _ _ => trivial⟩
  dom_bwd := fun _ _ _ _ _ => trivial
  rng_fwd := fun _ _ _ => ⟨trivial, trivial, fun _ _ _ => trivial⟩
  rng_bwd := fun _ _ _ _ _ => trivial
  eqc_fwd := fun _ _ _ => ⟨trivial, trivial, fun _ => Iff.rfl⟩
  eqp_fwd := fun _ _ _ => ⟨trivial, trivial, fun _ _ => Iff.rfl⟩
  same_fwd := fun a b _ => by cases a; cases b; rfl
  inv_fwd := fun _ _ _ => ⟨trivial, trivial, fun _ _ => Iff.rfl⟩
  sym_fwd := fun _ _ _ _ _ => trivial
  trp_fwd := fun _ _ _ _ _ _ _ => trivial
  svf_eq := fun _ _ _ _ _ _ => ⟨fun _ => ⟨(), trivial, trivial⟩, fun _ => trivial⟩
  avf_eq := fun _ _ _ _ _ _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩
  hv_eq := fun _ _ _ _ _ _ => Iff.rfl
  restr_IC := fun _ _ => trivial
  svf_typ := fun _ _ _ => ⟨trivial, trivial⟩
  avf_typ := fun _ _ _ => ⟨trivial, trivial⟩
  onp_typ := fun _ _ _ => ⟨trivial, trivial⟩

/-- A one-triple graph enumerating nothing: `E owl:oneOf rdf:nil`. -/
def emptyOneOfG : List Triple := [⟨"<e:E>", V.oneOf, V.nil⟩]

/-- **And the gap in the docstring above is a theorem too.** `saturated` meets
every field of `W3C`, and it is still not a `W3CModel` of this graph, because
Table 5.5's equality forces an empty enumeration to denote the empty class while
`saturated` makes every class the whole universe.

So `W3C` and `W3CModel` genuinely differ, the list rows are not decoration, and
"`saturated` satisfies the specification conditions" is true of the conditions
and false of the models. `Conditions.oneOf` carries only the `⊇` half and never
notices, which is why `saturated_is_a_model` holds for EVERY graph including
this one. -/
theorem saturated_is_not_a_w3c_model_of_an_empty_enumeration :
    ¬ W3CModel saturated (fun _ => True) emptyOneOfG := by
  intro W
  have h := (W.oneOf_eq "<e:E>" V.nil [] (by simp [emptyOneOfG]) Chain.nil ()).mp trivial
  simp at h

/-- The same graph, modelled by the weaker conditions without complaint. The two
sit side by side on purpose: this is what the `⊆` half of Table 5.5 buys, and
what leaving it out costs. -/
theorem saturated_is_a_model_of_the_same_graph : Model saturated emptyOneOfG :=
  saturated_is_a_model emptyOneOfG

/-! ## And `W3CEntails` is not everything either

`live` closes one vacuity hole: `W3C` has a non-degenerate model, so
`W3CModel.toModel` is not a theorem about an empty class. The other hole is that
`W3CEntails` could hold of every triple, which would make
`certificate_w3c_sound` say nothing at all. It does not, and the cheapest
witness closes it: over the EMPTY graph every antecedent in `W3C` is false, and
`IP := fun _ => False` makes the four backward conditions vacuous too. -/

/-- The Herbrand interpretation of the empty graph is a `W3CModel` of it,
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
`Witness.lean`'s own header, restated over the `W3CModel` class.

An earlier version of this docstring called it "the one obligation there that
transfers without a new hand-built structure". It is the FIRST, not the only:
`an_unlisted_individual_is_not_w3c_entailed`,
`membership_in_one_member_is_not_w3c_enough` and `Mixed.lean`'s
`mix_not_absolutely_w3c_entailed` transfer the same way, and this file used to
list all three among the results it could not reach. -/
theorem not_everything_is_w3c_entailed :
    ¬ W3CEntails [] ⟨"<http://ex.org/a>", "<http://ex.org/b>", "<http://ex.org/c>"⟩ := by
  intro h
  have hs := h (herbrand []) (fun _ => False) empty_herbrand_is_a_w3c_model
  simp at hs


/-! ## Two more non-entailments here, a third in `Mixed.lean`, on the interpretations they already had

`IP` is a free PARAMETER of `W3C`, not a field of `Interp`, and the four
backward conditions are the only fields that consume it as a hypothesis. Choose
`IP := fun _ => False` and `sp_bwd`, `dom_bwd` and `rng_bwd` become vacuous,
because their antecedents `IP a`, `IP p` have no instances. `sc_bwd` is guarded
by `IC` instead, and over a Herbrand interpretation `I.IC a` is
`⟨a, rdf:type, rdfs:Class⟩ ∈ H`, so a witness graph carrying no `rdfs:Class`
typing makes THAT field vacuous too.

An earlier draft of this file, of `Witness.lean` and of `Semantics.lean` claimed
the opposite in five places: that an empty `IC` makes Table 5.8's backward
direction FORCE `rdfs:subClassOf` and `rdfs:subPropertyOf` triples the witness
lacks, and that every conforming countermodel has to be a hand-built finite
structure. Both are false, and the first is inverted: an empty `IC` is exactly
what makes `sc_bwd` vacuous. The claim also silently promoted
`live_is_bridge_coherent`, which is an EXTRA property the `live` model happens
to have, into a requirement of `W3CModel`, which it is not.

FOUR of the seven results listed there transfer on the nose, with the existing
witness graphs unchanged and nothing hand-built: two proved in this section, one
in `Mixed.lean`, and one that was already proved further up THIS file at the
moment the list called it open. The remaining three do not, and the reason is
stated at each of them rather than generalised into a slogan.

| result | transfers | why |
|---|---|---|
| `not_everything_is_entailed` | yes, and already did | `not_everything_is_w3c_entailed`, below |
| `an_unlisted_individual_is_not_entailed` | yes | `an_unlisted_individual_is_not_w3c_entailed` |
| `membership_in_one_member_does_not_give_the_intersection` | yes | `membership_in_one_member_is_not_w3c_enough` |
| `mix_not_absolutely_entailed` | yes | `mix_not_absolutely_w3c_entailed`, in `Mixed.lean` |
| `the_old_svf_derivation_is_not_entailed` | no | `svfWitness` has `R owl:onProperty p` with no `R rdf:type owl:Restriction`, so `onp_typ` fails on its first conjunct for EVERY choice of `IP` |
| `feed_is_not_refuted` | no | `feed` carries `Lion rdfs:subClassOf Carnivore` and no `rdfs:Class` typing, so `sc_fwd` fails; and `¬ Unsat` runs the wrong way for transfer anyway |
| `not_unsat_of_joint_model` | no | it is a lemma with a hypothesis rather than a witness, and the same direction problem |

The two `owl:oneOf` and `owl:intersectionOf` graphs go through because the list
field of `W3CModel` is an `iff` and their witnesses satisfy it in both
directions: `ooWitness` types exactly the two listed members as `E`, and
`intWitness` makes exactly `w` a `K` and exactly `w` both an `M1` and an `M2`.
`v` is an `M1` and not an `M2`, which is what keeps `int_eq` true and the
conclusion false at the same time.
-/

/-- Exactly the two listed members are typed `E`. Decidable over a seven-triple
list, which is what lets `oneOf_eq`'s forward direction be discharged without
case analysis on string literals. -/
private theorem oo_typed_E :
    ∀ t ∈ ooWitness, t.p = V.type → t.o = tE → t.s = tA ∨ t.s = tB := by decide

/-- **The `owl:oneOf` witness is a `W3CModel`.** `ooWitness` carries no
`rdfs:Class` typing, so `IC` is empty and `sc_bwd` is vacuous; with
`IP := fun _ => False` the other three backward fields are vacuous as well; and
every forward field has an antecedent this graph never satisfies.

Table 5.5's equality is the one field that has to be EARNED rather than
dodged, and this witness satisfies it in both directions, because `ICEXT(E)` is
exactly `{a, b}`. `Conditions.oneOf` carries only the `⊇` half, which is the
asymmetry `an_unlisted_individual_is_not_entailed`'s docstring records. -/
theorem oo_witness_is_a_w3c_model :
    W3CModel (herbrand ooWitness) (fun _ => False) ooPremises where
  conds :=
    { sc_fwd := fun a b h => absurd h (not_mem_pred ooWitness V.subClassOf (by decide) a b)
      sc_bwd := fun a _ ha => absurd ha (not_typed ooWitness V.Class (by decide) a)
      sp_fwd := fun a b h => absurd h (not_mem_pred ooWitness V.subPropertyOf (by decide) a b)
      sp_bwd := fun _ _ h => absurd h (fun x => x)
      dom_fwd := fun p c h => absurd h (not_mem_pred ooWitness V.domain (by decide) p c)
      dom_bwd := fun _ _ h => absurd h (fun x => x)
      rng_fwd := fun p c h => absurd h (not_mem_pred ooWitness V.range (by decide) p c)
      rng_bwd := fun _ _ h => absurd h (fun x => x)
      eqc_fwd := fun a b h => absurd h (not_mem_pred ooWitness V.equivalentClass (by decide) a b)
      eqp_fwd := fun a b h =>
        absurd h (not_mem_pred ooWitness V.equivalentProperty (by decide) a b)
      same_fwd := fun a b h => absurd h (not_mem_pred ooWitness V.sameAs (by decide) a b)
      inv_fwd := fun p q h => absurd h (not_mem_pred ooWitness V.inverseOf (by decide) p q)
      sym_fwd := fun p h => absurd h (not_typed ooWitness V.symmetricProperty (by decide) p)
      trp_fwd := fun p h => absurd h (not_typed ooWitness V.transitiveProperty (by decide) p)
      svf_eq := fun z c _ h => absurd h (not_mem_pred ooWitness V.someValuesFrom (by decide) z c)
      avf_eq := fun z c _ h => absurd h (not_mem_pred ooWitness V.allValuesFrom (by decide) z c)
      hv_eq := fun z a _ h => absurd h (not_mem_pred ooWitness V.hasValue (by decide) z a)
      restr_IC := fun x h => absurd h (not_typed ooWitness V.Restriction (by decide) x)
      svf_typ := fun z c h => absurd h (not_mem_pred ooWitness V.someValuesFrom (by decide) z c)
      avf_typ := fun z c h => absurd h (not_mem_pred ooWitness V.allValuesFrom (by decide) z c)
      onp_typ := fun z p h => absurd h (not_mem_pred ooWitness V.onProperty (by decide) z p) }
  facts := fun t ht => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)
  int_eq := fun c l _ hc => absurd hc (not_mem_pred ooPremises V.intersectionOf (by decide) c l)
  uni_eq := fun c l _ hc => absurd hc (not_mem_pred ooPremises V.unionOf (by decide) c l)
  oneOf_eq := by
    intro c l ms hc hchain x
    obtain ⟨rfl, rfl⟩ := oo_only_oneOf _ hc rfl
    rw [oo_chain_l0 ms hchain]
    constructor
    · intro hx
      rcases oo_typed_E ⟨x, V.type, tE⟩ hx rfl rfl with rfl | rfl
      · exact ⟨tA, by simp, rfl⟩
      · exact ⟨tB, by simp, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · show (⟨tA, V.type, tE⟩ : Triple) ∈ ooWitness
        decide
      · rcases List.mem_cons.mp hm with rfl | hm
        · show (⟨tB, V.type, tE⟩ : Triple) ∈ ooWitness
          decide
        · cases hm

/-- **`cls-oo` stops at the members, over the `W3CModel` class.** The same
statement as `an_unlisted_individual_is_not_entailed` with `W3CEntails` for
`Entails`, and the same interpretation discharges it. -/
theorem an_unlisted_individual_is_not_w3c_entailed :
    ¬ W3CEntails ooPremises ⟨tZ, V.type, tE⟩ := fun h =>
  absurd (h (herbrand ooWitness) (fun _ => False) oo_witness_is_a_w3c_model)
    (by decide : (⟨tZ, V.type, tE⟩ : Triple) ∉ ooWitness)

/-- Whatever this graph makes a `K` it already makes an `M1` and an `M2`. -/
private theorem int_K_gives_both : ∀ t ∈ intWitness, t.p = V.type → t.o = tK →
    (⟨t.s, V.type, tM1⟩ : Triple) ∈ intWitness ∧
      (⟨t.s, V.type, tM2⟩ : Triple) ∈ intWitness := by decide

/-- And whatever it makes both it already makes a `K`. `v` is an `M1` and not an
`M2`, so it never triggers this, which is the whole content of the theorem
below. -/
private theorem int_both_give_K : ∀ t ∈ intWitness, ∀ u ∈ intWitness,
    (t.p = V.type ∧ t.o = tM1 ∧ u.p = V.type ∧ u.o = tM2 ∧ u.s = t.s) →
      (⟨t.s, V.type, tK⟩ : Triple) ∈ intWitness := by decide

/-- **The `owl:intersectionOf` witness is a `W3CModel`.** Table 5.4's
equality holds in both directions here, not just the `⊆` half `Conditions.int`
and `Conditions.int2` carry between them. -/
theorem int_witness_is_a_w3c_model :
    W3CModel (herbrand intWitness) (fun _ => False) intPremises where
  conds :=
    { sc_fwd := fun a b h => absurd h (not_mem_pred intWitness V.subClassOf (by decide) a b)
      sc_bwd := fun a _ ha => absurd ha (not_typed intWitness V.Class (by decide) a)
      sp_fwd := fun a b h => absurd h (not_mem_pred intWitness V.subPropertyOf (by decide) a b)
      sp_bwd := fun _ _ h => absurd h (fun x => x)
      dom_fwd := fun p c h => absurd h (not_mem_pred intWitness V.domain (by decide) p c)
      dom_bwd := fun _ _ h => absurd h (fun x => x)
      rng_fwd := fun p c h => absurd h (not_mem_pred intWitness V.range (by decide) p c)
      rng_bwd := fun _ _ h => absurd h (fun x => x)
      eqc_fwd := fun a b h => absurd h (not_mem_pred intWitness V.equivalentClass (by decide) a b)
      eqp_fwd := fun a b h =>
        absurd h (not_mem_pred intWitness V.equivalentProperty (by decide) a b)
      same_fwd := fun a b h => absurd h (not_mem_pred intWitness V.sameAs (by decide) a b)
      inv_fwd := fun p q h => absurd h (not_mem_pred intWitness V.inverseOf (by decide) p q)
      sym_fwd := fun p h => absurd h (not_typed intWitness V.symmetricProperty (by decide) p)
      trp_fwd := fun p h => absurd h (not_typed intWitness V.transitiveProperty (by decide) p)
      svf_eq := fun z c _ h => absurd h (not_mem_pred intWitness V.someValuesFrom (by decide) z c)
      avf_eq := fun z c _ h => absurd h (not_mem_pred intWitness V.allValuesFrom (by decide) z c)
      hv_eq := fun z a _ h => absurd h (not_mem_pred intWitness V.hasValue (by decide) z a)
      restr_IC := fun x h => absurd h (not_typed intWitness V.Restriction (by decide) x)
      svf_typ := fun z c h => absurd h (not_mem_pred intWitness V.someValuesFrom (by decide) z c)
      avf_typ := fun z c h => absurd h (not_mem_pred intWitness V.allValuesFrom (by decide) z c)
      onp_typ := fun z p h => absurd h (not_mem_pred intWitness V.onProperty (by decide) z p) }
  facts := fun t ht => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)
  int_eq := by
    intro c l ms hc hchain x
    obtain ⟨rfl, rfl⟩ := i_only_int _ hc rfl
    rw [i_chain_l0 ms hchain]
    constructor
    · intro hx m hm
      obtain ⟨h1, h2⟩ := int_K_gives_both ⟨x, V.type, tK⟩ hx rfl rfl
      rcases List.mem_cons.mp hm with rfl | hm
      · exact h1
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact h2
        · cases hm
    · intro hall
      exact int_both_give_K ⟨x, V.type, tM1⟩ (hall tM1 (by simp))
        ⟨x, V.type, tM2⟩ (hall tM2 (by simp)) ⟨rfl, rfl, rfl, rfl, rfl⟩
  uni_eq := fun c l _ hc => absurd hc (not_mem_pred intPremises V.unionOf (by decide) c l)
  oneOf_eq := fun c l _ hc => absurd hc (not_mem_pred intPremises V.oneOf (by decide) c l)

/-- **`cls-int1` still needs every member, over the `W3CModel` class.**
The same statement as `membership_in_one_member_does_not_give_the_intersection`
with `W3CEntails` for `Entails`. -/
theorem membership_in_one_member_is_not_w3c_enough :
    ¬ W3CEntails intPremises ⟨tv, V.type, tK⟩ := fun h =>
  absurd (h (herbrand intWitness) (fun _ => False) int_witness_is_a_w3c_model)
    (by decide : (⟨tv, V.type, tK⟩ : Triple) ∉ intWitness)

/-! ### And two that do not transfer, with the obstruction checked rather than argued

Both obstructions are independent of `IP`: the field that fails does not mention
it. They are recorded as theorems so that a later reader who tries the same
`IP := fun _ => False` trick is told why it stops, instead of rediscovering it. -/

/-- `svfWitness` carries `R owl:someValuesFrom D` and `R owl:onProperty p` and
types `R` as nothing at all, so RBS Table 5.3's `owl:onProperty` row fails on its
FIRST conjunct, `z ∈ ICEXT(owl:Restriction)`. No choice of `IP` repairs that,
which is why `the_old_svf_derivation_is_not_entailed` stays a statement about
the `Conditions` class. -/
theorem svf_witness_misses_the_restriction_typing :
    ((⟨tR, V.onProperty, tp⟩ : Triple) ∈ svfWitness) ∧
      (⟨tR, V.type, V.Restriction⟩ : Triple) ∉ svfWitness := by decide

/-! `feed`'s obstruction is the matching one and it is checked in
`RefuteWitness.lean`, beside the theorem it blocks, because `feedClosure` lives
there. -/

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

/-- info: 'OOCert.live_exercises_every_arm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms live_exercises_every_arm

/-- info: 'OOCert.live_fires_the_other_sixteen' depends on axioms: [propext] -/
#guard_msgs in
#print axioms live_fires_the_other_sixteen

/-- info: 'OOCert.live_leaves_exactly_these_five_vacuous' depends on axioms: [propext] -/
#guard_msgs in
#print axioms live_leaves_exactly_these_five_vacuous

/-- info: 'OOCert.scm_avf2_runs_one_way_under_the_specification' depends on axioms: [propext] -/
#guard_msgs in
#print axioms scm_avf2_runs_one_way_under_the_specification

/-- info: 'OOCert.not_everything_is_w3c_entailed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_everything_is_w3c_entailed

/-- info: 'OOCert.saturated_meets_the_w3c_conditions' does not depend on any axioms -/
#guard_msgs in
#print axioms saturated_meets_the_w3c_conditions

/--
info: 'OOCert.saturated_is_not_a_w3c_model_of_an_empty_enumeration' depends on axioms: [propext,
Quot.sound]
-/
#guard_msgs in
#print axioms saturated_is_not_a_w3c_model_of_an_empty_enumeration

/-- info: 'OOCert.oo_witness_is_a_w3c_model' depends on axioms: [propext] -/
#guard_msgs in
#print axioms oo_witness_is_a_w3c_model

/-- info: 'OOCert.an_unlisted_individual_is_not_w3c_entailed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms an_unlisted_individual_is_not_w3c_entailed

/-- info: 'OOCert.int_witness_is_a_w3c_model' depends on axioms: [propext] -/
#guard_msgs in
#print axioms int_witness_is_a_w3c_model

/-- info: 'OOCert.membership_in_one_member_is_not_w3c_enough' depends on axioms: [propext] -/
#guard_msgs in
#print axioms membership_in_one_member_is_not_w3c_enough

end OOCert
