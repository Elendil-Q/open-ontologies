import OOCert.Triple

/-!
# Semantics

The meaning against which a certificate is checked. It is the RDF-based
reading of a graph (RDF 1.1 Semantics, section 5; OWL 2 RDF-Based Semantics,
section 5), restricted to the vocabulary the engine's rules use.

## Shape of an interpretation

An interpretation is a domain `D`, a denotation `ι` for every term, and one
ternary relation `iext p x y`, read "(x, y) is in the extension of the
property p". Class membership is not a separate primitive: `x` is in class
`c` when `(x, c)` is in the extension of `rdf:type`. That is the RDF-based
semantics' `ICEXT`, and it is what makes a triple `s rdf:type o` mean the same
thing whether it was asserted or derived by a domain rule.

A triple `s p o` is satisfied when `iext (ι p) (ι s) (ι o)`. Nothing else.
Every piece of schema meaning is a condition on the interpretation
(`Conditions`), quantified over domain elements, the way the W3C tables state
them ("if (p, c) is in IEXT(I(rdfs:domain)) then ...").

## The conditions are the weakest the rules need

Each condition is the *if* direction of the corresponding W3C semantic
condition, or a consequence of it, never more. Where the W3C table states an
*iff* (subClassOf, for instance, is extensional in the RDF-based semantics)
only the half the rules use is assumed, plus transitivity where a rule
concludes a schema triple. Weaker assumptions mean more interpretations, so a
rule proved sound here is sound under the W3C semantics and under the OWL 2
Direct Semantics translated to triples, since every model of those satisfies
these conditions.

The two list constructors are the exception to "conditions on the
interpretation alone". `owl:intersectionOf` and `owl:unionOf` point at an RDF
list, and a list is a syntactic object: the W3C tables read it off the graph
with the sequence notation. `Model` therefore reads the list off the graph
too, through `Chain`, and states the class condition relative to the graph
being interpreted.

## What is not here

Literal values are terms like any other: two spellings of one value are two
terms. No rule compares literals by value, so nothing is lost, but a
consumer must not read `Entails` as datatype-aware. `owl:sameAs` is read as
identity of denotation, which is the standard condition; only its symmetry is
used.
-/
namespace OOCert

structure Interp where
  D : Type
  ι : Term → D
  iext : D → D → D → Prop

namespace Interp
variable (I : Interp)

/-- `x` is in class `c`: `(x, c) ∈ IEXT(rdf:type)`. -/
def cext (c x : I.D) : Prop := I.iext (I.ι V.type) x c
/-- `(a, b) ∈ IEXT(rdfs:subClassOf)`. -/
def sc (a b : I.D) : Prop := I.iext (I.ι V.subClassOf) a b
/-- `(a, b) ∈ IEXT(rdfs:subPropertyOf)`. -/
def sp (a b : I.D) : Prop := I.iext (I.ι V.subPropertyOf) a b
/-- A triple holds when its predicate's extension contains the pair. -/
def sat (t : Triple) : Prop := I.iext (I.ι t.p) (I.ι t.s) (I.ι t.o)

end Interp

/-- The semantic conditions, one group per rule family. -/
structure Conditions (I : Interp) : Prop where
  /-- rdfs9. RDF-based semantics: subClassOf implies extension inclusion. -/
  sc_sub : ∀ a b, I.sc a b → ∀ x, I.cext a x → I.cext b x
  /-- rdfs11. Follows from the extensional reading of subClassOf. -/
  sc_trans : ∀ a b c, I.sc a b → I.sc b c → I.sc a c
  /-- rdfs7. -/
  sp_sub : ∀ a b, I.sp a b → ∀ x y, I.iext a x y → I.iext b x y
  /-- rdfs5. -/
  sp_trans : ∀ a b c, I.sp a b → I.sp b c → I.sp a c
  /-- rdfs2. -/
  dom : ∀ p c, I.iext (I.ι V.domain) p c → ∀ x y, I.iext p x y → I.cext c x
  /-- rdfs3. -/
  rng : ∀ p c, I.iext (I.ι V.range) p c → ∀ x y, I.iext p x y → I.cext c y
  /-- prp-trp. Members of owl:TransitiveProperty have transitive extensions. -/
  trp : ∀ p, I.cext (I.ι V.transitiveProperty) p →
    ∀ x y z, I.iext p x y → I.iext p y z → I.iext p x z
  /-- prp-symp. -/
  symp : ∀ p, I.cext (I.ι V.symmetricProperty) p → ∀ x y, I.iext p x y → I.iext p y x
  /-- prp-inv1, prp-inv2. -/
  inv : ∀ p q, I.iext (I.ι V.inverseOf) p q → ∀ x y, (I.iext p x y ↔ I.iext q y x)
  /-- eq-sym. owl:sameAs is identity of denotation. -/
  same : ∀ a b, I.iext (I.ι V.sameAs) a b → a = b
  /-- scm-eqc1, scm-eqc2. -/
  eqc : ∀ a b, I.iext (I.ι V.equivalentClass) a b → I.sc a b ∧ I.sc b a
  /-- scm-eqp1, scm-eqp2. -/
  eqp : ∀ a b, I.iext (I.ι V.equivalentProperty) a b → I.sp a b ∧ I.sp b a
  /-- cls-svf1. A witness puts `x` into the restriction class. Only this
  direction is assumed; the converse is not needed by any rule. -/
  svf : ∀ r p c, I.iext (I.ι V.onProperty) r p → I.iext (I.ι V.someValuesFrom) r c →
    ∀ x y, I.iext p x y → I.cext c y → I.cext r x
  /-- cls-avf. Everything an `x` in the restriction reaches by `p` is in the
  filler. The mirror of `svf`, and like it only the direction the rule uses. -/
  avf : ∀ r p c, I.iext (I.ι V.onProperty) r p → I.iext (I.ι V.allValuesFrom) r c →
    ∀ x y, I.cext r x → I.iext p x y → I.cext c y
  /-- cls-hv1 needs the forward direction, cls-hv2 the backward one. -/
  hv : ∀ r p v, I.iext (I.ι V.onProperty) r p → I.iext (I.ι V.hasValue) r v →
    ∀ x, (I.cext r x ↔ I.iext p x v)

/-- `Chain G l ms`: the RDF list whose head node is `l` in graph `G` has the
members `ms`, read through `rdf:first` / `rdf:rest` down to `rdf:nil`. A node
with two `rdf:first` values has two chains; the class condition then applies to
both, which can only strengthen the constraint on a model. -/
inductive Chain (G : List Triple) : Term → List Term → Prop
  | nil : Chain G V.nil []
  | cons {l m l' ms} :
      (⟨l, V.first, m⟩ : Triple) ∈ G → (⟨l, V.rest, l'⟩ : Triple) ∈ G →
      Chain G l' ms → Chain G l (m :: ms)

/-- `I` is a model of `G`: the conditions hold, every triple of `G` holds, and
the two list constructors mean intersection and union of their members. -/
structure Model (I : Interp) (G : List Triple) : Prop where
  conds : Conditions I
  facts : ∀ t ∈ G, I.sat t
  /-- cls-int1. -/
  int : ∀ c l ms, (⟨c, V.intersectionOf, l⟩ : Triple) ∈ G → Chain G l ms →
    ∀ x, (∀ m ∈ ms, I.cext (I.ι m) x) → I.cext (I.ι c) x
  /-- cls-uni. -/
  uni : ∀ c l ms, (⟨c, V.unionOf, l⟩ : Triple) ∈ G → Chain G l ms →
    ∀ x m, m ∈ ms → I.cext (I.ι m) x → I.cext (I.ι c) x

/-- Entailment relative to an arbitrary class of interpretations. The soundness
proof never needs more than "every interpretation in this class models `G`", so
stating it this way lets one proof serve the built-in rules and any further
assumption a certificate chooses to carry, `OOCert.EntailsR` for user-written
Horn rules among them. -/
def EntailsIn (P : Interp → Prop) (t : Triple) : Prop := ∀ I : Interp, P I → I.sat t

/-- `G ⊨ t`: every model of `G` satisfies `t`. -/
def Entails (G : List Triple) (t : Triple) : Prop := EntailsIn (fun I => Model I G) t

theorem Entails.of_mem {G : List Triple} {t : Triple} (h : t ∈ G) : Entails G t :=
  fun _ M => M.facts t h

end OOCert
