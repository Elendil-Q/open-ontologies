import Shacl.Shape

/-!
# The specification

What it means for a focus node to conform to a shape. Nothing in this file
computes anything: `Conf` is a `Prop`, the counting constraints quantify over
lists of value nodes rather than over any enumeration procedure, and the subclass
closure is an inductive relation rather than a fixpoint. `Shacl/Eval.lean` gives a
decision procedure and `Shacl/Agreement.lean` proves the two agree.

## Where this comes from

SHACL's normative validators are the prose ones in Appendix D of the
Recommendation. The document says of its own SPARQL definitions that they
"represent potential validators ... included for illustration purposes only and
have no formal status otherwise". So a direct reading of the prose is closer to the
normative text than a translation into SPARQL is, and it puts no SPARQL engine in
the trust path.

Each clause below is that prose, restated. The clauses that are NOT the prose are
called out where they occur, and there are two of them:

* `datatype` demands `lexOK l = some true`, so a literal whose datatype this
  development declines to judge (`lexOK = none`) does NOT conform. The evaluator
  refuses to answer in that case rather than reporting the violation this
  specification would license, which is the more conservative of the two.
* `klass` reads `rdfs:subClassOf*` off the data graph only. The Recommendation says
  the same, and an engine that reasons first will disagree with both.

## Why `Conf` ignores `named`

`named` carries the `sh:sourceShape` IRI for the report. A shape's identity must
not be able to change whether a node conforms, so the clause for it is a
pass-through. That is a property worth stating rather than assuming, and
`Agreement.lean` states it as `conf_named`.
-/
namespace Shacl

/-- `v` is a value node of `f` along `pa`. The whole of the path semantics covered,
in two lines. -/
def IsValue (G : Graph) : Path → Term → Term → Prop
  | .pred p, f, v => (⟨f, p, v⟩ : Triple) ∈ G
  | .inv p, f, v => (⟨v, p, f⟩ : Triple) ∈ G

/-- `rdfs:subClassOf*`, read off the data graph and nothing else. Reflexive and
transitive by construction. -/
inductive SubClassStar (G : Graph) : Term → Term → Prop
  | refl (a : Term) : SubClassStar G a a
  | step {a b c : Term} :
      (⟨a, V.subClassOf, b⟩ : Triple) ∈ G → SubClassStar G b c → SubClassStar G a c

/-- A SHACL instance of a class: a node with an `rdf:type` value that is a
subclass, reflexively and transitively, of the class. -/
def IsInstance (G : Graph) (c x : Term) : Prop :=
  ∃ t, (⟨x, V.type, t⟩ : Triple) ∈ G ∧ SubClassStar G t c

/-- **Conformance.** `Conf G s f` says focus node `f` conforms to shape `s` in
graph `G`.

The two counting clauses are the point of interest. `minCount` says there EXIST
that many distinct value nodes; `maxCount` says NO list of distinct value nodes is
longer than the bound. Both are statements about the set of value nodes with no
enumeration of it anywhere, which is what keeps this specification independent of
the evaluator that has to build one. -/
def Conf (G : Graph) : Shape → Term → Prop
  | .top, _ => True
  | .bot, _ => False
  | .klass c, f => IsInstance G c f
  | .datatype d, f => ∃ l, asLiteral f = some l ∧ l.dt = d ∧ lexOK l = some true
  | .nodeKind k, f => ∃ κ, kindOf f = some κ ∧ k.admits κ = true
  | .hasValue v, f => f = v
  | .inSet vs, f => f ∈ vs
  | .both a b, f => Conf G a f ∧ Conf G b f
  | .andC a b, f => Conf G a f ∧ Conf G b f
  | .orC a b, f => Conf G a f ∨ Conf G b f
  | .notC a, f => ¬ Conf G a f
  | .nodeC a, f => Conf G a f
  | .named _ a, f => Conf G a f
  | .forAll pa a, f => ∀ v, IsValue G pa f v → Conf G a v
  | .minCount pa n, f =>
      ∃ l : List Term, l.Nodup ∧ (∀ v ∈ l, IsValue G pa f v) ∧ n ≤ l.length
  | .maxCount pa n, f =>
      ∀ l : List Term, l.Nodup → (∀ v ∈ l, IsValue G pa f v) → l.length ≤ n
  | .hasValueOn pa v, f => IsValue G pa f v

/-! ## Targets

A target declaration selects focus nodes. These are `Prop`s for the same reason
`Conf` is: the executable computes a list and the agreement is proved. -/

/-- The focus nodes a target declaration selects. -/
inductive Target where
  | node (n : Term)
  | klass (c : Term)
  | subjectsOf (p : Term)
  | objectsOf (p : Term)
deriving DecidableEq, Repr

def IsFocus (G : Graph) : Target → Term → Prop
  | .node n, x => x = n
  | .klass c, x => IsInstance G c x
  | .subjectsOf p, x => ∃ o, (⟨x, p, o⟩ : Triple) ∈ G
  | .objectsOf p, x => ∃ s, (⟨s, p, x⟩ : Triple) ∈ G

end Shacl
