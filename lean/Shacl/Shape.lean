import Shacl.Term

/-!
# Shapes as a Lean datatype

A SHACL shapes graph is RDF. This module is the abstract syntax a shapes graph is
COMPILED into, and the compiler (`Shacl/Compile.lean`) is outside the theorem: it
either produces one of these shapes or refuses, and a refusal is a verdict of
"undetermined", never a pass. Everything downstream of this type is proved.

## Why an inductive type, and what that decides

SHACL shapes in RDF can refer to each other in a cycle. The Recommendation is
explicit that it "does not define the semantics of recursive shape definitions",
so there is nothing to be faithful to. Making `Shape` an inductive type settles the
question by construction: a cyclic shapes graph cannot be compiled into one, the
compiler refuses it, and the run is undetermined. That is the same answer the
Working Group gives, arrived at in a way a checker can act on.

## Transparent and opaque conjunction

SHACL has two conjunctions and they report differently, so they are two
constructors here.

* The constraints of one shape are conjoined and each reports its OWN validation
  result. That is `both`, and it produces the union of its two sides' results.
* `sh:and` conjoins shapes and reports ONE result, with
  `sh:AndConstraintComponent`, saying nothing about which conjunct failed. That is
  `andC`.

`sh:or`, `sh:not` and `sh:node` are opaque in the same way: one result each, and
the inner results are discarded. `sh:property` is transparent, which is why it has
no constructor of its own: a property shape compiles to `named PS (both ...)` and
its results surface at the parent unchanged, exactly as the Recommendation
describes.

## What `named` is for

`sh:sourceShape` on a validation result names the shape the constraint was written
on, which is not the shape being evaluated at that moment: a property shape's
constraints report the property shape, not the node shape that referenced it.
`named` carries that IRI down the tree. It has no effect on conformance, and
`Spec.lean` ignores it, which is the point: a shape's identity is bookkeeping for
the report and must not be able to change a verdict.
-/
namespace Shacl

/-- The two path forms this development covers.

`sh:path` in SHACL Core also has sequence, alternative, zero-or-more, one-or-more
and zero-or-one forms. They are not here. The compiler refuses a shapes graph that
uses one, so a test that needs them is undetermined rather than wrong. -/
inductive Path where
  | pred (p : Term)
  | inv (p : Term)
deriving DecidableEq, Repr

/-- Does this triple contribute a value node for focus node `f` along this path? -/
def Path.sel (pa : Path) (f : Term) (t : Triple) : Bool :=
  match pa with
  | .pred p => t.s == f && t.p == p
  | .inv p => t.p == p && t.o == f

/-- The value node a selected triple contributes. -/
def Path.val (pa : Path) (t : Triple) : Term :=
  match pa with
  | .pred _ => t.o
  | .inv _ => t.s

/-- The constraint components covered, plus the two units.

Constructors are named after the SHACL parameter they come from. `top` and `bot`
are the units of `andC` and `orC`; a compiler that folds a one-element `sh:or`
list needs `bot`, and nothing else produces it. -/
inductive Shape where
  /-- Conforms always. The unit of `andC`. -/
  | top
  /-- Conforms never. The unit of `orC`, and unreachable from a shapes graph whose
  `sh:or` lists are non-empty. -/
  | bot
  /-- `sh:class` -/
  | klass (c : Term)
  /-- `sh:datatype` -/
  | datatype (d : Term)
  /-- `sh:nodeKind` -/
  | nodeKind (k : NodeKind)
  /-- `sh:hasValue`, on a node shape: the focus node itself must be this term. -/
  | hasValue (v : Term)
  /-- `sh:in` -/
  | inSet (vs : List Term)
  /-- The implicit conjunction of one shape's constraints. Transparent: the
  results of both sides are reported. -/
  | both (a b : Shape)
  /-- `sh:and`. Opaque: one result. -/
  | andC (a b : Shape)
  /-- `sh:or`. Opaque: one result. -/
  | orC (a b : Shape)
  /-- `sh:not`. Opaque: one result. -/
  | notC (a : Shape)
  /-- `sh:node`. Opaque: one result, per the Recommendation, which says the nested
  shape's own results are not reported. -/
  | nodeC (a : Shape)
  /-- The value-node constraints of a property shape: every value node on the path
  must conform to the inner shape. -/
  | forAll (pa : Path) (a : Shape)
  /-- `sh:minCount` -/
  | minCount (pa : Path) (n : Nat)
  /-- `sh:maxCount` -/
  | maxCount (pa : Path) (n : Nat)
  /-- `sh:hasValue` on a property shape: SOME value node is this term. A set
  constraint, not a value-node constraint, which is why it is a separate
  constructor from `hasValue`. -/
  | hasValueOn (pa : Path) (v : Term)
  /-- Sets `sh:sourceShape` for everything underneath. No effect on conformance. -/
  | named (src : Term) (a : Shape)
deriving Repr, Inhabited

/-! ## The constraint component IRIs a result carries -/
namespace C

def klass : Term := "<http://www.w3.org/ns/shacl#ClassConstraintComponent>"
def datatype : Term := "<http://www.w3.org/ns/shacl#DatatypeConstraintComponent>"
def nodeKind : Term := "<http://www.w3.org/ns/shacl#NodeKindConstraintComponent>"
def hasValue : Term := "<http://www.w3.org/ns/shacl#HasValueConstraintComponent>"
def inSet : Term := "<http://www.w3.org/ns/shacl#InConstraintComponent>"
def andC : Term := "<http://www.w3.org/ns/shacl#AndConstraintComponent>"
def orC : Term := "<http://www.w3.org/ns/shacl#OrConstraintComponent>"
def notC : Term := "<http://www.w3.org/ns/shacl#NotConstraintComponent>"
def nodeC : Term := "<http://www.w3.org/ns/shacl#NodeConstraintComponent>"
def minCount : Term := "<http://www.w3.org/ns/shacl#MinCountConstraintComponent>"
def maxCount : Term := "<http://www.w3.org/ns/shacl#MaxCountConstraintComponent>"

/-- Not a SHACL IRI. `bot` has no counterpart in the Recommendation because it has
no counterpart in a shapes graph; it exists as the unit of `orC` and its result is
always discarded by the enclosing `orC`. Giving it a marker rather than borrowing
`sh:OrConstraintComponent` keeps a fabricated component out of any report that
somehow did escape. -/
def bot : Term := "<urn:x-oo-shacl-core:EmptyDisjunction>"

end C

end Shacl
