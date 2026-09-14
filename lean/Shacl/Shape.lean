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

/-- The path forms this development covers.

`sh:zeroOrMorePath` and `sh:oneOrMorePath` are NOT here, and they are the only
SHACL Core path forms that are not. Every form below is decided by a recursion that
follows the shape of the PATH and terminates because a path is a finite tree; those
two are transitive closures over the DATA GRAPH, so deciding them needs an
iteration whose bound has to be argued rather than read off the syntax. The
compiler refuses a shapes graph that uses one, so a test that needs them is
undetermined rather than wrong.

`inv` takes a predicate rather than a path. `sh:inversePath` of a compound path is
legal SHACL and the compiler refuses it, for a related reason: the value nodes of
an inverse path cannot be computed forwards from the focus node. -/
inductive Path where
  /-- A predicate path. -/
  | pred (p : Term)
  /-- `sh:inversePath` of a predicate. -/
  | inv (p : Term)
  /-- A sequence path, written as an RDF list in the shapes graph. Binary here; the
  compiler folds a longer list to the right. -/
  | seq (a b : Path)
  /-- `sh:alternativePath`. Binary here, folded the same way. -/
  | alt (a b : Path)
  /-- `sh:zeroOrOnePath` -/
  | zeroOrOne (a : Path)
deriving DecidableEq, Repr, Inhabited

/-! ## The regular-expression subset `sh:pattern` is decided over

`sh:pattern` is defined by the SPARQL `REGEX` function, which is XPath's regular
expression language, which is XML Schema's plus a few additions. Core Lean has no
regular expression engine, and writing a general one with a proof that it decides
the XPath language is a project of its own.

So this development implements a SUBSET and refuses everything outside it BY NAME,
in `Shacl/Compile.lean`. The subset is: a literal character, a character class with
ranges and an optional leading negation, the `*` quantifier, the `^` and `$`
anchors, and the `i` flag. Anything else, `+`, `?`, `{n}`, `.`, `|`, grouping, a
backreference, an escape of any kind, is a compile error naming the construct, so a
shapes graph that uses one is undetermined rather than answered wrongly.

**Every element of the subset matches exactly one character.** That is what makes
the matcher below a structural recursion over the pattern with no backtracking
budget and no fuel: `star` is decided by trying each split point of the remaining
string, and the recursion moves to a shorter list of items each time.

A pattern is matched against the string a term denotes, by SEARCH rather than by
full match, which is what SPARQL `REGEX` does: an unanchored pattern matches when
SOME substring matches. -/

/-- How many times one element may repeat. -/
inductive Quant where
  | one
  | star
deriving DecidableEq, Repr, Inhabited

/-- One element of a pattern: a character class and a quantifier. A literal
character is the class holding the one range from it to itself. -/
structure Item where
  neg : Bool
  ranges : List (Char × Char)
  quant : Quant
deriving DecidableEq, Repr, Inhabited

def inRanges (rs : List (Char × Char)) (c : Char) : Bool :=
  rs.any (fun r => r.1.toNat ≤ c.toNat && c.toNat ≤ r.2.toNat)

/-- Does this element admit this character?

The `i` flag is applied to the INPUT character: the class is tried against both its
lower and its upper case. For a class of ASCII letters and ASCII letter ranges that
is exactly what XPath's `i` flag does. For a class whose range straddles a case
boundary it is not, and this matcher does not pretend otherwise; the suite's only
uses of the flag are the literal patterns `Aldi` and `joh`. -/
def itemAdmits (fold : Bool) (it : Item) (c : Char) : Bool :=
  let hit :=
    if fold then inRanges it.ranges c.toLower || inRanges it.ranges c.toUpper
    else inRanges it.ranges c
  if it.neg then !hit else hit

structure Regex where
  fold : Bool
  anchorStart : Bool
  anchorEnd : Bool
  items : List Item
deriving DecidableEq, Repr, Inhabited

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
  /-- `sh:minInclusive`. The parameter's value is carried as a term and compared
  by VALUE with `cmpTerms`, not by spelling. -/
  | minInclusive (c : Term)
  /-- `sh:maxInclusive` -/
  | maxInclusive (c : Term)
  /-- `sh:minExclusive` -/
  | minExclusive (c : Term)
  /-- `sh:maxExclusive` -/
  | maxExclusive (c : Term)
  /-- `sh:minLength` -/
  | minLength (n : Nat)
  /-- `sh:maxLength` -/
  | maxLength (n : Nat)
  /-- `sh:languageIn` -/
  | languageIn (tags : List String)
  /-- `sh:pattern`, with `sh:flags` folded into the `Regex`. -/
  | pattern (re : Regex)
  /-- `sh:equals`. The `Option Path` is `none` on a node shape, where the set of
  value nodes is the focus node on its own, and `some pa` on a property shape. The
  four property-pair constraints and `sh:uniqueLang` all take that shape, which is
  why they carry an `Option Path` rather than a `Path`: the suite puts `sh:equals`
  and `sh:disjoint` on node shapes and a `Path` could not express that. -/
  | equals (pa : Option Path) (q : Term)
  /-- `sh:disjoint` -/
  | disjoint (pa : Option Path) (q : Term)
  /-- `sh:lessThan` -/
  | lessThan (pa : Option Path) (q : Term)
  /-- `sh:lessThanOrEquals` -/
  | lessThanOrEq (pa : Option Path) (q : Term)
  /-- `sh:uniqueLang` -/
  | uniqueLang (pa : Option Path)
  /-- `sh:qualifiedMinCount`: at least `n` value nodes along `pa` conform to `q`.

  `q` is not only the `sh:qualifiedValueShape`. When
  `sh:qualifiedValueShapesDisjoint` is true the compiler conjoins the negation of
  every SIBLING shape into `q`, so the disjointness is expressed with `sh:and` and
  `sh:not`, whose semantics `Spec.lean` already gives, rather than with a clause of
  its own. The sibling lookup needs the parent shape and is therefore a compile-time
  question, which is where it belongs: the evaluator never re-reads the shapes
  graph. -/
  | qualifiedMin (pa : Path) (q : Shape) (n : Nat)
  /-- `sh:qualifiedMaxCount`, with `q` built the same way. -/
  | qualifiedMax (pa : Path) (q : Shape) (n : Nat)
  /-- `sh:closed`. The allowed predicates are computed by the compiler from the
  `sh:path` of every property shape the closed shape references plus
  `sh:ignoredProperties`, so the evaluator receives a list and never re-reads the
  shapes graph. -/
  | closed (allowed : List Term)
  /-- Evaluate the inner shape and report ONE result carrying this constraint
  component when it fails, discarding the inner results.

  `nodeC` is the same idea with `sh:NodeConstraintComponent` fixed. This one
  carries its own component, which is what lets `sh:xone` be COMPILED into the
  constructors already here, with `sh:or`, `sh:and` and `sh:not` doing the work,
  and still report `sh:XoneConstraintComponent` as the Recommendation requires. -/
  | report (comp : Term) (a : Shape)
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
def minInclusive : Term := "<http://www.w3.org/ns/shacl#MinInclusiveConstraintComponent>"
def maxInclusive : Term := "<http://www.w3.org/ns/shacl#MaxInclusiveConstraintComponent>"
def minExclusive : Term := "<http://www.w3.org/ns/shacl#MinExclusiveConstraintComponent>"
def maxExclusive : Term := "<http://www.w3.org/ns/shacl#MaxExclusiveConstraintComponent>"
def minLength : Term := "<http://www.w3.org/ns/shacl#MinLengthConstraintComponent>"
def maxLength : Term := "<http://www.w3.org/ns/shacl#MaxLengthConstraintComponent>"
def languageIn : Term := "<http://www.w3.org/ns/shacl#LanguageInConstraintComponent>"
def pattern : Term := "<http://www.w3.org/ns/shacl#PatternConstraintComponent>"
def equals : Term := "<http://www.w3.org/ns/shacl#EqualsConstraintComponent>"
def disjoint : Term := "<http://www.w3.org/ns/shacl#DisjointConstraintComponent>"
def lessThan : Term := "<http://www.w3.org/ns/shacl#LessThanConstraintComponent>"
def lessThanOrEq : Term := "<http://www.w3.org/ns/shacl#LessThanOrEqualsConstraintComponent>"
def uniqueLang : Term := "<http://www.w3.org/ns/shacl#UniqueLangConstraintComponent>"
def closed : Term := "<http://www.w3.org/ns/shacl#ClosedConstraintComponent>"
def xone : Term := "<http://www.w3.org/ns/shacl#XoneConstraintComponent>"
def qualifiedMin : Term := "<http://www.w3.org/ns/shacl#QualifiedMinCountConstraintComponent>"
def qualifiedMax : Term := "<http://www.w3.org/ns/shacl#QualifiedMaxCountConstraintComponent>"

/-- Not a SHACL IRI. `bot` has no counterpart in the Recommendation because it has
no counterpart in a shapes graph; it exists as the unit of `orC` and its result is
always discarded by the enclosing `orC`. Giving it a marker rather than borrowing
`sh:OrConstraintComponent` keeps a fabricated component out of any report that
somehow did escape. -/
def bot : Term := "<urn:x-oo-shacl-core:EmptyDisjunction>"

end C

end Shacl
