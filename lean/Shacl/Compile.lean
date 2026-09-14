import Shacl.Report

/-!
# Compiling a shapes graph into shapes

This module turns RDF into the `Shape` datatype the proved evaluator consumes. It
is NOT part of any theorem, and that is the design, not an omission: a compiler
from RDF into an abstract syntax is a parser, and the project's existing position on
parsers is that a parse error rejects rather than accepts.

## It fails closed, and that is the only reason it can be trusted at all

The dangerous failure for a validator is to ignore a constraint it does not
understand and report `conforms`. So:

* **Every `sh:` predicate on every shape the compiler walks must be known.** One it
  has not implemented is an error naming the predicate, not a silently dropped
  constraint. `ignoredParams` lists the handful that carry no conformance meaning,
  each with a reason.
* **A shapes graph that defines a constraint COMPONENT is refused outright.** A
  custom component introduces parameters in the user's own namespace, so the
  `sh:` check above cannot see them, and a shape using one would look empty. The
  guard is a scan for `sh:parameter`, `sh:validator`, `sh:nodeValidator`,
  `sh:propertyValidator`, `sh:sparql` and `rdf:type sh:ConstraintComponent`
  anywhere in the shapes graph.
* **Recursion is refused.** SHACL says it "does not define the semantics of
  recursive shape definitions". `Shape` is an inductive type, so a cyclic shapes
  graph exhausts the nesting budget and is reported as recursive.
* **A malformed shape is refused**, not guessed at: two `sh:path` values, a
  `sh:minCount` on a shape with no path, an RDF list that does not end at
  `rdf:nil`.

Every refusal comes out as `undetermined` in the report and in the conformance
measurement, which counts it separately from a pass and from a failure.

## What is deliberately ignored, and why it is safe here

`sh:message`, `sh:name`, `sh:description`, `sh:order`, `sh:group` and
`sh:defaultValue` carry no conformance meaning at all.

`sh:severity` does carry meaning, for `sh:resultSeverity` in the report. It is
ignored, so every result this validator produces is a violation with no severity
recorded. That is a real gap and it is named here rather than discovered: a report
consumer that acts on severity must not use this validator.
-/
namespace Shacl.Compile

open Shacl

/-! ## Vocabulary -/

namespace SH
def ns : String := "http://www.w3.org/ns/shacl#"
def iri (l : String) : Term := "<" ++ ns ++ l ++ ">"

def NodeShape : Term := iri "NodeShape"
def PropertyShape : Term := iri "PropertyShape"
def ConstraintComponent : Term := iri "ConstraintComponent"

def targetNode : Term := iri "targetNode"
def targetClass : Term := iri "targetClass"
def targetSubjectsOf : Term := iri "targetSubjectsOf"
def targetObjectsOf : Term := iri "targetObjectsOf"

def path : Term := iri "path"
def inversePath : Term := iri "inversePath"
def alternativePath : Term := iri "alternativePath"
def zeroOrMorePath : Term := iri "zeroOrMorePath"
def oneOrMorePath : Term := iri "oneOrMorePath"
def zeroOrOnePath : Term := iri "zeroOrOnePath"

def klass : Term := iri "class"
def datatype : Term := iri "datatype"
def nodeKind : Term := iri "nodeKind"
def minCount : Term := iri "minCount"
def maxCount : Term := iri "maxCount"
def hasValue : Term := iri "hasValue"
def inList : Term := iri "in"
def notC : Term := iri "not"
def andC : Term := iri "and"
def orC : Term := iri "or"
def nodeC : Term := iri "node"
def property : Term := iri "property"
def deactivated : Term := iri "deactivated"

def message : Term := iri "message"
def name : Term := iri "name"
def description : Term := iri "description"
def order : Term := iri "order"
def group : Term := iri "group"
def defaultValue : Term := iri "defaultValue"
def severity : Term := iri "severity"

def parameter : Term := iri "parameter"
def validator : Term := iri "validator"
def nodeValidator : Term := iri "nodeValidator"
def propertyValidator : Term := iri "propertyValidator"
def sparql : Term := iri "sparql"

def kIRI : Term := iri "IRI"
def kBlankNode : Term := iri "BlankNode"
def kLiteral : Term := iri "Literal"
def kBlankNodeOrIRI : Term := iri "BlankNodeOrIRI"
def kBlankNodeOrLiteral : Term := iri "BlankNodeOrLiteral"
def kIRIOrLiteral : Term := iri "IRIOrLiteral"

end SH

/-- Parameters with a conformance meaning that this development implements. -/
def knownParams : List Term :=
  [ SH.path, SH.klass, SH.datatype, SH.nodeKind, SH.minCount, SH.maxCount,
    SH.hasValue, SH.inList, SH.notC, SH.andC, SH.orC, SH.nodeC, SH.property,
    SH.deactivated, SH.targetNode, SH.targetClass, SH.targetSubjectsOf,
    SH.targetObjectsOf ]

/-- Parameters with no effect on the verdict or on the result fields this
validator reports. `sh:severity` is the one that is a real gap; see the module
header. -/
def ignoredParams : List Term :=
  [ SH.message, SH.name, SH.description, SH.order, SH.group, SH.defaultValue,
    SH.severity ]

def isShaclPred (p : Term) : Bool := p.startsWith ("<" ++ SH.ns)

/-! ## Reading the graph -/

def objectsOf (G : Graph) (s p : Term) : List Term :=
  (G.filter (fun t => t.s == s && t.p == p)).map Triple.o

def predsOf (G : Graph) (s : Term) : List Term :=
  dedup ((G.filter (fun t => t.s == s)).map Triple.p)

def hasTriple (G : Graph) (s p o : Term) : Bool :=
  G.any (fun t => t.s == s && t.p == p && t.o == o)

/-- An RDF list, or an error naming where it went wrong. -/
def readList (G : Graph) : Nat → Term → Except String (List Term)
  | 0, node => .error s!"RDF list at {node} is longer than the shapes graph, so it is cyclic"
  | fuel + 1, node =>
      if node == V.nil then .ok []
      else
        match objectsOf G node V.first, objectsOf G node V.rest with
        | [f], [r] => do
            let tl ← readList G fuel r
            .ok (f :: tl)
        | _, _ => .error s!"malformed RDF list at {node}: expected one rdf:first and one rdf:rest"

/-- The natural number a literal denotes, for `sh:minCount` and `sh:maxCount`. -/
def readNat (o : Term) : Except String Nat :=
  match asLiteral o with
  | some l =>
      if isDigits l.lex.toList then .ok (natOfDigits l.lex.toList)
      else .error s!"{o} is not a non-negative integer literal"
  | none => .error s!"{o} is not a literal, so it cannot be a count"

def readNodeKind (o : Term) : Except String NodeKind :=
  if o == SH.kIRI then .ok .iri
  else if o == SH.kBlankNode then .ok .blankNode
  else if o == SH.kLiteral then .ok .literal
  else if o == SH.kBlankNodeOrIRI then .ok .blankNodeOrIRI
  else if o == SH.kBlankNodeOrLiteral then .ok .blankNodeOrLiteral
  else if o == SH.kIRIOrLiteral then .ok .iriOrLiteral
  else .error s!"{o} is not one of the six sh:nodeKind values"

/-- The path forms present on a blank path node, named. -/
def pathForms (G : Graph) (node : Term) : List String :=
  (if (objectsOf G node SH.inversePath).isEmpty then [] else ["sh:inversePath"]) ++
  (if (objectsOf G node SH.alternativePath).isEmpty then [] else ["sh:alternativePath"]) ++
  (if (objectsOf G node SH.zeroOrMorePath).isEmpty then [] else ["sh:zeroOrMorePath"]) ++
  (if (objectsOf G node SH.oneOrMorePath).isEmpty then [] else ["sh:oneOrMorePath"]) ++
  (if (objectsOf G node SH.zeroOrOnePath).isEmpty then [] else ["sh:zeroOrOnePath"]) ++
  (if (objectsOf G node V.first).isEmpty then [] else ["a sequence path"])

/-- A path, or an error naming the path form that was found. Only a predicate path
and `sh:inversePath` of a predicate are covered.

A node carrying TWO path forms is refused rather than read as either. SHACL
requires a well-formed path node to have exactly one form, and the suite's
`core/path/path-strange-001` is a node that is simultaneously a sequence path and
an inverse path. Reading it as the first form the code happens to check is how this
compiler produced its one wrong answer against the suite: it chose the inverse
reading and blamed the wrong node. Refusing an ill-formed shapes graph and saying
so is the answer that cannot be wrong. -/
def compilePath (G : Graph) (node : Term) : Except String Path :=
  if isIriSpelling node then .ok (.pred node)
  else
    match pathForms G node with
    | [] => .error s!"{node} is not a path this development understands"
    | ["sh:inversePath"] =>
        match objectsOf G node SH.inversePath with
        | [inner] =>
            if isIriSpelling inner then .ok (.inv inner)
            else .error "sh:inversePath of something other than a predicate is not implemented"
        | _ => .error "more than one sh:inversePath on a path node"
    | [one] => .error s!"{one} is not implemented"
    | many =>
        .error s!"the path node {node} carries more than one path form \
          ({String.intercalate ", " many}); SHACL allows exactly one, so this shapes graph is \
          ill formed and no reading of it is chosen"

def isDeactivated (G : Graph) (node : Term) : Bool :=
  (objectsOf G node SH.deactivated).any fun o =>
    match asLiteral o with
    | some l => l.lex == "true"
    | none => false

/-- Wrap a value-node constraint for the shape it sits on: on a property shape it
applies to every value node, on a node shape to the focus node itself. -/
def wrapV : Option Path → Shape → Shape
  | none, s => s
  | some pa, s => .forAll pa s

def foldAnd : List Shape → Shape
  | [] => .top
  | s :: rest => .andC s (foldAnd rest)

def foldOr : List Shape → Shape
  | [] => .bot
  | s :: rest => .orC s (foldOr rest)

/-- Compile one shape node. `fuel` bounds the nesting; one level of nesting always
consumes at least one triple of the shapes graph, so a budget of `|G| + 1`
exhausts only on a cycle. -/
def compileShape (G : Graph) : Nat → Term → Except String Shape
  | 0, node =>
      .error s!"shape nesting at {node} exceeds the size of the shapes graph, so the shapes \
        are recursive; SHACL does not define the semantics of recursive shapes"
  | fuel + 1, node => do
      for p in predsOf G node do
        if isShaclPred p && !(knownParams.contains p) && !(ignoredParams.contains p) then
          throw s!"{node}: the constraint parameter {p} is not implemented"
      if isDeactivated G node then
        return .top
      let pathOpt : Option Path ← (
        match objectsOf G node SH.path with
        | [] => pure none
        | [po] => do
            let pa ← compilePath G po
            pure (some pa)
        | _ => throw s!"{node}: more than one sh:path")
      let mut acc : Shape := .top
      for o in objectsOf G node SH.klass do
        acc := .both acc (wrapV pathOpt (.klass o))
      for o in objectsOf G node SH.datatype do
        acc := .both acc (wrapV pathOpt (.datatype o))
      for o in objectsOf G node SH.nodeKind do
        let k ← readNodeKind o
        acc := .both acc (wrapV pathOpt (.nodeKind k))
      for o in objectsOf G node SH.inList do
        let vs ← readList G (G.length + 1) o
        acc := .both acc (wrapV pathOpt (.inSet vs))
      for o in objectsOf G node SH.notC do
        let s ← compileShape G fuel o
        acc := .both acc (wrapV pathOpt (.notC s))
      for o in objectsOf G node SH.nodeC do
        let s ← compileShape G fuel o
        acc := .both acc (wrapV pathOpt (.nodeC s))
      for o in objectsOf G node SH.andC do
        let members ← readList G (G.length + 1) o
        let mut ss : List Shape := []
        for m in members do
          ss := ss ++ [← compileShape G fuel m]
        acc := .both acc (wrapV pathOpt (foldAnd ss))
      for o in objectsOf G node SH.orC do
        let members ← readList G (G.length + 1) o
        let mut ss : List Shape := []
        for m in members do
          ss := ss ++ [← compileShape G fuel m]
        acc := .both acc (wrapV pathOpt (foldOr ss))
      for o in objectsOf G node SH.property do
        let s ← compileShape G fuel o
        acc := .both acc (wrapV pathOpt s)
      for o in objectsOf G node SH.hasValue do
        match pathOpt with
        | none => acc := .both acc (.hasValue o)
        | some pa => acc := .both acc (.hasValueOn pa o)
      for o in objectsOf G node SH.minCount do
        let n ← readNat o
        match pathOpt with
        | none => throw s!"{node}: sh:minCount on a shape with no sh:path"
        | some pa => acc := .both acc (.minCount pa n)
      for o in objectsOf G node SH.maxCount do
        let n ← readNat o
        match pathOpt with
        | none => throw s!"{node}: sh:maxCount on a shape with no sh:path"
        | some pa => acc := .both acc (.maxCount pa n)
      return .named node acc

/-! ## Targets -/

def targetsOf (G : Graph) (node : Term) : List Target :=
  let explicit :=
    (objectsOf G node SH.targetNode).map Target.node ++
    (objectsOf G node SH.targetClass).map Target.klass ++
    (objectsOf G node SH.targetSubjectsOf).map Target.subjectsOf ++
    (objectsOf G node SH.targetObjectsOf).map Target.objectsOf
  -- The implicit class target: a node that is both a shape and a class targets its
  -- own instances.
  let isShape :=
    hasTriple G node V.type SH.NodeShape || hasTriple G node V.type SH.PropertyShape
  if isShape && hasTriple G node V.type V.rdfsClass then
    explicit ++ [Target.klass node]
  else explicit

/-- Every node in the shapes graph that carries at least one target. -/
def targetedNodes (G : Graph) : List Term :=
  dedup ((G.filterMap fun t =>
    if t.p == SH.targetNode || t.p == SH.targetClass || t.p == SH.targetSubjectsOf
       || t.p == SH.targetObjectsOf then some t.s
    else if t.p == V.type && t.o == V.rdfsClass then
      if hasTriple G t.s V.type SH.NodeShape || hasTriple G t.s V.type SH.PropertyShape
      then some t.s else none
    else none))

/-- The global guard: a shapes graph that defines its own constraint components
introduces parameters outside the `sh:` namespace, so the per-shape check cannot
see them and a shape using one would look empty. Refuse the whole graph. -/
def extensionMechanism (G : Graph) : Option String :=
  let hit := G.find? fun t =>
    t.p == SH.parameter || t.p == SH.validator || t.p == SH.nodeValidator
      || t.p == SH.propertyValidator || t.p == SH.sparql
      || (t.p == V.type && t.o == SH.ConstraintComponent)
  match hit with
  | some t =>
      some s!"the shapes graph uses the SHACL extension mechanism ({t.p} on {t.s}); a \
        constraint component can declare parameters outside the sh: namespace, which this \
        compiler cannot detect, so the whole graph is refused rather than partly ignored"
  | none => none

/-- Compile a whole shapes graph into declarations, or refuse with a reason. -/
def compileShapes (G : Graph) : Except String (List ShapeDecl) := do
  match extensionMechanism G with
  | some why => throw why
  | none => pure ()
  let mut out : Array ShapeDecl := #[]
  for node in targetedNodes G do
    if isDeactivated G node then
      continue
    let s ← compileShape G (G.length + 1) node
    out := out.push { id := node, targets := targetsOf G node, shape := s }
  return out.toList

end Shacl.Compile
