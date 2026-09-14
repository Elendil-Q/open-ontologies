/-!
# The fragment, the interpretation, and the file format

This development certifies the POSITIVE answers of the SHIQ tableaux reasoner in
`src/tableaux.rs`. When that reasoner says a class is satisfiable, or that an ontology is
consistent, it can hand over the finite interpretation it built. `Dl/Check.lean` decides
whether that interpretation really satisfies the axioms, and `Dl.satisfiable_of_checkModel`
turns an accepted interpretation into `∃ I, I ⊨ A`.

The negative answer is not certified and is not meant to be. "Unsatisfiable" needs a closed
tableau with every branch, every clash and a blocking argument, which is a proof-checking
problem rather than a model-checking one. Nothing here says anything about it, and the
reasoner keeps emitting bare unsatisfiability verdicts.

## What is in the fragment

Atomic concepts, `⊤`, `⊥`, negation, binary conjunction and disjunction, `∃R.C`, `∀R.C`,
and the qualified number restrictions `≥n R.C` and `≤n R.C`. On the axiom side: subclass,
disjointness, `rdfs:domain`, `rdfs:range`, role inclusion, transitive roles, symmetric
roles, inverse roles, inverse-functional roles, class assertions, role assertions, named
individuals, and a non-emptiness claim (`nonempty C`, which is how "the reasoner said C is
satisfiable" becomes something a model can be checked against).

`n`-ary conjunction and disjunction are folded into the binary constructors by the emitter.
Functional roles are emitted as `⊤ ⊑ ≤1 R.⊤` and need no constructor of their own.

## What is NOT in the fragment, and is therefore never emitted

* Nominals (`owl:oneOf`, `owl:hasValue` as `{a}`). `src/tableaux.rs` has no nominal
  constructor either; it approximates `owl:hasValue` by an atomic concept named after the
  individual, and that approximation is emitted as the atom it is, not as a nominal.
* Datatypes, data properties and literal values. The reasoner never puts them on a tableau
  edge and this file has no syntax for them.
* `owl:sameAs`, `owl:differentFrom` and the unique name assumption. A model here is free to
  send two individual IRIs to the same domain element.
* Role chains, reflexive, irreflexive and asymmetric roles, `owl:disjointUnionOf` and
  `owl:AllDisjointClasses` as a single axiom (pairwise disjointness is emitted instead).
* Anything the OWL parser in `src/tableaux.rs` does not recognise. The parser is OUTSIDE
  this theorem, exactly as the N-Triples parser is outside `Shacl.validate_spec`. What is
  certified is that the emitted interpretation satisfies the emitted axioms. Whether the
  emitted axioms are the ontology is a separate question, and a reader must not read the
  exit code as an answer to it.

## The interpretation

A finite interpretation is a domain given as a list of element names, an extension for each
atomic concept, a successor list for each role and each element, and a denotation for each
individual IRI. The extension maps are total functions on `String` because that is what a
lookup table compiles to; `Dl.WellFormed` is what confines them to the domain, and every
theorem here carries that hypothesis.

## The file format

Two tab-separated files, both written by `src/tableaux.rs`.

`axioms.tsv`, one axiom per line. Field 1 is the keyword, the rest are its arguments:

```
sub        CONCEPT  CONCEPT     C ⊑ D
disjoint   CONCEPT  CONCEPT     C ⊓ D ⊑ ⊥
domain     ROLE     CONCEPT     ∃R.⊤ ⊑ C
range      ROLE     CONCEPT     ⊤ ⊑ ∀R.C
subrole    ROLE     ROLE        R ⊑ S
trans      ROLE                 R transitive
sym        ROLE                 R symmetric
inv        ROLE     ROLE        R ≡ S⁻
invfunc    ROLE                 R inverse functional
inst       IND      CONCEPT     C(a)
rel        IND      ROLE  IND   R(a, b)
indiv      IND                  a is a named individual
nonempty   CONCEPT              C^I ≠ ∅, the satisfiability claim
```

A CONCEPT is a SPACE-separated prefix token stream, with no parentheses and no arity
ambiguity, because every constructor has a fixed arity:

```
top | bot | atom IRI | not C | and C C | or C C
| some ROLE C | all ROLE C | min N ROLE C | max N ROLE C
```

IRIs keep their N-Triples spelling `<...>`, which contains no space and no tab, so both
splits are exact. `model.tsv`, one fact per line:

```
domain  ELEM               ELEM is a domain element
class   IRI   ELEM         ELEM is in the extension of the atomic concept IRI
edge    ELEM  ROLE  ELEM   the pair is in the extension of ROLE
ind     IRI   ELEM         the individual IRI denotes ELEM
```

Element names are opaque strings. The emitter uses `n0`, `n1`, ... after the tableau's
node identifiers, but nothing here depends on that.
-/
namespace Dl

/-- An IRI in its N-Triples spelling, or an opaque domain element name. The checker never
looks inside one; two are the same when the strings are the same. -/
abbrev Name := String

/-- A concept of the covered fragment. Conjunction and disjunction are binary: the emitter
folds the `n`-ary OWL constructors, which keeps this type free of the nested `List Concept`
that would otherwise complicate every recursion in `Dl/Check.lean`. -/
inductive Concept where
  | top
  | bot
  | atom (a : Name)
  | neg (c : Concept)
  | and (c d : Concept)
  | or (c d : Concept)
  | ex (r : Name) (c : Concept)
  | all (r : Name) (c : Concept)
  | min (n : Nat) (r : Name) (c : Concept)
  | max (n : Nat) (r : Name) (c : Concept)
deriving DecidableEq, Repr, Inhabited

/-- An axiom of the covered fragment. See the file format table above for the
correspondence with the OWL constructs the reasoner parses. -/
inductive Axiom where
  | sub (c d : Concept)
  | disjoint (c d : Concept)
  | dom (r : Name) (c : Concept)
  | rng (r : Name) (c : Concept)
  | subrole (r s : Name)
  | trans (r : Name)
  | sym (r : Name)
  | inv (r s : Name)
  | invfunc (r : Name)
  | inst (a : Name) (c : Concept)
  | rel (a r b : Name)
  | indiv (a : Name)
  | nonempty (c : Concept)
deriving DecidableEq, Repr, Inhabited

/-- A finite interpretation.

`dom` is the carrier. `cext a` is the extension of the atomic concept `a`, `rext r x` the
list of `r`-successors of `x`, and `ind a` the element the individual IRI `a` denotes. The
three are total functions rather than association lists so that a lookup costs one hash
rather than a scan of every fact in the file; `WellFormed` is what ties them back to
`dom`. -/
structure Interp where
  dom : List Name
  cext : Name → List Name
  rext : Name → Name → List Name
  ind : Name → Name

/-! ## The vocabulary an axiom set mentions

`WellFormed` has to say that the interpretation stays inside its domain. The extension maps
are total on `String`, so that cannot be stated for every name; it is stated for the names
the axiom set actually mentions, which is the only vocabulary any of the semantic clauses
ever looks at. These three functions collect them. -/

/-- The atomic concept names occurring in a concept. -/
def Concept.atoms : Concept → List Name
  | .top | .bot => []
  | .atom a => [a]
  | .neg c => c.atoms
  | .and c d | .or c d => c.atoms ++ d.atoms
  | .ex _ c | .all _ c => c.atoms
  | .min _ _ c | .max _ _ c => c.atoms

/-- The role names occurring in a concept. -/
def Concept.roles : Concept → List Name
  | .top | .bot | .atom _ => []
  | .neg c => c.roles
  | .and c d | .or c d => c.roles ++ d.roles
  | .ex r c | .all r c => r :: c.roles
  | .min _ r c | .max _ r c => r :: c.roles

/-- The atomic concept names an axiom mentions. -/
def Axiom.atoms : Axiom → List Name
  | .sub c d | .disjoint c d => c.atoms ++ d.atoms
  | .dom _ c | .rng _ c => c.atoms
  | .inst _ c | .nonempty c => c.atoms
  | .subrole .. | .trans _ | .sym _ | .inv .. | .invfunc _ | .rel .. | .indiv _ => []

/-- The role names an axiom mentions. -/
def Axiom.roles : Axiom → List Name
  | .sub c d | .disjoint c d => c.roles ++ d.roles
  | .dom r c | .rng r c => r :: c.roles
  | .inst _ c | .nonempty c => c.roles
  | .subrole r s | .inv r s => [r, s]
  | .trans r | .sym r | .invfunc r => [r]
  | .rel _ r _ => [r]
  | .indiv _ => []

/-- The individual IRIs an axiom mentions. -/
def Axiom.inds : Axiom → List Name
  | .inst a _ | .indiv a => [a]
  | .rel a _ b => [a, b]
  | _ => []

/-- Every atomic concept name the axiom set mentions. -/
def atomNames (A : List Axiom) : List Name := A.flatMap Axiom.atoms

/-- Every role name the axiom set mentions. -/
def roleNames (A : List Axiom) : List Name := A.flatMap Axiom.roles

/-- Every individual IRI the axiom set mentions. -/
def indNames (A : List Axiom) : List Name := A.flatMap Axiom.inds

end Dl
