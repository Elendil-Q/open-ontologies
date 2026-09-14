/-!
# The fragment, the finite model, and the two file formats

This development certifies the SATISFIABILITY answers of an external SAT/SMT solver or finite
model finder run over the first-order export in `src/tptp.rs`. When Z3 or Mace4 says a problem
is satisfiable and hands back the finite structure it built, `Fol/Check.lean` decides whether
that structure really satisfies every formula of the problem, and `Fol.satisfiable_of_check`
turns an accepted structure into `∃ M e, ∀ g ∈ Γ, holds M e g`.

The UNSATISFIABILITY answer is not certified and cannot be. Checking a superposition or CDCL(T)
refutation needs a verified calculus with unification and theory lemmas, which does not exist in
core Lean; decision 0005 rules that an automated prover's verdict is an oracle opinion and this
layer does not disturb that ruling. What it adds is the observation that the two directions are
not symmetric. A refutation is a proof object nobody here can replay. A MODEL is a finite object,
checking a closed formula against a finite structure is decidable, and a verified evaluator for
that is the few hundred lines in `Fol/Check.lean`. So one half of the SAT/SMT family can be
certified while the other half stays an oracle, and the vocabulary in `docs/decisions/0006` keeps
the two apart in every report.

## The monomorphisation, and the one obligation it carries

`OwlLean.FOL.Form` in the sibling project `owl-lean` is parameterised by a signature `FSig` with
three sorts of symbol: `P1` unary predicates, `P2` binary predicates and `Const` constants. The
OWL instance sets `P1 := OwlP1`, a four-arm disjoint sum (`Cls`, `Dt`, `Thing`, `Lit`), and
`P2 := OwlP2`, a two-arm sum (`Op`, `Dp`). Here all of that is monomorphised at `Sym := String`,
because a checker has to read symbols off a file and a file carries strings.

That flattening is sound only if the string map is INJECTIVE on those arms. If a class IRI and a
datatype IRI with the same spelling both mapped to the bare IRI, they would become one predicate
and a model could satisfy a problem the ontology does not. The injectivity is supplied by the
prefixes `src/tptp.rs` already writes, and it is the reason the checker format keeps them:

```
OwlP1.Thing  ->  thing        OwlP2.Op r   ->  op:r
OwlP1.Lit    ->  lit          OwlP2.Dp d   ->  dp:d
OwlP1.Cls a  ->  c:a          FSig.Const a ->  i:a
OwlP1.Dt d   ->  d:d
```

`thing` and `lit` carry no colon and every other arm carries its own prefix, so the seven images
are pairwise disjoint whatever the IRIs are. The unary and binary symbol spaces are separate
fields of `FinModel`, so `c:X` as a unary predicate and `op:X` as a binary one could not collide
even without the prefixes; the prefixes are what stop `c:X` colliding with `d:X`.

## What is in the fragment

Everything `OwlLean.FOL.Form` has: unary and binary atoms, equality, the two truth constants,
negation, conjunction, disjunction, implication, and both quantifiers with an explicit `Nat`
binder. Nothing is normalised on the way in. `owl-lean` uses NAMED variables rather than de Bruijn
indices precisely so that freshness is a proof obligation rather than a silent convention, and a
checker that renumbered would be checking a different formula from the one the adequacy theorem is
about.

## What is NOT in the fragment, and is therefore never read

* Function symbols of arity above zero. The translation emits none, and the certificate format has
  no syntax for one. Mace4 clausifies and Skolemises, so its models DO interpret symbols like
  `f1(_)` and `c1`; those are dropped on the way in, which is taking the reduct of its structure.
  That needs no lemma here, because the checker re-evaluates the original formulas and they cannot
  mention a symbol the translation never emitted.
* Predicates of arity three or above, and sorts. `FSig` has exactly `P1` and `P2`.
* Anything about UNSATISFIABILITY, in any direction. See the top of this file.

## `problem.tsv`

One formula per line, three tab-separated fields.

```
ROLE <TAB> LABEL <TAB> FORMULA
```

`ROLE` is `axiom` or `goal_negated` and nothing else. `goal_negated` marks the NEGATION of the
conjecture: a countermodel to `Γ ⊨ φ` is a model of `Γ ∪ {¬φ}`, so the file carries `¬φ` and the
checker never negates anything itself. `LABEL` is the emitter's own label (`background_1`,
`ind_typing_3`, `owl_7_subClassOf`, `goal_classAssertion`) and is DIAGNOSTIC ONLY: it is not part
of the digest and nothing in the theorem looks at it. `FORMULA` is a space-separated prefix token
stream with no parentheses, unambiguous because every constructor has a fixed arity:

```
F ::= tru | fls | app1 SYM T | app2 SYM T T | eq T T
    | neg F | and F F | or F F | imp F F | all N F | ex N F
T ::= var N | const SYM
```

`N` is a decimal natural. `SYM` is one of the seven images above and must contain no space, tab,
carriage return or newline: the writer in `src/tptp.rs` returns an error rather than emit one that
does, because a symbol with a space in it re-parses as a DIFFERENT formula and a symbol with a tab
in it re-parses as a different set of fields. The digest below is the second line of defence
against exactly that.

## `model.tsv`

Dense rows, so a carrier of 20 with 300 symbols is a few hundred lines rather than 120,000.

```
domain             <TAB> N                      N >= 1. N = 0 is exit 2, not exit 1
problem            <TAB> HEX                     16 lowercase hex digits, see below
source             <TAB> z3|mace4|hand           provenance. UNTRUSTED, reporting only
decl1              <TAB> SYM                     SYM is interpreted as a unary predicate
decl2              <TAB> SYM                     SYM is interpreted as a binary predicate
declc              <TAB> SYM                     SYM is interpreted as a constant
p1                 <TAB> SYM <TAB> BITS          |BITS| = N. BITS[i] = '1' iff SYM holds of i
p2                 <TAB> SYM <TAB> i <TAB> BITS  row i of the binary table
const              <TAB> SYM <TAB> i             0 <= i < N
cardinality_search <TAB> k1,k2,...               sizes tried. reporting only
```

Carrier elements are the integers `0 .. N-1`, which is what Mace4 prints and what `Fin N` is, so
ingesting a Mace4 `interpretation(N, ...)` block renames nothing. Row order is irrelevant: the
parser reads the declarations in one pass and the tables in a second.

`domain` and `problem` are REQUIRED, and a second line of either is exit 2. `source` defaults to
`hand` and `cardinality_search` to the empty string; both are echoed into the report and nothing
checks them. A binary symbol needs all `N` of its `p2` rows, one per source element, in any order.
Declaring a symbol the problem never mentions is allowed and harmless: the coverage gate checks
that the problem's symbols are all declared, not the reverse, so a writer may emit the solver's
whole signature without pruning it.

The parser is STRICT, and deliberately stricter than soundness requires. A declared symbol with no
row is exit 2, a row for an undeclared symbol is exit 2, a second row for the same slot is exit 2,
a symbol declared at two arities is exit 2, a row whose length is not `N` is exit 2, and an index
outside `0 .. N-1` is exit 2. `FinModel`'s three fields are TOTAL, so a missing row would default
rather than fail, and a defaulted structure is still a structure: soundness would survive it. What
would not survive is the attribution, because the object certified would not be the object the
solver produced. The strictness is there for that, and `Fol/Check.lean` states plainly which of
the two it is defending.

## The digest, and what it is not

`model.tsv`'s `problem` line carries a digest of the problem the solver was actually given, and
`Fol/Parse.lean` recomputes it from `problem.tsv` and refuses on a mismatch. It is computed over
the CANONICAL RE-SERIALISATION of the parsed formula list rather than over the file bytes: the
lines `ROLE <TAB> showForm f`, in file order, joined with newlines, then FNV-1a 64 over the UTF-8
of that, printed as 16 lowercase hex digits. Labels are excluded, spacing is normalised, and the
role is included because it is what a report reads to decide whether a non-entailment was even
asked about.

It identifies, it does not commit. FNV-1a is not a cryptographic hash and the algorithm is written
out here so that two independent implementations can agree, not so that one can be defended
against someone who controls the file. Anyone needing that should hash the file with something
that is built for it. This is decision 0003 item 5, in the same words, for the same reason.

## A worked example

The problem: nothing is both a thing and a literal, `a` is a thing, every `Person` works for some
`Company`, and `a` is a `Person`. The goal `Company(a)`, negated, so that a model of the whole file
is a countermodel to the entailment.

`problem.tsv`, with a literal tab between each pair of fields

```
axiom	background_1	all 0 neg and app1 thing var 0 app1 lit var 0
axiom	ind_typing_1	app1 thing const i:a
axiom	owl_1_subClassOf	all 0 imp app1 c:Person var 0 ex 1 and app2 op:worksFor var 0 var 1 app1 c:Company var 1
axiom	owl_2_classAssertion	app1 c:Person const i:a
goal_negated	goal_classAssertion	neg app1 c:Company const i:a
```

`model.tsv`, a two-element carrier with `a` at 0 and its employer at 1

```
domain	2
problem	4403d8aaa0c422f7
source	z3
decl1	thing
decl1	lit
decl1	c:Person
decl1	c:Company
decl2	op:worksFor
declc	i:a
p1	thing	11
p1	lit	00
p1	c:Person	10
p1	c:Company	01
p2	op:worksFor	0	01
p2	op:worksFor	1	00
const	i:a	0
cardinality_search	1,2
```

`oo-folmodel problem.tsv model.tsv` on those two files, measured:

```
{"verdict":"model_checked","formulas":5,"domain":2,"closed":true,
 "goal_negated_present":true,"source":"z3","cardinality_search":"1,2",
 "problem_digest":"4403d8aaa0c422f7","theorem":"Fol.satisfiable_of_check",
 "non_entailment_theorem":"Fol.not_entails_of_check"}
```

(printed on one line; wrapped here to fit). Exit code 0. Delete the `op:worksFor` edge from row 0
and the same command prints

```
{"verdict":"rejected", ... ,"theorem":"Fol.check_complete_closed","first_rejected":2,
 "label":"owl_1_subClassOf","role":"axiom","formula":"all 0 imp app1 c:Person var 0 ex 1 and
 app2 op:worksFor var 0 var 1 app1 c:Company var 1"}
```

with exit code 1.

The digest `4403d8aaa0c422f7` is the measured value for that exact five-line `problem.tsv`, and
`Fol/Parse.lean` pins it with a `#guard`, so a change to `showForm` or to the hash fails the build
rather than drifting away from the format the Rust writer targets.

## The verdict vocabulary this file does NOT own

`oo-folmodel` answers one question: does this structure satisfy this problem. The five fields a
report carries, and the four solver verdicts that must never be collapsed into each other, are in
`docs/decisions/0006`. Two of them matter enough to repeat here. `unsatisfiable_oracle` may be
produced ONLY by a run whose emitted problem carried no cardinality constraint of any kind; a
bounded run's `unsat` is `no_model_up_to_size_k` and is not unsatisfiability. And a solver that
answers `sat` whose model this checker then REJECTS is `satisfiable_oracle` with a
`model_not_confirmed` note, never `rejected` as though the ontology were at fault.
-/
namespace Fol

/-- A predicate or constant symbol, already prefixed by `src/tptp.rs` so that the four arms of
`OwlLean.OwlP1`, the two of `OwlLean.OwlP2` and the individual names stay disjoint. The checker
never looks inside one: two symbols are the same when the strings are the same. -/
abbrev Sym := String

/-- A first-order term. Mirrors `OwlLean.FOL.Term`: a `Nat`-indexed variable or a constant.
There are no function symbols of positive arity, here or in the translation. -/
inductive Term where
  | var : Nat → Term
  | const : Sym → Term
deriving DecidableEq, Repr, Inhabited

/-- A first-order formula. Mirrors `OwlLean.FOL.Form` constructor for constructor, including the
explicit `Nat` on each binder. -/
inductive Form where
  | app1 : Sym → Term → Form
  | app2 : Sym → Term → Term → Form
  | eq : Term → Term → Form
  | tru : Form
  | fls : Form
  | neg : Form → Form
  | and : Form → Form → Form
  | or : Form → Form → Form
  | imp : Form → Form → Form
  | all : Nat → Form → Form
  | ex : Nat → Form → Form
deriving DecidableEq, Repr, Inhabited

/-! ## The vocabulary a problem mentions

These four functions collect the symbols a formula uses. They exist for the COVERAGE gate in
`Fol/Check.lean`, which is an attribution gate and not a soundness gate: `FinModel`'s fields are
total, so a structure interprets every symbol whether the file mentioned it or not, and the
soundness theorem needs none of this. What the gate buys is that the object certified is the
object the solver described. -/

/-- The constants occurring in a term. -/
def Term.consts : Term → List Sym
  | .var _ => []
  | .const c => [c]

/-- The unary predicate symbols occurring in a formula. -/
def p1Syms : Form → List Sym
  | .app1 p _ => [p]
  | .app2 .. | .eq .. | .tru | .fls => []
  | .neg f | .all _ f | .ex _ f => p1Syms f
  | .and f g | .or f g | .imp f g => p1Syms f ++ p1Syms g

/-- The binary predicate symbols occurring in a formula. -/
def p2Syms : Form → List Sym
  | .app2 p _ _ => [p]
  | .app1 .. | .eq .. | .tru | .fls => []
  | .neg f | .all _ f | .ex _ f => p2Syms f
  | .and f g | .or f g | .imp f g => p2Syms f ++ p2Syms g

/-- The constant symbols occurring in a formula. -/
def constSyms : Form → List Sym
  | .app1 _ t => t.consts
  | .app2 _ t u | .eq t u => t.consts ++ u.consts
  | .tru | .fls => []
  | .neg f | .all _ f | .ex _ f => constSyms f
  | .and f g | .or f g | .imp f g => constSyms f ++ constSyms g

/-! ## Free variables

`Fol/Check.lean` evaluates at the constant environment `fun _ => 0`. For ACCEPTANCE that costs
nothing, because `Satisfiable` binds the environment existentially. For REJECTION it would cost
something: without the results in `Fol/Free.lean` a rejection would only say "not a model under
this one assignment". These two functions are what those results are stated with, and the driver
reports whether the problem is closed so a reader knows which of the two sentences applies. -/

/-- The variables occurring in a term. -/
def Term.free : Term → List Nat
  | .var k => [k]
  | .const _ => []

/-- The variables occurring FREE in a formula.

The binder cases FILTER rather than `erase`, and the difference is not cosmetic. `List.erase`
removes the first occurrence only, so `free (∀x0. P(x0) ∧ Q(x0))` would come back as `[0]` and
every formula with a bound variable used twice would be classified as open. Nothing would become
unsound, because a larger `free` only strengthens the hypothesis of `holds_congr`; what would
happen is that `check_complete_closed` would stop applying to essentially every real problem and
the driver would silently print the weaker rejection sentence for ever. The `by decide` in
`Fol/Witness.lean` that the problem there is a set of sentences is what holds this honest. -/
def free : Form → List Nat
  | .app1 _ t => t.free
  | .app2 _ t u | .eq t u => t.free ++ u.free
  | .tru | .fls => []
  | .neg f => free f
  | .and f g | .or f g | .imp f g => free f ++ free g
  | .all k f | .ex k f => (free f).filter (fun j => j != k)

end Fol
