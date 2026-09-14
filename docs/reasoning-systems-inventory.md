# Reasoning systems: what this project uses, what it refuses, and why

Every external reasoning system that has been considered for this project, with its real status. The
point of the document is that a name appearing in a design discussion is not a capability, and a
reader deserves to know which is which without reading the commit log.

The organising principle is decision 0004. A model is a finite object and a verified checker can
validate one, so a satisfiability answer can be turned into a certificate. A refutation is a proof in
a calculus nobody has mechanised in core Lean here, so an unsatisfiability answer is testimony. That
single asymmetry decides how each system below is used, and it explains rankings that otherwise look
perverse.

## Status at a glance

| System | Kind | Status here |
| --- | --- | --- |
| Lean 4 | Proof assistant | The kernel. Every checker in this repository. |
| E 3.2.5 | First-order prover | Used as a differential oracle. Never as an authority. |
| Vampire 5.1.0 | First-order prover | Installed, same role as E. |
| Z3 4.16.0 | SMT solver | Model-certificate layer, under construction. |
| Mace4 | Finite model finder | Same. Its output is checkable; Prover9's is not. |
| Prover9 | First-order prover | Declined. Unmaintained since 2011, refutations uncheckable. |
| cvc5 | SMT solver | Not installed. Same role as Z3 when it is. |
| Isabelle/HOL | Proof assistant | Declined for now. Reasons below. |
| Dedukti | Logical framework | Declined. Reasons below. |
| Duper, lean-smt | Lean automation | Declined. Both require Mathlib. |
| Aeneas with Charon | Rust to Lean | Declined. Subset does not contain this codebase. |
| Verus, Creusot, Prusti | Rust verification | Declined. Each needs the code rewritten in its subset. |
| Kani | Rust bounded model checker | Being applied to the trusted boundary only. |
| TPTP and TSTP | Interchange | Implemented. The execution format. |
| CLIF, ISO/IEC 24707 | Interchange | Implemented. The conformance format. |
| SMT-LIB 2 | Interchange | Under construction. |
| RIF Core, SWRL | Rule languages | Front ends under construction. |
| CertifyingDatalog | Prior art | Not a dependency. The Horn layer is our analogue. |

Anything marked under construction is on an unmerged branch and is not a capability yet. This
document will be wrong the moment that changes, so treat the branch state as authoritative.

## The provers, and why the strongest one is still only an oracle

Vampire and E are the live first-order provers. Vampire has dominated the relevant competition
divisions for two decades and E is the more embeddable of the two. Both read TPTP, which is why TPTP
is our execution format regardless of what else we print.

Neither can give us a certificate. Replaying a superposition refutation needs a verified calculus with
unification, term orderings and redundancy criteria, and none exists in core Lean. So both are used the
way pyshacl is used for validation: as a differential oracle whose disagreement with our engine means
one of the two is wrong, and whose agreement means nothing has been proved. On its first real run
against one public vocabulary the comparison disagreed with the engine on fifty-eight of one hundred and
eighty-one claimed entailments, and every one was a real defect, including one in the exporter itself.
That is the value, and it does not require trusting the prover at all.

Prover9 is declined. Its author died in 2011, it has had no maintainer since, and its refutations are
no more checkable than Vampire's. There is no version of the argument where an unmaintained prover
beats a maintained one at the same job.

Mace4, from the same distribution, is a different matter entirely and is kept. It is a finite model
finder, its output is a finite structure, and a verified evaluator can check it. Half of a dead
toolchain is alive here because of what kind of evidence it produces, not how well maintained it is.

## SAT and SMT

Z3 is the fifth reasoning family and the last one to be built. The interesting part is not the SMT-LIB
printer, which is a third rendering of a representation we already have, but that Z3 returns models.
A model that our verified checker accepts converts a solver's opinion into a proof of satisfiability,
which is the only place in this architecture where an external tool's answer is upgraded rather than
merely corroborated.

Its unsat answers stay oracle answers. An unsat core is not a proof object we can replay, and the
proof logs Z3 can emit would need the same mechanised calculus that the first-order case lacks.

## Isabelle, and why not yet

Isabelle/HOL is the obvious comparison, because Sledgehammer does exactly what we cannot: it calls
external provers and then reconstructs their findings through the Isabelle kernel, so an external
prover's answer becomes a proof. That is the capability this project lacks and would most like.

It is declined for now, and not because Isabelle is unsuitable. Adopting it
means a second proof assistant, a second build, a second set of proofs and a second trust surface,
for a codebase whose entire pitch is that the trust surface is small enough to read in an afternoon.
Reconstruction would have to be redone for our translation rather than inherited. And the specific
thing we would gain, kernel-checked refutations, we can already approximate where it matters by
checking models instead.

The version that would pay, and that remains open, is narrower: use Isabelle as an INDEPENDENT SECOND
KERNEL for the statements we already prove in Lean, so that a bug in one kernel or in one
formalisation does not go unnoticed. That is a replication exercise rather than an integration, and it
should be judged on its own when the Lean side is stable.

Nitpick, Isabelle's counterexample finder, belongs to the model-finder family above and would slot
into the certified path the same way Mace4 does.

## Dedukti, and why not

Dedukti is a logical framework designed so that proofs from different systems can be expressed in one
language and rechecked. The motivation is real and it is close to this project's own.

It is declined because it solves a problem we do not have. Dedukti pays when you hold large proof
libraries in several systems and want them to talk. We hold small certificates in one format, checked
by one small kernel, and adding a framework layer would enlarge the trusted base to buy portability
nobody has asked for. If a second consumer of our certificates ever appears, this is the first thing
to revisit.

## Lean automation we do not use

Duper is a superposition prover written inside Lean that produces kernel-checked proof terms, and
lean-smt reconstructs cvc5 proofs the same way. Either would give us precisely the missing capability,
kernel-checked refutations, without leaving Lean.

Both depend on Mathlib. The axiom footprint of every result here is pinned to `propext`,
`Classical.choice` and `Quot.sound`, the build takes no external package, and the argument that anyone
can read the whole checker rests on that. Taking Mathlib to gain refutation checking is a real trade
and might one day be the right one. It is not being made silently.

## Putting the Rust in Lean

The demand that all the code be verified in Lean cannot be met literally. There are roughly fifty
thousand lines of Rust here. Aeneas with Charon translates Rust into Lean for a restricted subset that
this codebase is not inside, and the same is true of Verus, Creusot and Prusti, each of which verifies
Rust written in its own dialect against SMT.

The demand has a real core and that core is small. The Lean theorems are conditional: they say that IF
the asserted graph is what the certificate says and IF the derivation steps are the ones the engine
took, THEN the conclusions follow. Everything to the left of that is the trusted computing base, and
it is a serialiser, a parser and an interner rather than fifty thousand lines. That boundary is what
is being property-tested and, where it pays, model-checked with Kani. What remains trusted after that
work will be named explicitly rather than left for a reader to infer.

## Rule languages

The Horn certificate layer is generic over rule tables, with one soundness theorem covering every
table at once, which is what makes RIF Core, SWRL and Datalog a single problem rather than three. Until
the front ends land, that coverage is architectural rather than actual, because nothing produces a
rule table from a standard rule syntax.

The verdict rule from decision 0003 governs all of it and is the reason this is safe to build. A
certificate over the built-in table earns `entailed`. A certificate over a table a user supplied,
whatever syntax it arrived in, earns `entailed_under_supplied_rules`, because those rules are
assumptions the certificate carries and never facts it establishes.

CertifyingDatalog, presented at ITP 2025, is the closest published prior art and is not a dependency.
It certifies Datalog derivations in Lean; our Horn layer is the analogue reached independently, and the
comparison is worth making in any write-up rather than avoided.

## Interchange formats

TPTP is the execution format, because it is the only one an installed solver will read. CLIF is the
conformance format, because ISO/IEC 21838-1 requires a top-level ontology to carry an axiomatisation in
a language conforming to ISO/IEC 24707 and the Basic Formal Ontology discharges that in CLIF. SMT-LIB
is the model-finding format. All three are printers over one representation, and the correspondence
between that representation and the Lean translation is pinned by hand-computed tests and is not itself
proved. That last sentence is the honest trust boundary of the export layer and should never be dropped
when the layer is described.
