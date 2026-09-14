# `isabelle/` — an independent second formalisation of the Horn certificate checker

This directory is a second, independent formalisation of the OWL 2 RL/RDF Horn
certificate checker and its model theory, in Isabelle/HOL. It exists to test the one
thing a single machine-checked proof cannot test: whether the **definitions** are right.
A proof assistant rules out a bad argument; it says nothing about a bad definition, and a
semantics that is stronger than the specification makes every soundness theorem over it
weaker than it looks while every proof still succeeds.

It was written from the W3C primary sources and the fixture **data** only. Nothing under
`lean/` was read, listed, grepped, or reasoned about while it was written. A
transliteration would have been worthless here, because a shared definitional bug
survives translation untouched.

Every modelling decision is recorded as a comment at the point it is made, with the
specification clause it rests on. That list is what makes a later disagreement
diagnosable instead of merely embarrassing; start with `OO_Semantics.thy`.

## Build

Needs Isabelle2025-2.

    isabelle build -d isabelle -c OOHorn

The session checks everything, including the fixture results and an audit that fails the
build if any soundness or non-vacuity theorem depends on an oracle (`sorry` is the
oracle `Pure.skip_proof`, so this catches it).

## Run the checker

    isabelle/run_checker.sh RULES.tsv ASSERTED.tsv CERT.tsv

Exit 0 accepted, 1 rejected, 2 parse error. One JSON object on stdout carrying **both**
the strict and the lenient verdict. `OO_VERBOSE=1` keeps Poly/ML's chatter.

Regenerate `driver/oo_horn_generated.ML` from the theories with `isabelle/export.sh`.

## Run the differential matrix

    isabelle/differential_matrix.sh

One JSON line per input triple. Run the same matrix through the other checker and diff
the accept/reject bit and the verdict word.

## Files

| file | what it holds |
|---|---|
| `OO_Format.thy` | terms, triples, rule patterns, rules, steps, instantiation. No semantics. |
| `OO_Semantics.thy` | interpretations, truth of a triple, the 26 semantic conditions, both entailment relations. Never in the export closure. |
| `OO_Check.thy` | the executable checker and the built-in rule table. No semantics. |
| `OO_Sound.thy` | `horn_certificate_sound` — the conditional verdict. |
| `OO_Builtin_Sound.thy` | the 27 arms, and `entails_of_builtin` — the absolute verdict. |
| `OO_NonVacuity.thy` | witness models; entailment is not the trivial relation. |
| `OO_Parse.thy` | TSV field lists to datatypes. Executable. |
| `OO_Pipeline.thy` | what the tool's own output means, end to end. |
| `OO_Fixtures.thy` | the checker run on the real fixture bytes, as build gates. Uses `eval`; no soundness theorem depends on it. |
| `OO_Audit.thy` | the oracle gate, and a check that the gate can fail. |
| `OO_Export.thy` | code generation. |
| `driver/` | the untrusted SML driver, and the generated core. |
| `fixtures-added/` | fixtures for properties the shipped set cannot reach. |

## Trust boundary

Inside: the Isabelle kernel, the theories above, and the code generator — which is
trusted, not verified, exactly as a compiler is on any other side of any comparison.

Outside: file IO, splitting bytes on LF and TAB, exit codes, JSON, and the claim that
the engine's `asserted.tsv` is the store it says it is.
