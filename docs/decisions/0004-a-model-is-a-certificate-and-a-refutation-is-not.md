# 0004 · A model is a certificate, and a refutation is not

- **Status**: accepted · the positive half is implemented for description logics in `lean/Dl/Check.lean`
  (`satisfiable_of_checkModel`, `checkModel_complete`), checker `oo-dlmodel`, gated by
  `tests/dl_model_certificate_test.rs` · the first-order half is under construction on branch
  `model-certificates` and this record does not claim it
- **Written**: 2026-09-14
- **Related**: decision 0002 (an inference carries a certificate), which cites this record;
  decision 0005 (a prover is an oracle and a translation is a theorem), which is the negative half
  of the same observation

## The problem

Every layer here follows one rule: a fast untrusted engine proposes, and a small verified checker
disposes. That rule is easy to state and it silently fails to apply to about half of automated
reasoning, because the two directions of a decision problem produce evidence of completely different
kinds, and only one of them is checkable with the means available.

When a solver answers SATISFIABLE it can hand back a model. When it answers UNSATISFIABLE it can hand
back a derivation. Those look symmetric and they are not. A finite model is a finite object, checking
a formula against it terminates, and a verified evaluator for that is a few hundred lines of core
Lean. A superposition refutation is a proof in a calculus with unification, term orderings and
redundancy criteria, and replaying one requires mechanising that calculus. No such thing exists in
core Lean, and building it is a research programme rather than a sprint.

Treating the two the same way is how a verified checker becomes decoration. Either the refutation gets
waved through as though it were checked, which is the assurance-laundering failure this project exists
to attack, or the model gets refused alongside it, which throws away the one case where an external
solver's answer can actually be turned into a proof.

## Decisions

1. **The asymmetry is architectural and it is visible in the code.** A satisfiability answer that
   arrives with a model goes to a verified checker and, if it passes, earns a certified verdict. An
   unsatisfiability answer earns an oracle verdict and can never earn more, for as long as no verified
   first-order calculus exists here. The two are separate code paths producing separate words.

2. **Three verdicts, never collapsed.** A checked model yields the certified verdict and names the
   theorem that backs it. A solver reporting satisfiable without a model we could check yields an
   oracle verdict. A solver reporting unsatisfiable yields an oracle verdict. A test must fail if an
   unchecked result ever prints the certified word, exactly as
   `a_user_rule_never_earns_the_absolute_verdict` does for rule tables under decision 0003.

3. **A rejected model is an incident, not a downgrade.** If a solver supplies a model and our verified
   checker refuses it, the correct response is to stop the line. It means the solver and our
   translation disagree about what the problem says, and exactly one of them is wrong. Quietly falling
   back to an oracle verdict would discard the most valuable signal the layer can produce.

4. **Model finders are therefore first-class, and this reverses an obvious ranking.** Judged on
   proving power, a model finder is the weaker tool and an unmaintained one is worthless. Judged on
   what this architecture can use, a model finder is the stronger tool, because its output is the kind
   we can check. That is why the LADR distribution is half dead and half live here: Prover9 has had no
   maintainer since 2011 and its refutations are uncheckable, while Mace4 produces finite models that
   a verified evaluator can validate. The same holds for Z3 and cvc5, whose models are checkable while
   their unsat cores are not.

5. **The boundary is stated, not implied.** Anywhere a verdict is reported, the document says which of
   the two kinds of evidence it rests on. Nothing in the output, the documentation, the command line
   or the tool descriptions may call a solver's answer proved, verified or certified when no checker
   accepted a model.

## What this costs

Half of the decision problem stays outside the verified perimeter, and saying so plainly is part of
the decision. An unsatisfiability answer from Vampire, E or Z3 is exactly as trustworthy as those
programs, which is to say very trustworthy and not proved. The honest description of this layer is
that it certifies consistency and takes inconsistency on testimony.

Two routes would change that, and neither is taken here. Reconstructing a prover's refutation inside
Lean is what Isabelle does through Sledgehammer, and the Lean equivalents, Duper and lean-smt, depend
on Mathlib, which would enlarge a trust surface currently small enough to read in an afternoon.
Mechanising a superposition calculus from scratch in core Lean is the other, and it is measured in
years rather than weeks. If either becomes cheap, this record should be revisited rather than quietly
worked around.
