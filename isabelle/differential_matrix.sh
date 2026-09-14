#!/bin/sh
# Emit one JSON line per (rule table, asserted graph, certificate) triple, for the
# differential test against the other implementation.  Run the SAME matrix through the
# other checker and diff the accept/reject bit and the verdict word.
#
# READ THIS BEFORE INTERPRETING THE RESULT.  Checking a Horn certificate is purely
# syntactic: neither side consults its semantics.  Two checkers built on contradictory
# model theories will agree on every row here.  AGREEMENT IS HYGIENE, NOT EVIDENCE THAT
# THE DEFINITIONS AGREE.  The evidence lives in which arms each side can discharge and
# from which conditions (isabelle/OO_Builtin_Sound.thy) and in whether the conditions
# describe anything at all (isabelle/OO_NonVacuity.thy).
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
FX=${OO_FIXTURES:-$HERE/../tests/fixtures/horn}
ADD=$HERE/fixtures-added

row() { "$HERE/run_checker.sh" "$1" "$2" "$3" || true; }

row "$FX/builtin_rules.tsv" "$FX/asserted.tsv"       "$FX/good.tsv"
row "$FX/user_rules.tsv"    "$FX/asserted.tsv"       "$FX/good.tsv"
row "$FX/short_rules.tsv"   "$FX/asserted.tsv"       "$FX/good.tsv"
row "$FX/builtin_rules.tsv" "$FX/asserted.tsv"       "$FX/bad_index.tsv"
row "$FX/builtin_rules.tsv" "$FX/asserted.tsv"       "$FX/bad_binding.tsv"
row "$FX/builtin_rules.tsv" "$FX/asserted.tsv"       "$FX/bad_conclusion.tsv"
row "$FX/builtin_rules.tsv" "$FX/asserted.tsv"       "$FX/bad_premise.tsv"
row "$FX/builtin_rules.tsv" "$FX/asserted.tsv"       "$FX/bad_self.tsv"
row "$FX/builtin_rules.tsv" "$ADD/asserted_chain.tsv" "$ADD/bad_self_chain.tsv"
row "$FX/builtin_rules.tsv" "$ADD/asserted_chain.tsv" "$ADD/good_chain.tsv"
row "$FX/builtin_rules.tsv" "$FX/asserted.tsv"       "$ADD/bad_order.tsv"
row "$FX/builtin_rules.tsv" "$FX/asserted.tsv"       "$ADD/bad_dup_key.tsv"
row "$FX/builtin_rules.tsv" "$ADD/asserted_gen.tsv"  "$ADD/generalized.tsv"
