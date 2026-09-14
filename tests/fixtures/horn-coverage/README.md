# One graph per rule the repository's own RDF never fires

`tools/horn_differential.py` compares the Rust reasoner against the Python one over every
RDF document this repository tracks. On 14 September 2026 that corpus fired **20 of the
27 rules** in the built-in Horn table. The differential therefore compared the two
engines zero times on the other seven, and its clean sweep said nothing whatever about
them:

    prp-inv2  eq-sym  cls-avf  cls-hv1  cls-hv2  scm-svf2  scm-avf2

This directory holds one Turtle file per silent rule. Each is the smallest graph that
makes exactly that rule fire — one derivation, credited to that rule, nothing else — and
each carries the W3C rule, its table, and its expected derivation in a comment at the top
of the file.

## These are TEST DATA and are not part of the corpus

They are deliberately constructed to make one rule fire. Mixing them into the corpus of
real ontologies would inflate the coverage number with graphs that were written to hit
it, which is measuring the ruler. So:

* `discover()` in `tools/horn_differential.py` EXCLUDES this directory, and a test in
  `python/tests/test_horn_three_way_differential.py` asserts that it does.
* The tool runs them as a separate, labelled set and reports two coverage numbers: how
  many rules fired on the repository's own RDF, and how many fired once these are added.
  Rules that fire ONLY here are named on every run.

A rule covered only by a fixture in this directory has been differentially compared on a
graph written for the purpose and on nothing else. That is much better than zero and it
is not the same as evidence from a real ontology, which is why the report keeps the two
apart rather than adding them up.

## Adding one

Name the file after the rule exactly as the rule table names it (`<rule>.ttl`); the tool
reads the target rule off the stem and checks that this is the rule that fires. Keep it
minimal, and put the W3C rule text in the header comment so a reader can check the
fixture against the standard without leaving the file.
