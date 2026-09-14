(* OO_Fixtures.thy -- the verified checker run on the REAL fixture bytes.

   NOTE THE DIFFERENT TRUST BASIS.  Everything in this file is proved "by eval", which
   runs the code generator and the ML runtime rather than the kernel's inference engine.
   These are TESTS, not part of the soundness argument.  No theorem in OO_Sound,
   OO_Builtin_Sound, OO_NonVacuity or OO_Pipeline depends on this file or on eval.
   They are here so that the fixture results are a BUILD GATE: if any of them changes,
   this session stops building.

   The data below was generated mechanically from tests/fixtures/horn/*.tsv and from
   isabelle/fixtures-added/*.tsv, field by field.  It is not retyped.

   WHAT THIS DEMONSTRATES, AND WHAT IT DOES NOT.  Checking a Horn certificate is purely
   syntactic; the semantics is never consulted.  Two checkers built on wildly different
   and even contradictory model theories will agree on every row of this table.
   AGREEMENT HERE IS HYGIENE, NOT EVIDENCE THAT TWO FORMALISATIONS AGREE.  The evidence
   is in OO_Builtin_Sound (which arms, from which conditions) and OO_NonVacuity (whether
   the conditions describe anything). *)

theory OO_Fixtures
  imports OO_Pipeline
begin

section \<open>Fixture data, transcribed from the TSV files\<close>


definition f_asserted :: "string list list" where
  "f_asserted =
    [ [''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/A>''],
      [''<http://ex.org/A>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/B>''] ]"

definition f_builtin_rules :: "string list list" where
  "f_builtin_rules =
    [ [''rdfs2'', ''2'', ''?s'', ''?p'', ''?o'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#domain>'', ''?c'', ''?s'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?c''],
      [''rdfs3'', ''2'', ''?s'', ''?p'', ''?o'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#range>'', ''?c'', ''?o'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?c''],
      [''rdfs5'', ''2'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?b'', ''?b'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?c'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?c''],
      [''rdfs7'', ''2'', ''?s'', ''?p'', ''?o'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?q'', ''?s'', ''?q'', ''?o''],
      [''rdfs9'', ''2'', ''?x'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?a'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?b'', ''?x'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?b''],
      [''rdfs11'', ''2'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?b'', ''?b'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c''],
      [''prp-trp'', ''3'', ''?p'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://www.w3.org/2002/07/owl#TransitiveProperty>'', ''?x'', ''?p'', ''?y'', ''?y'', ''?p'', ''?z'', ''?x'', ''?p'', ''?z''],
      [''prp-symp'', ''2'', ''?p'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://www.w3.org/2002/07/owl#SymmetricProperty>'', ''?x'', ''?p'', ''?y'', ''?y'', ''?p'', ''?x''],
      [''prp-inv1'', ''2'', ''?p'', ''<http://www.w3.org/2002/07/owl#inverseOf>'', ''?q'', ''?x'', ''?p'', ''?y'', ''?y'', ''?q'', ''?x''],
      [''prp-inv2'', ''2'', ''?p'', ''<http://www.w3.org/2002/07/owl#inverseOf>'', ''?q'', ''?x'', ''?q'', ''?y'', ''?y'', ''?p'', ''?x''],
      [''eq-sym'', ''1'', ''?a'', ''<http://www.w3.org/2002/07/owl#sameAs>'', ''?b'', ''?b'', ''<http://www.w3.org/2002/07/owl#sameAs>'', ''?a''],
      [''scm-eqc1'', ''1'', ''?a'', ''<http://www.w3.org/2002/07/owl#equivalentClass>'', ''?b'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?b''],
      [''scm-eqc1'', ''1'', ''?a'', ''<http://www.w3.org/2002/07/owl#equivalentClass>'', ''?b'', ''?b'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?a''],
      [''scm-eqp1'', ''1'', ''?a'', ''<http://www.w3.org/2002/07/owl#equivalentProperty>'', ''?b'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?b''],
      [''scm-eqp1'', ''1'', ''?a'', ''<http://www.w3.org/2002/07/owl#equivalentProperty>'', ''?b'', ''?b'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?a''],
      [''cls-svf1'', ''4'', ''?r'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?r'', ''<http://www.w3.org/2002/07/owl#someValuesFrom>'', ''?c'', ''?x'', ''?p'', ''?y'', ''?y'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?c'', ''?x'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?r''],
      [''cls-avf'', ''4'', ''?r'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?r'', ''<http://www.w3.org/2002/07/owl#allValuesFrom>'', ''?c'', ''?x'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?r'', ''?x'', ''?p'', ''?y'', ''?y'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?c''],
      [''cls-hv1'', ''3'', ''?r'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?r'', ''<http://www.w3.org/2002/07/owl#hasValue>'', ''?v'', ''?x'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?r'', ''?x'', ''?p'', ''?v''],
      [''cls-hv2'', ''3'', ''?r'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?r'', ''<http://www.w3.org/2002/07/owl#hasValue>'', ''?v'', ''?x'', ''?p'', ''?v'', ''?x'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?r''],
      [''scm-svf1'', ''5'', ''?c1'', ''<http://www.w3.org/2002/07/owl#someValuesFrom>'', ''?y1'', ''?c1'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?c2'', ''<http://www.w3.org/2002/07/owl#someValuesFrom>'', ''?y2'', ''?c2'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?y1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?y2'', ''?c1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c2''],
      [''scm-svf2'', ''5'', ''?c1'', ''<http://www.w3.org/2002/07/owl#someValuesFrom>'', ''?y'', ''?c1'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p1'', ''?c2'', ''<http://www.w3.org/2002/07/owl#someValuesFrom>'', ''?y'', ''?c2'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p2'', ''?p1'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?p2'', ''?c1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c2''],
      [''scm-avf1'', ''5'', ''?c1'', ''<http://www.w3.org/2002/07/owl#allValuesFrom>'', ''?y1'', ''?c1'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?c2'', ''<http://www.w3.org/2002/07/owl#allValuesFrom>'', ''?y2'', ''?c2'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?y1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?y2'', ''?c1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c2''],
      [''scm-avf2'', ''5'', ''?c1'', ''<http://www.w3.org/2002/07/owl#allValuesFrom>'', ''?y'', ''?c1'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p1'', ''?c2'', ''<http://www.w3.org/2002/07/owl#allValuesFrom>'', ''?y'', ''?c2'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p2'', ''?p1'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?p2'', ''?c2'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c1''],
      [''scm-dom1'', ''2'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#domain>'', ''?c1'', ''?c1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c2'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#domain>'', ''?c2''],
      [''scm-dom2'', ''2'', ''?p2'', ''<http://www.w3.org/2000/01/rdf-schema#domain>'', ''?c'', ''?p1'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?p2'', ''?p1'', ''<http://www.w3.org/2000/01/rdf-schema#domain>'', ''?c''],
      [''scm-rng1'', ''2'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#range>'', ''?c1'', ''?c1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c2'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#range>'', ''?c2''],
      [''scm-rng2'', ''2'', ''?p2'', ''<http://www.w3.org/2000/01/rdf-schema#range>'', ''?c'', ''?p1'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?p2'', ''?p1'', ''<http://www.w3.org/2000/01/rdf-schema#range>'', ''?c''] ]"

definition f_user_rules :: "string list list" where
  "f_user_rules =
    [ [''rdfs2'', ''2'', ''?s'', ''?p'', ''?o'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#domain>'', ''?c'', ''?s'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?c''],
      [''rdfs3'', ''2'', ''?s'', ''?p'', ''?o'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#range>'', ''?c'', ''?o'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?c''],
      [''rdfs5'', ''2'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?b'', ''?b'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?c'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?c''],
      [''rdfs7'', ''2'', ''?s'', ''?p'', ''?o'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?q'', ''?s'', ''?q'', ''?o''],
      [''rdfs9'', ''2'', ''?x'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?a'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?b'', ''?x'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?b''],
      [''rdfs11'', ''2'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?b'', ''?b'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c''],
      [''prp-trp'', ''3'', ''?p'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://www.w3.org/2002/07/owl#TransitiveProperty>'', ''?x'', ''?p'', ''?y'', ''?y'', ''?p'', ''?z'', ''?x'', ''?p'', ''?z''],
      [''prp-symp'', ''2'', ''?p'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://www.w3.org/2002/07/owl#SymmetricProperty>'', ''?x'', ''?p'', ''?y'', ''?y'', ''?p'', ''?x''],
      [''prp-inv1'', ''2'', ''?p'', ''<http://www.w3.org/2002/07/owl#inverseOf>'', ''?q'', ''?x'', ''?p'', ''?y'', ''?y'', ''?q'', ''?x''],
      [''prp-inv2'', ''2'', ''?p'', ''<http://www.w3.org/2002/07/owl#inverseOf>'', ''?q'', ''?x'', ''?q'', ''?y'', ''?y'', ''?p'', ''?x''],
      [''eq-sym'', ''1'', ''?a'', ''<http://www.w3.org/2002/07/owl#sameAs>'', ''?b'', ''?b'', ''<http://www.w3.org/2002/07/owl#sameAs>'', ''?a''],
      [''scm-eqc1'', ''1'', ''?a'', ''<http://www.w3.org/2002/07/owl#equivalentClass>'', ''?b'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?b''],
      [''scm-eqc1'', ''1'', ''?a'', ''<http://www.w3.org/2002/07/owl#equivalentClass>'', ''?b'', ''?b'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?a''],
      [''scm-eqp1'', ''1'', ''?a'', ''<http://www.w3.org/2002/07/owl#equivalentProperty>'', ''?b'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?b''],
      [''scm-eqp1'', ''1'', ''?a'', ''<http://www.w3.org/2002/07/owl#equivalentProperty>'', ''?b'', ''?b'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?a''],
      [''cls-svf1'', ''4'', ''?r'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?r'', ''<http://www.w3.org/2002/07/owl#someValuesFrom>'', ''?c'', ''?x'', ''?p'', ''?y'', ''?y'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?c'', ''?x'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?r''],
      [''cls-avf'', ''4'', ''?r'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?r'', ''<http://www.w3.org/2002/07/owl#allValuesFrom>'', ''?c'', ''?x'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?r'', ''?x'', ''?p'', ''?y'', ''?y'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?c''],
      [''cls-hv1'', ''3'', ''?r'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?r'', ''<http://www.w3.org/2002/07/owl#hasValue>'', ''?v'', ''?x'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?r'', ''?x'', ''?p'', ''?v''],
      [''cls-hv2'', ''3'', ''?r'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?r'', ''<http://www.w3.org/2002/07/owl#hasValue>'', ''?v'', ''?x'', ''?p'', ''?v'', ''?x'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?r''],
      [''scm-svf1'', ''5'', ''?c1'', ''<http://www.w3.org/2002/07/owl#someValuesFrom>'', ''?y1'', ''?c1'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?c2'', ''<http://www.w3.org/2002/07/owl#someValuesFrom>'', ''?y2'', ''?c2'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?y1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?y2'', ''?c1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c2''],
      [''scm-svf2'', ''5'', ''?c1'', ''<http://www.w3.org/2002/07/owl#someValuesFrom>'', ''?y'', ''?c1'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p1'', ''?c2'', ''<http://www.w3.org/2002/07/owl#someValuesFrom>'', ''?y'', ''?c2'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p2'', ''?p1'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?p2'', ''?c1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c2''],
      [''scm-avf1'', ''5'', ''?c1'', ''<http://www.w3.org/2002/07/owl#allValuesFrom>'', ''?y1'', ''?c1'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?c2'', ''<http://www.w3.org/2002/07/owl#allValuesFrom>'', ''?y2'', ''?c2'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p'', ''?y1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?y2'', ''?c1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c2''],
      [''scm-avf2'', ''5'', ''?c1'', ''<http://www.w3.org/2002/07/owl#allValuesFrom>'', ''?y'', ''?c1'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p1'', ''?c2'', ''<http://www.w3.org/2002/07/owl#allValuesFrom>'', ''?y'', ''?c2'', ''<http://www.w3.org/2002/07/owl#onProperty>'', ''?p2'', ''?p1'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?p2'', ''?c2'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c1''],
      [''scm-dom1'', ''2'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#domain>'', ''?c1'', ''?c1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c2'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#domain>'', ''?c2''],
      [''scm-dom2'', ''2'', ''?p2'', ''<http://www.w3.org/2000/01/rdf-schema#domain>'', ''?c'', ''?p1'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?p2'', ''?p1'', ''<http://www.w3.org/2000/01/rdf-schema#domain>'', ''?c''],
      [''scm-rng1'', ''2'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#range>'', ''?c1'', ''?c1'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''?c2'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#range>'', ''?c2''],
      [''scm-rng2'', ''2'', ''?p2'', ''<http://www.w3.org/2000/01/rdf-schema#range>'', ''?c'', ''?p1'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?p2'', ''?p1'', ''<http://www.w3.org/2000/01/rdf-schema#range>'', ''?c''],
      [''every-supplier-is-compliant'', ''1'', ''?s'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/Supplier>'', ''?s'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/Compliant>''] ]"

definition f_short_rules :: "string list list" where
  "f_short_rules =
    [ [''rdfs2'', ''2'', ''?s'', ''?p'', ''?o'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#domain>'', ''?c'', ''?s'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?c''],
      [''rdfs3'', ''2'', ''?s'', ''?p'', ''?o'', ''?p'', ''<http://www.w3.org/2000/01/rdf-schema#range>'', ''?c'', ''?o'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''?c''],
      [''rdfs5'', ''2'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?b'', ''?b'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?c'', ''?a'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''?c''] ]"

definition f_good :: "string list list" where
  "f_good =
    [ [''4'', ''3'', ''x'', ''<http://ex.org/a>'', ''a'', ''<http://ex.org/A>'', ''b'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/A>'', ''<http://ex.org/A>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/B>''] ]"

definition f_bad_index :: "string list list" where
  "f_bad_index =
    [ [''99'', ''3'', ''x'', ''<http://ex.org/a>'', ''a'', ''<http://ex.org/A>'', ''b'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/A>'', ''<http://ex.org/A>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/B>''] ]"

definition f_bad_binding :: "string list list" where
  "f_bad_binding =
    [ [''4'', ''3'', ''x'', ''<http://ex.org/a>'', ''a'', ''<http://ex.org/WRONG>'', ''b'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/A>'', ''<http://ex.org/A>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/B>''] ]"

definition f_bad_conclusion :: "string list list" where
  "f_bad_conclusion =
    [ [''4'', ''3'', ''x'', ''<http://ex.org/a>'', ''a'', ''<http://ex.org/A>'', ''b'', ''<http://ex.org/Z>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/A>'', ''<http://ex.org/A>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/B>''] ]"

definition f_bad_premise :: "string list list" where
  "f_bad_premise =
    [ [''4'', ''3'', ''x'', ''<http://ex.org/ghost>'', ''a'', ''<http://ex.org/A>'', ''b'', ''<http://ex.org/B>'', ''<http://ex.org/ghost>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/B>'', ''<http://ex.org/ghost>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/A>'', ''<http://ex.org/A>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/B>''] ]"

definition f_bad_self :: "string list list" where
  "f_bad_self =
    [ [''4'', ''3'', ''x'', ''<http://ex.org/a>'', ''a'', ''<http://ex.org/A>'', ''b'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/B>'', ''<http://ex.org/A>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/B>''] ]"

definition f_asserted_chain :: "string list list" where
  "f_asserted_chain =
    [ [''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/A>''],
      [''<http://ex.org/A>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/B>''],
      [''<http://ex.org/B>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/C>''] ]"

definition f_bad_self_chain :: "string list list" where
  "f_bad_self_chain =
    [ [''4'', ''3'', ''x'', ''<http://ex.org/a>'', ''a'', ''<http://ex.org/B>'', ''b'', ''<http://ex.org/C>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/C>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/B>'', ''<http://ex.org/B>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/C>''],
      [''4'', ''3'', ''x'', ''<http://ex.org/a>'', ''a'', ''<http://ex.org/A>'', ''b'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/A>'', ''<http://ex.org/A>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/B>''] ]"

definition f_good_chain :: "string list list" where
  "f_good_chain =
    [ [''4'', ''3'', ''x'', ''<http://ex.org/a>'', ''a'', ''<http://ex.org/A>'', ''b'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/A>'', ''<http://ex.org/A>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/B>''],
      [''4'', ''3'', ''x'', ''<http://ex.org/a>'', ''a'', ''<http://ex.org/B>'', ''b'', ''<http://ex.org/C>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/C>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/B>'', ''<http://ex.org/B>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/C>''] ]"

definition f_bad_order :: "string list list" where
  "f_bad_order =
    [ [''4'', ''3'', ''x'', ''<http://ex.org/a>'', ''a'', ''<http://ex.org/A>'', ''b'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/B>'', ''<http://ex.org/A>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/A>''] ]"

definition f_bad_dup_key :: "string list list" where
  "f_bad_dup_key =
    [ [''4'', ''4'', ''x'', ''<http://ex.org/a>'', ''x'', ''<http://ex.org/zzz>'', ''a'', ''<http://ex.org/A>'', ''b'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/B>'', ''<http://ex.org/a>'', ''<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>'', ''<http://ex.org/A>'', ''<http://ex.org/A>'', ''<http://www.w3.org/2000/01/rdf-schema#subClassOf>'', ''<http://ex.org/B>''] ]"

definition f_asserted_gen :: "string list list" where
  "f_asserted_gen =
    [ [''<http://ex.org/x>'', ''<http://ex.org/p>'', ''<http://ex.org/y>''],
      [''<http://ex.org/p>'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''_:bq''] ]"

definition f_generalized :: "string list list" where
  "f_generalized =
    [ [''3'', ''4'', ''s'', ''<http://ex.org/x>'', ''p'', ''<http://ex.org/p>'', ''o'', ''<http://ex.org/y>'', ''q'', ''_:bq'', ''<http://ex.org/x>'', ''_:bq'', ''<http://ex.org/y>'', ''<http://ex.org/x>'', ''<http://ex.org/p>'', ''<http://ex.org/y>'', ''<http://ex.org/p>'', ''<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>'', ''_:bq''] ]"


section \<open>The parser recovers the built-in table exactly (M33)\<close>

(* If this failed, every certificate would silently receive the WEAKER verdict, and
   nothing else in the suite would notice. *)
lemma parsed_builtin_is_the_builtin_table:
  "parse_rules f_builtin_rules = Some builtin_table"
  by eval

lemma parsed_user_table_is_not_the_builtin_table:
  "parse_rules f_user_rules \<noteq> Some builtin_table"
  by eval

section \<open>The shipped fixtures\<close>

lemma fx_good_builtin:
  "run_check f_builtin_rules f_asserted f_good = Ok Entailed"
  by eval

(* THE ASSUMPTION-INTO-FACT GUARD.  user_rules.tsv is builtin_rules.tsv plus one row
   reading "every supplier is compliant".  The certificate is the SAME one, and it still
   checks green -- but the verdict word changes, and with it which theorem applies. *)
lemma fx_good_user_rules_gets_the_weaker_verdict:
  "run_check f_user_rules f_asserted f_good = Ok EntailedUnderSuppliedRules"
  by eval

lemma fx_good_short_rules:
  "run_check f_short_rules f_asserted f_good = Rejected 0 R_index_out_of_range"
  by eval

lemma fx_bad_index:
  "run_check f_builtin_rules f_asserted f_bad_index = Rejected 0 R_index_out_of_range"
  by eval

lemma fx_bad_binding:
  "run_check f_builtin_rules f_asserted f_bad_binding = Rejected 0 (R_body_mismatch 0)"
  by eval

lemma fx_bad_conclusion:
  "run_check f_builtin_rules f_asserted f_bad_conclusion = Rejected 0 (R_body_mismatch 1)"
  by eval

lemma fx_bad_premise:
  "run_check f_builtin_rules f_asserted f_bad_premise = Rejected 0 (R_premise_unknown 0)"
  by eval

lemma fx_bad_self:
  "run_check f_builtin_rules f_asserted f_bad_self = Rejected 0 (R_body_mismatch 0)"
  by eval

section \<open>FINDING: bad_self.tsv does not test what its name says\<close>

(* bad_self.tsv is REJECTED by the strict discipline (above) and ACCEPTED by the lenient
   one (below), with the ABSOLUTE verdict.  That is not a bug in either: the instantiated
   body of rdfs9 under this binding is exactly the two triples of asserted.tsv, and the
   instantiated head is exactly the claimed conclusion, so the conclusion really is
   entailed and accepting it is SOUND (horn_certificate_sound_lenient says so).  The
   file's only defect is that its CITED premise list names its own conclusion instead of
   the asserted triple it actually used.

   Two consequences, both worth carrying into any differential test.
   1. This fixture does NOT exercise self-support.  It is caught by the positional
      premise check and by nothing else.  The property it is named for -- that a step
      cannot be discharged by a later step's conclusion -- CANNOT be tested by any
      single-line certificate, and every shipped certificate fixture is one line.
      isabelle/fixtures-added/bad_self_chain.tsv is the two-step test; see below.
   2. This is the sharpest predicted point of disagreement with any other
      implementation, and it lands on a SHIPPED fixture rather than on a hypothetical
      one.  An implementation that re-derives from the known set instead of comparing
      against the cited premises will ACCEPT bad_self.tsv.  Such an implementation is
      not unsound; it is less strict.  Do not "fix" the stricter one. *)

lemma fx_bad_self_is_accepted_leniently:
  "run_check_lenient f_builtin_rules f_asserted f_bad_self = Ok Entailed"
  by eval

section \<open>Added fixtures: the properties the shipped set cannot reach\<close>

(* THE ONLY REAL TEST OF THE STRICT-PREFIX DISCIPLINE (M27, trap T8).  Two steps, in
   which step 0 cites step 1's conclusion as a premise.  Under strict prefix visibility
   the known set for step 0 is the asserted graph alone, so the forward reference is
   unknown and the certificate is rejected.  Under a closure pass -- build the graph plus
   all conclusions once, then check every step against it -- it would be ACCEPTED, and a
   two-step cycle could certify itself.  No single-line fixture can distinguish these. *)
lemma fx_chain_forward_reference_is_rejected:
  "run_check f_builtin_rules f_asserted_chain f_bad_self_chain
     = Rejected 0 (R_premise_unknown 0)"
  by eval

(* The control: the SAME two steps in dependency order are accepted.  This is what makes
   the previous lemma a test of ORDER rather than of content. *)
lemma fx_chain_in_order_is_accepted:
  "run_check f_builtin_rules f_asserted_chain f_good_chain = Ok Entailed"
  by eval

(* Conflict C11 isolated: premises transposed, both asserted.  Strict rejects, lenient
   accepts, and both are sound. *)
lemma fx_order_strict_rejects:
  "run_check f_builtin_rules f_asserted f_bad_order = Rejected 0 (R_body_mismatch 0)"
  by eval
lemma fx_order_lenient_accepts:
  "run_check_lenient f_builtin_rules f_asserted f_bad_order = Ok Entailed"
  by eval

(* Uncertainty U10 isolated: a duplicate binding key, with two different values.  map_of
   is silently first-wins, so a checker that does not test for duplicates accepts this.
   Rejecting is this formalisation's choice (M25) and it is a strictness, not a
   soundness requirement -- the lenient run accepts it and is still sound. *)
lemma fx_dup_key_strict_rejects:
  "run_check f_builtin_rules f_asserted f_bad_dup_key = Rejected 0 R_binding_dup_key"
  by eval
lemma fx_dup_key_lenient_accepts:
  "run_check_lenient f_builtin_rules f_asserted f_bad_dup_key = Ok Entailed"
  by eval

(* M2 and M31: a GENERALIZED triple.  rdfs7 with ?q bound to a blank node yields a
   conclusion with a blank node in PREDICATE position, which cannot be written in
   concrete RDF.  It is accepted, because no RDF well-formedness condition exists
   anywhere in this development.  An implementation that rejects it has imported a
   well-formedness side condition the specification does not state. *)
lemma fx_generalized_triple_is_accepted:
  "run_check f_builtin_rules f_asserted_gen f_generalized = Ok Entailed"
  by eval

section \<open>Strict implies lenient, checked on the data as well as proved\<close>

(* strict_implies_lenient is a theorem (OO_Sound).  These rows are the instances where
   the implication is strict, i.e. where lenient accepts and strict does not. *)
lemma fx_strictness_gap_is_exactly_three_rows:
  "(run_check_lenient f_builtin_rules f_asserted f_bad_self = Ok Entailed
    \<and> run_check_lenient f_builtin_rules f_asserted f_bad_order = Ok Entailed
    \<and> run_check_lenient f_builtin_rules f_asserted f_bad_dup_key = Ok Entailed)
   \<and> (run_check f_builtin_rules f_asserted f_bad_self \<noteq> Ok Entailed
      \<and> run_check f_builtin_rules f_asserted f_bad_order \<noteq> Ok Entailed
      \<and> run_check f_builtin_rules f_asserted f_bad_dup_key \<noteq> Ok Entailed)"
  by eval

end
