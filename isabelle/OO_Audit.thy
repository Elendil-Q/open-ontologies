(* OO_Audit.thy -- a build gate on the trust surface.

   In Isabelle the analogue of pinning a Lean theorem's axiom list is to check what
   ORACLES a theorem's proof term depends on.  "sorry" is the oracle Pure.skip_proof, so
   a sorry anywhere beneath a theorem shows up here; so does any use of eval,
   normalization, or an external prover invoked as an oracle.

   The first block FAILS THE BUILD if any soundness or non-vacuity theorem depends on an
   oracle.  The second block fails the build if an eval-proved lemma does NOT show an
   oracle -- because a gate that cannot fail is decoration. *)

theory OO_Audit
  imports OO_Fixtures OO_NonVacuity
begin

ML \<open>
  let
    val ths =
      [@{thm horn_certificate_sound},
       @{thm horn_certificate_sound_lenient},
       @{thm entails_of_builtin},
       @{thm entails_of_builtin_lenient},
       @{thm entails_simple},
       @{thm builtin_table_sound},
       @{thm verdict_honest},
       @{thm a_user_rule_never_earns_the_absolute_verdict},
       @{thm strict_implies_lenient},
       @{thm coverage_implied},
       @{thm check_step_sound},
       @{thm check_from_sound},
       @{thm run_check_sound},
       @{thm run_check_entailed_sound},
       @{thm run_check_lenient_entailed_sound},
       @{thm conditions_satisfiable},
       @{thm M3_is_a_model},
       @{thm M3_wf},
       @{thm M3_models_fixture_graph},
       @{thm M3_sat_the_certified_conclusion},
       @{thm M3_refutes_fresh_class},
       @{thm M3_refutes_sameAs},
       @{thm entailment_is_not_trivial},
       @{thm entailment_is_not_trivial_empty},
       @{thm the_IP_clause_has_content}]
      @ @{thms M3_is_not_degenerate}
    val oracles = Thm_Deps.all_oracles ths
    val names = map (fn ((n, _), _) => n) oracles
  in
    if null oracles
    then File.write (Path.explode "/tmp/oo_audit_result.txt")
           ("ORACLE AUDIT PASSED: " ^ string_of_int (length ths) ^
            " soundness and non-vacuity theorems checked; oracle set is EMPTY.\n")
    else error ("ORACLE AUDIT FAILED -- these theorems depend on oracles: " ^ commas names)
  end
\<close>

ML \<open>
  let
    val oracles = Thm_Deps.all_oracles [@{thm fx_good_builtin}]
    val names = map (fn ((n, _), _) => n) oracles
  in
    if null oracles
    then error ("ORACLE AUDIT IS BROKEN: an eval-proved lemma reports no oracle, so the " ^
                "audit above cannot distinguish a kernel proof from an evaluation and " ^
                "is decoration.")
    else File.append (Path.explode "/tmp/oo_audit_result.txt")
           ("GATE PROVED ABLE TO FAIL: eval-proved fixture lemmas do carry an oracle (" ^
            commas names ^ "); none of the theorems above does.\n")
  end
\<close>

end
