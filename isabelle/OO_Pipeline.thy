(* OO_Pipeline.thy -- what the TOOL's output means, as opposed to what the checker's
   output means.  This is the theorem a user of the binary actually relies on: if the
   report says "entailed", the conclusion of every step is entailed by the asserted
   graph. *)

theory OO_Pipeline
  imports OO_Parse OO_Builtin_Sound
begin

lemma run_check_accepts:
  assumes ok: "run_check rl gl cl = Ok v"
      and pr: "parse_rules rl = Some R"
      and pg: "parse_graph gl = Some G"
      and pc: "parse_cert cl = Some C"
  shows "check_cert R G C = None \<and> v = verdict_of R"
  using assms by (simp add: run_check_def split: option.splits prod.splits)

lemma run_check_lenient_accepts:
  assumes ok: "run_check_lenient rl gl cl = Ok v"
      and pr: "parse_rules rl = Some R"
      and pg: "parse_graph gl = Some G"
      and pc: "parse_cert cl = Some C"
  shows "check_cert_lenient R G C = None \<and> v = verdict_of R"
  using assms by (simp add: run_check_lenient_def split: option.splits prod.splits)

(* The conditional guarantee: whatever table was supplied, every certified conclusion
   holds in every interpretation that satisfies the asserted graph AND those rules. *)
theorem run_check_sound:
  assumes ok: "run_check rl gl cl = Ok v"
      and pr: "parse_rules rl = Some R"
      and pg: "parse_graph gl = Some G"
      and pc: "parse_cert cl = Some C"
      and mem: "s \<in> set C"
  shows "entails_under TYPE('d) R (set G) (sconcl s)"
proof -
  have chk: "check_cert R G C = None" using run_check_accepts[OF ok pr pg pc] by simp
  show ?thesis by (rule horn_certificate_sound[OF chk mem])
qed

(* THE ABSOLUTE GUARANTEE, and the only one that may be read as a claim about the world.
   Note that R does not appear: the verdict word Entailed is itself what establishes
   that the supplied table was the built-in one (T5), so a reader of the report does not
   have to take the rule file on trust. *)
theorem run_check_entailed_sound:
  assumes ok: "run_check rl gl cl = Ok Entailed"
      and pr: "parse_rules rl = Some R"
      and pg: "parse_graph gl = Some G"
      and pc: "parse_cert cl = Some C"
      and mem: "s \<in> set C"
  shows "entails TYPE('d) (set G) (sconcl s)"
proof -
  from run_check_accepts[OF ok pr pg pc]
  have chk: "check_cert R G C = None" and v: "Entailed = verdict_of R" by auto
  from v have RB: "R = builtin_table" using verdict_honest by metis
  from chk RB have "check_cert builtin_table G C = None" by simp
  then show ?thesis by (rule entails_of_builtin[OF _ mem])
qed

theorem run_check_lenient_entailed_sound:
  assumes ok: "run_check_lenient rl gl cl = Ok Entailed"
      and pr: "parse_rules rl = Some R"
      and pg: "parse_graph gl = Some G"
      and pc: "parse_cert cl = Some C"
      and mem: "s \<in> set C"
  shows "entails TYPE('d) (set G) (sconcl s)"
proof -
  from run_check_lenient_accepts[OF ok pr pg pc]
  have chk: "check_cert_lenient R G C = None" and v: "Entailed = verdict_of R" by auto
  from v have RB: "R = builtin_table" using verdict_honest by metis
  from chk RB have "check_cert_lenient builtin_table G C = None" by simp
  then show ?thesis by (rule entails_of_builtin_lenient[OF _ mem])
qed

end
