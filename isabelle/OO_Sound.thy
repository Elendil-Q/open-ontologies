(* OO_Sound.thy -- the generic soundness theorem.

   This is the only place the syntactic checker and the model theory meet.  The theorem
   needs NO case analysis over rules, because there is no per-rule structure left in the
   checker: a rule is data, and the rules are the user's assumption. *)

theory OO_Sound
  imports OO_Check OO_Semantics
begin

section \<open>Tier B: the finite binding and its total extension agree\<close>

lemma B1:
  assumes "ipat \<beta> p = Some t"
  shows "ap (tot_of \<beta>) p = t"
  using assms by (cases p) (auto simp: tot_of_def)

lemma B2:
  assumes "iptriple \<beta> tp = Some u"
  shows "apt (tot_of \<beta>) tp = u"
proof (cases tp rule: prod_cases3)
  case (fields s p q)
  then obtain a b c where
      A: "ipat \<beta> s = Some a" and Bb: "ipat \<beta> p = Some b" and C: "ipat \<beta> q = Some c"
      and U: "u = (a,b,c)"
    using assms by (auto split: option.splits)
  show ?thesis using fields U B1[OF A] B1[OF Bb] B1[OF C] by simp
qed

section \<open>Tier A: what the body check establishes\<close>

lemma body_strict_map:
  "body_strict \<beta> j bs ps = None \<Longrightarrow> map (apt (tot_of \<beta>)) bs = ps"
proof (induction bs arbitrary: j ps)
  case Nil
  then show ?case by (cases ps) auto
next
  case (Cons b bs)
  show ?case
  proof (cases ps)
    case Nil
    with Cons.prems show ?thesis by simp
  next
    case (Cons p ps')
    with Cons.prems have i: "iptriple \<beta> b = Some p"
      and r: "body_strict \<beta> (Suc j) bs ps' = None"
      by (auto split: if_splits)
    show ?thesis using Cons Cons.IH[OF r] B2[OF i] by simp
  qed
qed

lemma body_strict_inst:
  "body_strict \<beta> j bs ps = None \<Longrightarrow> \<forall>b \<in> set bs. iptriple \<beta> b \<noteq> None"
proof (induction bs arbitrary: j ps)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  show ?case
  proof (cases ps)
    case Nil
    with Cons.prems show ?thesis by simp
  next
    case (Cons p ps')
    with Cons.prems have i: "iptriple \<beta> b = Some p"
      and r: "body_strict \<beta> (Suc j) bs ps' = None"
      by (auto split: if_splits)
    have hb: "iptriple \<beta> b \<noteq> None" using i by simp
    show ?thesis
    proof (rule ballI)
      fix c assume "c \<in> set (b # bs)"
      then consider (hd) "c = b" | (tl) "c \<in> set bs" by auto
      then show "iptriple \<beta> c \<noteq> None"
      proof cases
        case hd with hb show ?thesis by simp
      next
        case tl with Cons.IH[OF r] show ?thesis by blast
      qed
    qed
  qed
qed

lemma premises_known_all:
  "premises_known K j ps = None \<Longrightarrow> \<forall>p \<in> set ps. p \<in> K"
  by (induction ps arbitrary: j) (auto split: if_splits)

section \<open>Tier C: one step, then the induction that IS the no-self-support property\<close>

lemma check_step_parts:
  assumes "check_step R K s = None"
  shows "sidx s < length R"
    and "body_strict (sbind s) 0 (rbody (R ! sidx s)) (sprem s) = None"
    and "premises_known K 0 (sprem s) = None"
    and "iptriple (sbind s) (rhead (R ! sidx s)) = Some (sconcl s)"
  using assms
  by (auto simp: check_step_def Let_def not_le split: if_splits option.splits)

lemma check_step_sound:
  assumes ok: "check_step R K s = None"
      and kn: "\<And>t. t \<in> K \<Longrightarrow> sat I t"
      and rl: "\<And>r. r \<in> set R \<Longrightarrow> sat_rule I r"
  shows "sat I (sconcl s)"
proof -
  note P = check_step_parts[OF ok]
  have rmem: "R ! sidx s \<in> set R" using P(1) by simp
  have body: "map (apt (tot_of (sbind s))) (rbody (R ! sidx s)) = sprem s"
    using P(2) by (rule body_strict_map)
  have prem: "\<forall>p \<in> set (sprem s). p \<in> K" using P(3) by (rule premises_known_all)
  have "\<forall>u \<in> set (rbody (R ! sidx s)). sat I (apt (tot_of (sbind s)) u)"
  proof
    fix u assume u: "u \<in> set (rbody (R ! sidx s))"
    then have "apt (tot_of (sbind s)) u \<in> set (sprem s)"
      using body by (metis image_eqI list.set_map)
    then have "apt (tot_of (sbind s)) u \<in> K" using prem by blast
    then show "sat I (apt (tot_of (sbind s)) u)" by (rule kn)
  qed
  then have "sat I (apt (tot_of (sbind s)) (rhead (R ! sidx s)))"
    using rl[OF rmem] by (simp add: sat_rule_def)
  then show ?thesis using B2[OF P(4)] by simp
qed

(* THE INDUCTION BELOW IS THE NO-SELF-SUPPORT PROPERTY.  It generalises over the known
   set K, and it is FALSE if check_from inserts the conclusion before checking the step:
   the step's own conclusion would then be available to discharge its own premises, and
   the hypothesis "every triple in K is true" would no longer be establishable at the
   recursive call.  There is no separate test for this; the proof is the test. *)

lemma check_from_sound:
  assumes "check_from R K j ss = None"
      and "\<And>t. t \<in> K \<Longrightarrow> sat I t"
      and "\<And>r. r \<in> set R \<Longrightarrow> sat_rule I r"
  shows "\<forall>s \<in> set ss. sat I (sconcl s)"
  using assms
proof (induction ss arbitrary: K j)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  from Cons.prems(1) have cs: "check_step R K s = None"
    and rest: "check_from R (insert (sconcl s) K) (Suc j) ss = None"
    by (auto split: option.splits)
  have h: "sat I (sconcl s)"
    using check_step_sound[OF cs Cons.prems(2) Cons.prems(3)] .
  have k': "\<And>t. t \<in> insert (sconcl s) K \<Longrightarrow> sat I t"
    using h Cons.prems(2) by auto
  show ?case using h Cons.IH[OF rest k' Cons.prems(3)] by simp
qed

section \<open>T1: the conditional verdict\<close>

theorem horn_certificate_sound:
  fixes G :: "triple list" and R :: rtable and C :: "hstep list"
  assumes ok: "check_cert R G C = None"
      and mem: "s \<in> set C"
  shows "entails_under TYPE('d) R (set G) (sconcl s)"
  unfolding entails_under_def
proof (intro allI impI)
  fix I :: "'d interp"
  assume rl: "\<forall>r \<in> set R. sat_rule I r" and m: "models I (set G)"
  have "\<forall>s \<in> set C. sat I (sconcl s)"
  proof (rule check_from_sound)
    show "check_from R (set G) 0 C = None" using ok by (simp add: check_cert_def)
    show "\<And>t. t \<in> set G \<Longrightarrow> sat I t" using m by (simp add: models_def)
    show "\<And>r. r \<in> set R \<Longrightarrow> sat_rule I r" using rl by blast
  qed
  then show "sat I (sconcl s)" using mem by blast
qed

section \<open>The lenient judgement is sound too, and strict implies lenient\<close>

(* Proving BOTH disciplines sound is what turns conflict C11 from a guess into a
   theorem: a differential disagreement on premise ORDER is then known in advance to be
   a difference of strictness with no soundness content, and neither side needs
   "fixing". *)

lemma body_lenient_sat:
  assumes "body_lenient \<beta> K j bs = None"
      and "\<And>t. t \<in> K \<Longrightarrow> sat I t"
  shows "\<forall>u \<in> set bs. sat I (apt (tot_of \<beta>) u)"
  using assms
proof (induction bs arbitrary: j)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  from Cons.prems(1) obtain t where
      i: "iptriple \<beta> b = Some t" and tK: "t \<in> K"
      and r: "body_lenient \<beta> K (Suc j) bs = None"
    by (auto split: option.splits if_splits)
  have "sat I (apt (tot_of \<beta>) b)" using B2[OF i] tK Cons.prems(2) by simp
  then show ?case using Cons.IH[OF r Cons.prems(2)] by simp
qed

lemma check_step_lenient_sound:
  assumes ok: "check_step_lenient R K s = None"
      and kn: "\<And>t. t \<in> K \<Longrightarrow> sat I t"
      and rl: "\<And>r. r \<in> set R \<Longrightarrow> sat_rule I r"
  shows "sat I (sconcl s)"
proof -
  from ok have idx: "sidx s < length R"
    by (auto simp: check_step_lenient_def Let_def not_le split: if_splits)
  from ok idx have bl: "body_lenient (sbind s) K 0 (rbody (R ! sidx s)) = None"
    and hd: "iptriple (sbind s) (rhead (R ! sidx s)) = Some (sconcl s)"
    by (auto simp: check_step_lenient_def Let_def split: if_splits option.splits)
  have rmem: "R ! sidx s \<in> set R" using idx by simp
  have "\<forall>u \<in> set (rbody (R ! sidx s)). sat I (apt (tot_of (sbind s)) u)"
    using body_lenient_sat[OF bl kn] .
  then have "sat I (apt (tot_of (sbind s)) (rhead (R ! sidx s)))"
    using rl[OF rmem] by (simp add: sat_rule_def)
  then show ?thesis using B2[OF hd] by simp
qed

lemma check_from_lenient_sound:
  assumes "check_from_lenient R K j ss = None"
      and "\<And>t. t \<in> K \<Longrightarrow> sat I t"
      and "\<And>r. r \<in> set R \<Longrightarrow> sat_rule I r"
  shows "\<forall>s \<in> set ss. sat I (sconcl s)"
  using assms
proof (induction ss arbitrary: K j)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  from Cons.prems(1) have cs: "check_step_lenient R K s = None"
    and rest: "check_from_lenient R (insert (sconcl s) K) (Suc j) ss = None"
    by (auto split: option.splits)
  have h: "sat I (sconcl s)"
    using check_step_lenient_sound[OF cs Cons.prems(2) Cons.prems(3)] .
  have k': "\<And>t. t \<in> insert (sconcl s) K \<Longrightarrow> sat I t" using h Cons.prems(2) by auto
  show ?case using h Cons.IH[OF rest k' Cons.prems(3)] by simp
qed

theorem horn_certificate_sound_lenient:
  fixes G :: "triple list" and R :: rtable and C :: "hstep list"
  assumes ok: "check_cert_lenient R G C = None"
      and mem: "s \<in> set C"
  shows "entails_under TYPE('d) R (set G) (sconcl s)"
  unfolding entails_under_def
proof (intro allI impI)
  fix I :: "'d interp"
  assume rl: "\<forall>r \<in> set R. sat_rule I r" and m: "models I (set G)"
  have "\<forall>s \<in> set C. sat I (sconcl s)"
  proof (rule check_from_lenient_sound)
    show "check_from_lenient R (set G) 0 C = None" using ok by (simp add: check_cert_lenient_def)
    show "\<And>t. t \<in> set G \<Longrightarrow> sat I t" using m by (simp add: models_def)
    show "\<And>r. r \<in> set R \<Longrightarrow> sat_rule I r" using rl by blast
  qed
  then show "sat I (sconcl s)" using mem by blast
qed

lemma body_strict_lenient:
  "body_strict \<beta> j bs ps = None \<Longrightarrow> \<forall>p \<in> set ps. p \<in> K \<Longrightarrow> body_lenient \<beta> K j' bs = None"
proof (induction bs arbitrary: j j' ps)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  show ?case
  proof (cases ps)
    case Nil
    with Cons.prems show ?thesis by simp
  next
    case (Cons p ps')
    with Cons.prems(1) have i: "iptriple \<beta> b = Some p"
      and r: "body_strict \<beta> (Suc j) bs ps' = None"
      by (auto split: if_splits)
    have pK: "p \<in> K" using Cons.prems(2) Cons by simp
    have "\<forall>q \<in> set ps'. q \<in> K" using Cons.prems(2) Cons by simp
    then show ?thesis using i pK Cons.IH[OF r] by simp
  qed
qed

lemma strict_implies_lenient_step:
  "check_step R K s = None \<Longrightarrow> check_step_lenient R K s = None"
proof -
  assume ok: "check_step R K s = None"
  note P = check_step_parts[OF ok]
  have "\<forall>p \<in> set (sprem s). p \<in> K" using P(3) by (rule premises_known_all)
  then have "body_lenient (sbind s) K 0 (rbody (R ! sidx s)) = None"
    using body_strict_lenient[OF P(2)] by blast
  then show ?thesis using P(1) P(4) by (simp add: check_step_lenient_def Let_def)
qed

lemma strict_implies_lenient_from:
  "check_from R K j ss = None \<Longrightarrow> check_from_lenient R K j ss = None"
proof (induction ss arbitrary: K j)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  from Cons.prems have cs: "check_step R K s = None"
    and rest: "check_from R (insert (sconcl s) K) (Suc j) ss = None"
    by (auto split: option.splits)
  show ?case
    using strict_implies_lenient_step[OF cs] Cons.IH[OF rest] by simp
qed

theorem strict_implies_lenient:
  "check_cert R G C = None \<Longrightarrow> check_cert_lenient R G C = None"
  by (simp add: check_cert_def check_cert_lenient_def strict_implies_lenient_from)

section \<open>The coverage check adds no strictness (M25, first half)\<close>

(* binding_covers is checked BEFORE the body and head checks, so it changes which REASON
   a rejected certificate is given.  It cannot change the ACCEPT/REJECT bit, because the
   body and head checks already force every variable occurring in the rule to be bound.
   Recorded because over-checking (trap T11) manufactures differential disagreements that
   consume review time and find nothing; this one provably cannot. *)

lemma ipat_covers:
  "ipat \<beta> p \<noteq> None \<Longrightarrow> \<forall>v \<in> set (pat_vars1 p). map_of \<beta> v \<noteq> None"
  by (cases p) auto

lemma iptriple_parts:
  "iptriple \<beta> (s,p,q) \<noteq> None
     \<Longrightarrow> ipat \<beta> s \<noteq> None \<and> ipat \<beta> p \<noteq> None \<and> ipat \<beta> q \<noteq> None"
  by (auto split: option.splits)

lemma iptriple_covers:
  "iptriple \<beta> tp \<noteq> None \<Longrightarrow> \<forall>v \<in> set (pat_var_list tp). map_of \<beta> v \<noteq> None"
proof (cases tp rule: prod_cases3)
  case (fields s p q)
  assume "iptriple \<beta> tp \<noteq> None"
  with fields have "ipat \<beta> s \<noteq> None \<and> ipat \<beta> p \<noteq> None \<and> ipat \<beta> q \<noteq> None"
    using iptriple_parts by simp
  then show ?thesis using fields ipat_covers by auto
qed

lemma coverage_implied:
  assumes bs: "body_strict \<beta> 0 (rbody r) ps = None"
      and hd: "iptriple \<beta> (rhead r) = Some t"
  shows "binding_covers \<beta> r"
proof -
  have "\<forall>b \<in> set (rbody r). iptriple \<beta> b \<noteq> None"
    using bs by (rule body_strict_inst)
  then have body: "\<forall>b \<in> set (rbody r). \<forall>v \<in> set (pat_var_list b). map_of \<beta> v \<noteq> None"
    using iptriple_covers by blast
  have head: "\<forall>v \<in> set (pat_var_list (rhead r)). map_of \<beta> v \<noteq> None"
    using hd by (intro iptriple_covers) simp
  show ?thesis
    unfolding binding_covers_def rule_var_list_def
    using body head by (auto simp: list_all_iff)
qed

end
