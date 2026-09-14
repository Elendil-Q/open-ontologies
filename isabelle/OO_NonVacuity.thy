(* OO_NonVacuity.thy -- the conditions are satisfiable, and satisfiable NON-DEGENERATELY.

   A soundness theorem over an unsatisfiable model class proves nothing: if no
   interpretation met the 26 conditions, every triple would be entailed and the checker
   could accept anything.  That is the standing obligation.  It is easy to discharge
   BADLY, and this file is arranged so that the bad discharge is visible.

   THE WEAK WITNESS, and why it is not enough.  The one-point interpretation W (below)
   satisfies every condition, so the class is non-empty.  But W makes ICEXT constant and
   IC the whole universe, so c_sco_bwd, c_dom_bwd and c_rng_bwd -- the BACKWARD halves of
   RBS Table 5.8, which twelve of the 27 arms depend on -- are satisfied by collapse
   rather than by construction.  Worse, the only triple W fails to satisfy is one whose
   subject is a LITERAL with no denotation, so the refutation turns entirely on the
   partiality of IL (M3) and says nothing about the IRI-only case, which is the
   interesting one.

   THE REAL WITNESS is M3.  It is a model of the ACTUAL FIXTURE GRAPH
   tests/fixtures/horn/asserted.tsv; it has IC non-empty, so the Table 5.8 backward
   conditions are LIVE rather than vacuous; it satisfies the conclusion the fixture
   certificate derives, as soundness requires; and it refutes an IRI-only triple over
   that same non-empty graph. *)

theory OO_NonVacuity
  imports OO_Builtin_Sound
begin

section \<open>N1: the weak witness, recorded with its weakness\<close>

definition W :: "unit interp" where
  "W = \<lparr> IR = UNIV, IP = UNIV, IEXT = (\<lambda>x. UNIV),
         IS = (\<lambda>u. ()), IB = (\<lambda>b. ()), IL = (\<lambda>l. None) \<rparr>"

lemma W_simps [simp]:
  "IR W = UNIV" "IP W = UNIV" "IEXT W x = UNIV"
  "IS W u = ()" "IB W b = ()" "IL W l = None"
  by (simp_all add: W_def)

lemma W_ICEXT [simp]: "ICEXT W y = UNIV" by (simp add: ICEXT_def)
lemma W_IC [simp]: "IC W = UNIV" by (simp add: IC_def)

theorem conditions_satisfiable: "owl_rl_interp W"
  by (simp add: owl_rl_interp_def
      c_type_IP_def c_sco_IP_def c_spo_IP_def
      c_sco_fwd_def c_sco_bwd_def c_spo_fwd_def c_spo_bwd_def
      c_sco_trans_def c_spo_trans_def
      c_dom_fwd_def c_dom_bwd_def c_rng_fwd_def c_rng_bwd_def
      c_sameAs_fwd_def c_eqc_fwd_def c_eqp_fwd_def c_inv_fwd_def
      c_sym_fwd_def c_trp_fwd_def c_svf_def c_avf_def c_hv_def
      c_restr_IC_def c_svf_typ_def c_avf_typ_def c_onp_typ_def)

(* W also satisfies the domain conditions, so the model class stays non-empty when the
   bridge theorem T4 adds them back. *)
lemma W_wf: "wf_interp W" by (simp add: wf_interp_def)

section \<open>The fixture IRIs, transcribed from tests/fixtures/horn/asserted.tsv\<close>

(* Angle brackets stripped: see DECISION D-PARSE-2 in OO_Parse.  ex_C does not occur in
   any fixture; it is the fresh IRI whose triple M3 refutes. *)

definition ex_a :: string where "ex_a = ''http://ex.org/a''"
definition ex_A :: string where "ex_A = ''http://ex.org/A''"
definition ex_B :: string where "ex_B = ''http://ex.org/B''"
definition ex_C :: string where "ex_C = ''http://ex.org/C''"

definition fixture_graph :: "triple list" where
  "fixture_graph = [ (Iri ex_a, Iri rdf_type, Iri ex_A),
                     (Iri ex_A, Iri rdfs_subClassOf, Iri ex_B) ]"

section \<open>N3: a non-degenerate model of the fixture graph\<close>

(* THE CONSTRUCTION, AND WHY IT IS NOT OBVIOUS.  Once IC is non-empty the backward halves
   of Table 5.8 bite, and they are close to circular: c_spo_bwd forces
   (p1,p2) into IEXT(I(rdfs:subPropertyOf)) whenever p1, p2 are in IP and IEXT p1 is
   contained in IEXT p2 -- and I(rdfs:subPropertyOf) is itself in IP, by c_spo_IP, so the
   set being defined occurs on both sides of its own defining condition, once
   monotonically and once antitonically.  A naive "collapse everything" interpretation
   does not solve it.

   The circularity is broken by SEPARATING THE KINDS.  Property elements, class elements,
   the individual and the junk element are distinct constructors, and the three property
   extensions T3, S3, Q3 live in disjoint parts of the pair space.  Then no two of them
   are comparable under containment except reflexively, the defining condition for Q3
   collapses to the DIAGONAL on IP, and the diagonal is a fixpoint of it.  Verified
   below, case by case, rather than asserted.

   Every unused vocabulary IRI is sent to the single junk element zz with EMPTY
   extension.  That is what makes sameAs, equivalentClass, equivalentProperty, inverseOf,
   someValuesFrom, allValuesFrom, hasValue, onProperty, domain, range, Restriction,
   SymmetricProperty and TransitiveProperty all vacuous at once -- and it is sound
   precisely because nothing in the condition set FORCES a pair into any of those
   extensions.  Checked: only c_sco_bwd, c_spo_bwd, c_dom_bwd and c_rng_bwd have a
   consequent that asserts membership, and their consequents name subClassOf,
   subPropertyOf, domain and range.  domain and range are handled by showing their
   antecedents false. *)

datatype E = pT | pS | pQ | cA | cB | cls | ia | zz

definition T3 :: "(E \<times> E) set" where
  "T3 = {(ia,cA), (ia,cB), (cA,cls), (cB,cls)}"
definition S3 :: "(E \<times> E) set" where
  "S3 = {(cA,cA), (cA,cB), (cB,cA), (cB,cB)}"
definition Q3 :: "(E \<times> E) set" where
  "Q3 = {(pT,pT), (pS,pS), (pQ,pQ)}"

definition M3 :: "E interp" where
  "M3 = \<lparr> IR = UNIV,
          IP = {pT, pS, pQ},
          IEXT = (\<lambda>x. if x = pT then T3 else if x = pS then S3
                      else if x = pQ then Q3 else {}),
          IS = (\<lambda>u. if u = ex_a then ia
                    else if u = ex_A then cA
                    else if u = ex_B then cB
                    else if u = rdf_type then pT
                    else if u = rdfs_subClassOf then pS
                    else if u = rdfs_subPropertyOf then pQ
                    else if u = rdfs_Class then cls
                    else zz),
          IB = (\<lambda>b. zz),
          IL = (\<lambda>l. None) \<rparr>"

lemma M3_IP [simp]: "IP M3 = {pT, pS, pQ}" by (simp add: M3_def)
lemma M3_IR [simp]: "IR M3 = UNIV" by (simp add: M3_def)
lemma M3_IB [simp]: "IB M3 b = zz" by (simp add: M3_def)
lemma M3_IL [simp]: "IL M3 l = None" by (simp add: M3_def)

lemma M3_IEXT [simp]:
  "IEXT M3 pT = T3" "IEXT M3 pS = S3" "IEXT M3 pQ = Q3"
  "IEXT M3 cA = {}" "IEXT M3 cB = {}" "IEXT M3 cls = {}"
  "IEXT M3 ia = {}" "IEXT M3 zz = {}"
  by (simp_all add: M3_def)

lemma M3_IS [simp]:
  "IS M3 ex_a = ia" "IS M3 ex_A = cA" "IS M3 ex_B = cB"
  "IS M3 rdf_type = pT" "IS M3 rdfs_subClassOf = pS"
  "IS M3 rdfs_subPropertyOf = pQ" "IS M3 rdfs_Class = cls"
  "IS M3 ex_C = zz"
  "IS M3 rdfs_domain = zz" "IS M3 rdfs_range = zz"
  "IS M3 owl_sameAs = zz" "IS M3 owl_equivalentClass = zz"
  "IS M3 owl_equivalentProperty = zz" "IS M3 owl_inverseOf = zz"
  "IS M3 owl_SymmetricProperty = zz" "IS M3 owl_TransitiveProperty = zz"
  "IS M3 owl_Restriction = zz" "IS M3 owl_onProperty = zz"
  "IS M3 owl_someValuesFrom = zz" "IS M3 owl_allValuesFrom = zz"
  "IS M3 owl_hasValue = zz"
  by (simp_all add: M3_def ex_a_def ex_A_def ex_B_def ex_C_def
      rdf_type_def rdfs_Class_def rdfs_subClassOf_def rdfs_subPropertyOf_def
      rdfs_domain_def rdfs_range_def owl_sameAs_def owl_equivalentClass_def
      owl_equivalentProperty_def owl_inverseOf_def owl_SymmetricProperty_def
      owl_TransitiveProperty_def owl_Restriction_def owl_onProperty_def
      owl_someValuesFrom_def owl_allValuesFrom_def owl_hasValue_def)

lemma M3_ICEXT_raw: "ICEXT M3 y = {x. (x,y) \<in> T3}"
  by (simp add: ICEXT_def)

lemma M3_ICEXT [simp]:
  "ICEXT M3 pT = {}" "ICEXT M3 pS = {}" "ICEXT M3 pQ = {}"
  "ICEXT M3 cA = {ia}" "ICEXT M3 cB = {ia}" "ICEXT M3 cls = {cA, cB}"
  "ICEXT M3 ia = {}" "ICEXT M3 zz = {}"
  by (auto simp: M3_ICEXT_raw T3_def)

lemma M3_IC [simp]: "IC M3 = {cA, cB}" by (simp add: IC_def)

subsection \<open>Each condition, discharged separately so a failure names itself\<close>

lemma M3_type_IP: "c_type_IP M3" by (simp add: c_type_IP_def)
lemma M3_sco_IP:  "c_sco_IP M3"  by (simp add: c_sco_IP_def)
lemma M3_spo_IP:  "c_spo_IP M3"  by (simp add: c_spo_IP_def)

lemma M3_sco_fwd: "c_sco_fwd M3"
  unfolding c_sco_fwd_def by (auto simp: S3_def)

lemma M3_sco_bwd: "c_sco_bwd M3"
  unfolding c_sco_bwd_def by (auto simp: S3_def)

lemma M3_sco_trans: "c_sco_trans M3"
  unfolding c_sco_trans_def by (auto simp: S3_def)

(* The fixpoint.  Q3 is exactly the diagonal on IP, and the nine cases below are the
   check that it IS a fixpoint of the condition rather than merely a plausible guess. *)
lemma M3_spo_fwd: "c_spo_fwd M3"
  unfolding c_spo_fwd_def by (auto simp: Q3_def)

lemma M3_spo_bwd: "c_spo_bwd M3"
  unfolding c_spo_bwd_def
proof (intro allI impI)
  fix p1 p2 :: E
  assume a1: "p1 \<in> IP M3" and a2: "p2 \<in> IP M3" and sub: "IEXT M3 p1 \<subseteq> IEXT M3 p2"
  from a1 have c1: "p1 = pT \<or> p1 = pS \<or> p1 = pQ" by auto
  from a2 have c2: "p2 = pT \<or> p2 = pS \<or> p2 = pQ" by auto
  from c1 c2 sub show "(p1,p2) \<in> IEXT M3 (IS M3 rdfs_subPropertyOf)"
    by (elim disjE) (auto simp: T3_def S3_def Q3_def)
qed

lemma M3_spo_trans: "c_spo_trans M3"
  unfolding c_spo_trans_def by (auto simp: Q3_def)

(* domain and range: the extension of the junk element is empty, so the consequent is
   False, and the proof must show the ANTECEDENT is false for every p in IP and c in IC.
   It is, because every property extension has a first (resp. second) component outside
   ICEXT cA = ICEXT cB = {ia}. *)
lemma M3_dom_fwd: "c_dom_fwd M3" unfolding c_dom_fwd_def by simp
lemma M3_rng_fwd: "c_rng_fwd M3" unfolding c_rng_fwd_def by simp

lemma M3_dom_bwd: "c_dom_bwd M3"
  unfolding c_dom_bwd_def
proof (intro allI impI)
  fix p c :: E
  assume a1: "p \<in> IP M3" and a2: "c \<in> IC M3"
    and h: "\<forall>x y. (x,y) \<in> IEXT M3 p \<longrightarrow> x \<in> ICEXT M3 c"
  have icx: "ICEXT M3 c = {ia}" using a2 by auto
  have False
  proof -
    from a1 consider (t) "p = pT" | (s) "p = pS" | (q) "p = pQ" by auto
    then show False
    proof cases
      case t
      have m: "(cA, cls) \<in> IEXT M3 p" using t by (simp add: T3_def)
      from h m have "cA \<in> ICEXT M3 c" by blast
      with icx show False by simp
    next
      case s
      have m: "(cA, cA) \<in> IEXT M3 p" using s by (simp add: S3_def)
      from h m have "cA \<in> ICEXT M3 c" by blast
      with icx show False by simp
    next
      case q
      have m: "(pT, pT) \<in> IEXT M3 p" using q by (simp add: Q3_def)
      from h m have "pT \<in> ICEXT M3 c" by blast
      with icx show False by simp
    qed
  qed
  then show "(p,c) \<in> IEXT M3 (IS M3 rdfs_domain)" by simp
qed

lemma M3_rng_bwd: "c_rng_bwd M3"
  unfolding c_rng_bwd_def
proof (intro allI impI)
  fix p c :: E
  assume a1: "p \<in> IP M3" and a2: "c \<in> IC M3"
    and h: "\<forall>x y. (x,y) \<in> IEXT M3 p \<longrightarrow> y \<in> ICEXT M3 c"
  have icx: "ICEXT M3 c = {ia}" using a2 by auto
  have False
  proof -
    from a1 consider (t) "p = pT" | (s) "p = pS" | (q) "p = pQ" by auto
    then show False
    proof cases
      case t
      have m: "(ia, cA) \<in> IEXT M3 p" using t by (simp add: T3_def)
      from h m have "cA \<in> ICEXT M3 c" by blast
      with icx show False by simp
    next
      case s
      have m: "(cA, cA) \<in> IEXT M3 p" using s by (simp add: S3_def)
      from h m have "cA \<in> ICEXT M3 c" by blast
      with icx show False by simp
    next
      case q
      have m: "(pT, pT) \<in> IEXT M3 p" using q by (simp add: Q3_def)
      from h m have "pT \<in> ICEXT M3 c" by blast
      with icx show False by simp
    qed
  qed
  then show "(p,c) \<in> IEXT M3 (IS M3 rdfs_range)" by simp
qed

lemma M3_sameAs_fwd: "c_sameAs_fwd M3" unfolding c_sameAs_fwd_def by simp
lemma M3_eqc_fwd: "c_eqc_fwd M3" unfolding c_eqc_fwd_def by simp
lemma M3_eqp_fwd: "c_eqp_fwd M3" unfolding c_eqp_fwd_def by simp
lemma M3_inv_fwd: "c_inv_fwd M3" unfolding c_inv_fwd_def by simp
lemma M3_sym_fwd: "c_sym_fwd M3" unfolding c_sym_fwd_def by simp
lemma M3_trp_fwd: "c_trp_fwd M3" unfolding c_trp_fwd_def by simp
lemma M3_svf: "c_svf M3" unfolding c_svf_def by simp
lemma M3_avf: "c_avf M3" unfolding c_avf_def by simp
lemma M3_hv: "c_hv M3" unfolding c_hv_def by simp
lemma M3_restr_IC: "c_restr_IC M3" unfolding c_restr_IC_def by simp
lemma M3_svf_typ: "c_svf_typ M3" unfolding c_svf_typ_def by simp
lemma M3_avf_typ: "c_avf_typ M3" unfolding c_avf_typ_def by simp
lemma M3_onp_typ: "c_onp_typ M3" unfolding c_onp_typ_def by simp

theorem M3_is_a_model: "owl_rl_interp M3"
  unfolding owl_rl_interp_def
  by (simp add: M3_type_IP M3_sco_IP M3_spo_IP M3_sco_fwd M3_sco_bwd
      M3_spo_fwd M3_spo_bwd M3_sco_trans M3_spo_trans
      M3_dom_fwd M3_dom_bwd M3_rng_fwd M3_rng_bwd
      M3_sameAs_fwd M3_eqc_fwd M3_eqp_fwd M3_inv_fwd M3_sym_fwd M3_trp_fwd
      M3_svf M3_avf M3_hv M3_restr_IC M3_svf_typ M3_avf_typ M3_onp_typ)

(* M3 also satisfies the domain conditions of RBS Table 5.1, so it witnesses
   satisfiability for the bridge theorem T4 as well as for entails. *)
theorem M3_wf: "wf_interp M3" by (simp add: wf_interp_def)

(* THE POINT OF M3: the Table 5.8 backward conditions are LIVE in it, not vacuous.  A
   witness with IC empty satisfies c_sco_bwd, c_dom_bwd and c_rng_bwd by having nothing
   to quantify over, and therefore provides NO evidence that those conditions -- which
   twelve of the 27 arms depend on -- are jointly satisfiable alongside the rest. *)
theorem M3_is_not_degenerate:
  "IC M3 \<noteq> {}" and "ICEXT M3 cA \<noteq> {}" and "IEXT M3 (IS M3 rdfs_subClassOf) \<noteq> {}"
  by (simp_all add: S3_def)

subsection \<open>What M3 makes true, and what it makes false\<close>

lemma M3_sat_asserted_1: "sat M3 (Iri ex_a, Iri rdf_type, Iri ex_A)"
  by (simp add: T3_def)
lemma M3_sat_asserted_2: "sat M3 (Iri ex_A, Iri rdfs_subClassOf, Iri ex_B)"
  by (simp add: S3_def)

theorem M3_models_fixture_graph: "models M3 (set fixture_graph)"
  by (simp add: models_def fixture_graph_def T3_def S3_def)

(* Consistency check on the whole development: the conclusion the fixture certificate
   good.tsv derives by rdfs9 MUST be true here, since soundness says so.  If this failed,
   either the checker or the semantics would be wrong. *)
theorem M3_sat_the_certified_conclusion: "sat M3 (Iri ex_a, Iri rdf_type, Iri ex_B)"
  by (simp add: T3_def)

(* Refutation 1: an IRI-only triple, over the NON-EMPTY fixture graph.  Nothing here
   turns on the partiality of IL. *)
theorem M3_refutes_fresh_class: "\<not> sat M3 (Iri ex_a, Iri rdf_type, Iri ex_C)"
  by (simp add: T3_def)

(* Refutation 2: exercises the IP clause of the truth condition (M5) specifically.  The
   predicate owl:sameAs denotes zz, which is not in IP, so the triple is false however
   its subject and object are related.  Under a truth clause that omits the IP
   requirement this triple would be false only for a different reason, and under one that
   cases on the predicate it might not be false at all. *)
theorem M3_refutes_sameAs: "\<not> sat M3 (Iri ex_a, Iri owl_sameAs, Iri ex_a)"
  by simp

section \<open>The headline non-vacuity results\<close>

theorem entailment_is_not_trivial:
  "\<not> entails TYPE(E) (set fixture_graph) (Iri ex_a, Iri rdf_type, Iri ex_C)"
  unfolding entails_def
  using M3_is_a_model M3_models_fixture_graph M3_refutes_fresh_class by blast

(* Entailment from a larger graph is easier, so a refutation over the fixture graph
   gives the empty-graph refutation for free.  Recorded because the brief's suggested
   separate empty-graph witness is subsumed by this one. *)
theorem entailment_is_not_trivial_empty:
  "\<not> entails TYPE(E) {} (Iri ex_a, Iri rdf_type, Iri ex_C)"
  unfolding entails_def
  using M3_is_a_model M3_refutes_fresh_class by (auto simp: models_def)

theorem the_IP_clause_has_content:
  "\<not> entails TYPE(E) (set fixture_graph) (Iri ex_a, Iri owl_sameAs, Iri ex_a)"
  unfolding entails_def
  using M3_is_a_model M3_models_fixture_graph M3_refutes_sameAs by blast

end
