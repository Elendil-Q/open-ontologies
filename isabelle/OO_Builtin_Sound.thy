(* OO_Builtin_Sound.thy -- every arm of the built-in table is sound in the conditioned
   model class, and therefore the absolute verdict.

   THIS IS THE FILE THAT CARRIES THE INDEPENDENT CONTENT.  The rule table itself is
   shared input (M40): it was transcribed from the fixture, so two formalisations will
   have the same rows whatever they believe.  What is NOT shared is WHICH SEMANTIC
   CONDITIONS EACH ARM CONSUMES.  A semantics that is stronger than the specification
   discharges MORE arms, and discharges them MORE EASILY.  If every arm below were
   trivial, that would be evidence of a bug, not of quality.

   The derived lemmas are arranged so that the condition-to-derived-lemma map is
   ONE-TO-ONE: each D_ lemma is a one-line consequence of exactly ONE named condition
   (or, where marked, of exactly two).  That is where a reviewer checks that no extra
   strength crept in between a condition and its use.

   THE CONSUMPTION MAP.  Every arm, every condition it needs, nothing more.
   Conditions in CAPITALS are the ones that would silently disappear under a weaker
   truth clause (M5) or without the Table 5.2/5.3 typing rows (M17).

     rdfs2       c_dom_fwd, C_TYPE_IP
     rdfs3       c_rng_fwd, C_TYPE_IP
     rdfs5       c_spo_trans, C_SPO_IP
     rdfs7       c_spo_fwd                     (head predicate ?q enters IP via c_spo_fwd)
     rdfs9       c_sco_fwd, C_TYPE_IP
     rdfs11      c_sco_trans, C_SCO_IP
     prp-trp     c_trp_fwd                     (head predicate ?p is a body predicate)
     prp-symp    c_sym_fwd                     (likewise)
     prp-inv1    c_inv_fwd, both inclusions of its set equality, and its IP conjuncts
     prp-inv2    c_inv_fwd, the other inclusion, and its IP conjuncts
     eq-sym      c_sameAs_fwd                  (sameAs enters IP from the premise itself)
     scm-eqc1 a  c_eqc_fwd, c_sco_bwd, C_SCO_IP
     scm-eqc1 b  c_eqc_fwd, c_sco_bwd, C_SCO_IP
     scm-eqp1 a  c_eqp_fwd, c_spo_bwd, C_SPO_IP
     scm-eqp1 b  c_eqp_fwd, c_spo_bwd, C_SPO_IP
     cls-svf1    c_svf, SUPERSET half, C_TYPE_IP
     cls-avf     c_avf, SUBSET half, C_TYPE_IP
     cls-hv1     c_hv, SUBSET half, C_ONP_TYP  (the only source of p in IP for the head)
     cls-hv2     c_hv, SUPERSET half, C_TYPE_IP
     scm-svf1    c_svf both halves (two instances), c_sco_fwd, c_sco_bwd,
                 C_SVF_TYP, C_RESTR_IC, C_SCO_IP
     scm-svf2    c_svf both halves, c_spo_fwd, c_sco_bwd, C_SVF_TYP, C_RESTR_IC, C_SCO_IP
     scm-avf1    c_avf both halves, c_sco_fwd, c_sco_bwd, C_AVF_TYP, C_RESTR_IC, C_SCO_IP
     scm-avf2    c_avf both halves, c_spo_fwd, c_sco_bwd, C_AVF_TYP, C_RESTR_IC, C_SCO_IP
                 -- HEAD REVERSED, see D_avf_mono2
     scm-dom1    c_dom_fwd, c_sco_fwd, c_dom_bwd
     scm-dom2    c_dom_fwd, c_spo_fwd, c_dom_bwd
     scm-rng1    c_rng_fwd, c_sco_fwd, c_rng_bwd
     scm-rng2    c_rng_fwd, c_spo_fwd, c_rng_bwd

   Twelve arms (scm-eqc1 x2, scm-eqp1 x2, scm-svf1, scm-svf2, scm-avf1, scm-avf2,
   scm-dom1, scm-dom2, scm-rng1, scm-rng2) consume a BACKWARD half of RBS Table 5.8.
   They are unprovable without it.  That is the sharpest single prediction this
   formalisation makes about any other formalisation of the same table. *)

theory OO_Builtin_Sound
  imports OO_Sound
begin

section \<open>Derived forms of the semantic conditions\<close>

lemma D_type_IP: "owl_rl_interp I \<Longrightarrow> IS I rdf_type \<in> IP I"
  by (simp add: owl_rl_interp_def c_type_IP_def)
lemma D_sco_IP: "owl_rl_interp I \<Longrightarrow> IS I rdfs_subClassOf \<in> IP I"
  by (simp add: owl_rl_interp_def c_sco_IP_def)
lemma D_spo_IP: "owl_rl_interp I \<Longrightarrow> IS I rdfs_subPropertyOf \<in> IP I"
  by (simp add: owl_rl_interp_def c_spo_IP_def)

lemma D_dom:
  "\<lbrakk>owl_rl_interp I; (p,c) \<in> IEXT I (IS I rdfs_domain); (x,y) \<in> IEXT I p\<rbrakk>
     \<Longrightarrow> (x,c) \<in> IEXT I (IS I rdf_type)"
  by (auto simp: owl_rl_interp_def c_dom_fwd_def ICEXT_def)
lemma D_dom_IP: "\<lbrakk>owl_rl_interp I; (p,c) \<in> IEXT I (IS I rdfs_domain)\<rbrakk> \<Longrightarrow> p \<in> IP I"
  by (auto simp: owl_rl_interp_def c_dom_fwd_def)
lemma D_dom_IC: "\<lbrakk>owl_rl_interp I; (p,c) \<in> IEXT I (IS I rdfs_domain)\<rbrakk> \<Longrightarrow> c \<in> IC I"
  by (auto simp: owl_rl_interp_def c_dom_fwd_def)
lemma D_dom_bwd:
  "\<lbrakk>owl_rl_interp I; p \<in> IP I; c \<in> IC I;
    \<forall>x y. (x,y) \<in> IEXT I p \<longrightarrow> (x,c) \<in> IEXT I (IS I rdf_type)\<rbrakk>
     \<Longrightarrow> (p,c) \<in> IEXT I (IS I rdfs_domain)"
  by (auto simp: owl_rl_interp_def c_dom_bwd_def ICEXT_def)

lemma D_rng:
  "\<lbrakk>owl_rl_interp I; (p,c) \<in> IEXT I (IS I rdfs_range); (x,y) \<in> IEXT I p\<rbrakk>
     \<Longrightarrow> (y,c) \<in> IEXT I (IS I rdf_type)"
  by (auto simp: owl_rl_interp_def c_rng_fwd_def ICEXT_def)
lemma D_rng_IP: "\<lbrakk>owl_rl_interp I; (p,c) \<in> IEXT I (IS I rdfs_range)\<rbrakk> \<Longrightarrow> p \<in> IP I"
  by (auto simp: owl_rl_interp_def c_rng_fwd_def)
lemma D_rng_IC: "\<lbrakk>owl_rl_interp I; (p,c) \<in> IEXT I (IS I rdfs_range)\<rbrakk> \<Longrightarrow> c \<in> IC I"
  by (auto simp: owl_rl_interp_def c_rng_fwd_def)
lemma D_rng_bwd:
  "\<lbrakk>owl_rl_interp I; p \<in> IP I; c \<in> IC I;
    \<forall>x y. (x,y) \<in> IEXT I p \<longrightarrow> (y,c) \<in> IEXT I (IS I rdf_type)\<rbrakk>
     \<Longrightarrow> (p,c) \<in> IEXT I (IS I rdfs_range)"
  by (auto simp: owl_rl_interp_def c_rng_bwd_def ICEXT_def)

lemma D_sco:
  "\<lbrakk>owl_rl_interp I; (a,b) \<in> IEXT I (IS I rdfs_subClassOf); (x,a) \<in> IEXT I (IS I rdf_type)\<rbrakk>
     \<Longrightarrow> (x,b) \<in> IEXT I (IS I rdf_type)"
  by (auto simp: owl_rl_interp_def c_sco_fwd_def ICEXT_def)
lemma D_sco_IC1: "\<lbrakk>owl_rl_interp I; (a,b) \<in> IEXT I (IS I rdfs_subClassOf)\<rbrakk> \<Longrightarrow> a \<in> IC I"
  by (auto simp: owl_rl_interp_def c_sco_fwd_def)
lemma D_sco_IC2: "\<lbrakk>owl_rl_interp I; (a,b) \<in> IEXT I (IS I rdfs_subClassOf)\<rbrakk> \<Longrightarrow> b \<in> IC I"
  by (auto simp: owl_rl_interp_def c_sco_fwd_def)
lemma D_sco_bwd:
  "\<lbrakk>owl_rl_interp I; a \<in> IC I; b \<in> IC I;
    \<forall>x. (x,a) \<in> IEXT I (IS I rdf_type) \<longrightarrow> (x,b) \<in> IEXT I (IS I rdf_type)\<rbrakk>
     \<Longrightarrow> (a,b) \<in> IEXT I (IS I rdfs_subClassOf)"
  by (auto simp: owl_rl_interp_def c_sco_bwd_def ICEXT_def)
lemma D_sco_trans:
  "\<lbrakk>owl_rl_interp I; (a,b) \<in> IEXT I (IS I rdfs_subClassOf);
    (b,c) \<in> IEXT I (IS I rdfs_subClassOf)\<rbrakk> \<Longrightarrow> (a,c) \<in> IEXT I (IS I rdfs_subClassOf)"
  by (auto simp: owl_rl_interp_def c_sco_trans_def)

lemma D_spo:
  "\<lbrakk>owl_rl_interp I; (p,q) \<in> IEXT I (IS I rdfs_subPropertyOf); (x,y) \<in> IEXT I p\<rbrakk>
     \<Longrightarrow> (x,y) \<in> IEXT I q"
  by (auto simp: owl_rl_interp_def c_spo_fwd_def)
lemma D_spo_IP1: "\<lbrakk>owl_rl_interp I; (p,q) \<in> IEXT I (IS I rdfs_subPropertyOf)\<rbrakk> \<Longrightarrow> p \<in> IP I"
  by (auto simp: owl_rl_interp_def c_spo_fwd_def)
lemma D_spo_IP2: "\<lbrakk>owl_rl_interp I; (p,q) \<in> IEXT I (IS I rdfs_subPropertyOf)\<rbrakk> \<Longrightarrow> q \<in> IP I"
  by (auto simp: owl_rl_interp_def c_spo_fwd_def)
lemma D_spo_bwd:
  "\<lbrakk>owl_rl_interp I; p \<in> IP I; q \<in> IP I; IEXT I p \<subseteq> IEXT I q\<rbrakk>
     \<Longrightarrow> (p,q) \<in> IEXT I (IS I rdfs_subPropertyOf)"
  by (auto simp: owl_rl_interp_def c_spo_bwd_def)
lemma D_spo_trans:
  "\<lbrakk>owl_rl_interp I; (a,b) \<in> IEXT I (IS I rdfs_subPropertyOf);
    (b,c) \<in> IEXT I (IS I rdfs_subPropertyOf)\<rbrakk>
     \<Longrightarrow> (a,c) \<in> IEXT I (IS I rdfs_subPropertyOf)"
  by (auto simp: owl_rl_interp_def c_spo_trans_def)

lemma D_sameAs: "\<lbrakk>owl_rl_interp I; (a,b) \<in> IEXT I (IS I owl_sameAs)\<rbrakk> \<Longrightarrow> a = b"
  by (auto simp: owl_rl_interp_def c_sameAs_fwd_def)

lemma D_eqc_IC1: "\<lbrakk>owl_rl_interp I; (a,b) \<in> IEXT I (IS I owl_equivalentClass)\<rbrakk> \<Longrightarrow> a \<in> IC I"
  by (auto simp: owl_rl_interp_def c_eqc_fwd_def)
lemma D_eqc_IC2: "\<lbrakk>owl_rl_interp I; (a,b) \<in> IEXT I (IS I owl_equivalentClass)\<rbrakk> \<Longrightarrow> b \<in> IC I"
  by (auto simp: owl_rl_interp_def c_eqc_fwd_def)
lemma D_eqc_ext:
  "\<lbrakk>owl_rl_interp I; (a,b) \<in> IEXT I (IS I owl_equivalentClass)\<rbrakk>
     \<Longrightarrow> ICEXT I a = ICEXT I b"
  by (auto simp: owl_rl_interp_def c_eqc_fwd_def)

lemma D_eqp_IP1: "\<lbrakk>owl_rl_interp I; (a,b) \<in> IEXT I (IS I owl_equivalentProperty)\<rbrakk> \<Longrightarrow> a \<in> IP I"
  by (auto simp: owl_rl_interp_def c_eqp_fwd_def)
lemma D_eqp_IP2: "\<lbrakk>owl_rl_interp I; (a,b) \<in> IEXT I (IS I owl_equivalentProperty)\<rbrakk> \<Longrightarrow> b \<in> IP I"
  by (auto simp: owl_rl_interp_def c_eqp_fwd_def)
lemma D_eqp_ext:
  "\<lbrakk>owl_rl_interp I; (a,b) \<in> IEXT I (IS I owl_equivalentProperty)\<rbrakk> \<Longrightarrow> IEXT I a = IEXT I b"
  by (auto simp: owl_rl_interp_def c_eqp_fwd_def)

lemma D_inv_IP1: "\<lbrakk>owl_rl_interp I; (p,q) \<in> IEXT I (IS I owl_inverseOf)\<rbrakk> \<Longrightarrow> p \<in> IP I"
  by (auto simp: owl_rl_interp_def c_inv_fwd_def)
lemma D_inv_IP2: "\<lbrakk>owl_rl_interp I; (p,q) \<in> IEXT I (IS I owl_inverseOf)\<rbrakk> \<Longrightarrow> q \<in> IP I"
  by (auto simp: owl_rl_interp_def c_inv_fwd_def)
lemma D_inv1:
  "\<lbrakk>owl_rl_interp I; (p,q) \<in> IEXT I (IS I owl_inverseOf); (x,y) \<in> IEXT I p\<rbrakk>
     \<Longrightarrow> (y,x) \<in> IEXT I q"
  by (auto simp: owl_rl_interp_def c_inv_fwd_def)
lemma D_inv2:
  "\<lbrakk>owl_rl_interp I; (p,q) \<in> IEXT I (IS I owl_inverseOf); (x,y) \<in> IEXT I q\<rbrakk>
     \<Longrightarrow> (y,x) \<in> IEXT I p"
  by (auto simp: owl_rl_interp_def c_inv_fwd_def)

lemma D_sym:
  "\<lbrakk>owl_rl_interp I; (p, IS I owl_SymmetricProperty) \<in> IEXT I (IS I rdf_type);
    (x,y) \<in> IEXT I p\<rbrakk> \<Longrightarrow> (y,x) \<in> IEXT I p"
  by (auto simp: owl_rl_interp_def c_sym_fwd_def ICEXT_def)
lemma D_trp:
  "\<lbrakk>owl_rl_interp I; (p, IS I owl_TransitiveProperty) \<in> IEXT I (IS I rdf_type);
    (x,y) \<in> IEXT I p; (y,z) \<in> IEXT I p\<rbrakk> \<Longrightarrow> (x,z) \<in> IEXT I p"
  by (auto simp: owl_rl_interp_def c_trp_fwd_def ICEXT_def)

lemma D_onP_IP: "\<lbrakk>owl_rl_interp I; (z,p) \<in> IEXT I (IS I owl_onProperty)\<rbrakk> \<Longrightarrow> p \<in> IP I"
  by (auto simp: owl_rl_interp_def c_onp_typ_def)
lemma D_svf_IC: "\<lbrakk>owl_rl_interp I; (z,c) \<in> IEXT I (IS I owl_someValuesFrom)\<rbrakk> \<Longrightarrow> z \<in> IC I"
  by (auto simp: owl_rl_interp_def c_svf_typ_def c_restr_IC_def)
lemma D_avf_IC: "\<lbrakk>owl_rl_interp I; (z,c) \<in> IEXT I (IS I owl_allValuesFrom)\<rbrakk> \<Longrightarrow> z \<in> IC I"
  by (auto simp: owl_rl_interp_def c_avf_typ_def c_restr_IC_def)

lemma D_svf_in:
  "\<lbrakk>owl_rl_interp I; (z,c) \<in> IEXT I (IS I owl_someValuesFrom);
    (z,p) \<in> IEXT I (IS I owl_onProperty);
    (x,y) \<in> IEXT I p; (y,c) \<in> IEXT I (IS I rdf_type)\<rbrakk>
     \<Longrightarrow> (x,z) \<in> IEXT I (IS I rdf_type)"
  by (auto simp: owl_rl_interp_def c_svf_def ICEXT_def set_eq_iff)
lemma D_svf_out:
  "\<lbrakk>owl_rl_interp I; (z,c) \<in> IEXT I (IS I owl_someValuesFrom);
    (z,p) \<in> IEXT I (IS I owl_onProperty); (x,z) \<in> IEXT I (IS I rdf_type)\<rbrakk>
     \<Longrightarrow> \<exists>y. (x,y) \<in> IEXT I p \<and> (y,c) \<in> IEXT I (IS I rdf_type)"
  by (auto simp: owl_rl_interp_def c_svf_def ICEXT_def set_eq_iff)

lemma D_avf_in:
  "\<lbrakk>owl_rl_interp I; (z,c) \<in> IEXT I (IS I owl_allValuesFrom);
    (z,p) \<in> IEXT I (IS I owl_onProperty);
    \<forall>y. (x,y) \<in> IEXT I p \<longrightarrow> (y,c) \<in> IEXT I (IS I rdf_type)\<rbrakk>
     \<Longrightarrow> (x,z) \<in> IEXT I (IS I rdf_type)"
  by (auto simp: owl_rl_interp_def c_avf_def ICEXT_def set_eq_iff)
lemma D_avf_out:
  "\<lbrakk>owl_rl_interp I; (z,c) \<in> IEXT I (IS I owl_allValuesFrom);
    (z,p) \<in> IEXT I (IS I owl_onProperty); (x,z) \<in> IEXT I (IS I rdf_type);
    (x,y) \<in> IEXT I p\<rbrakk> \<Longrightarrow> (y,c) \<in> IEXT I (IS I rdf_type)"
  by (auto simp: owl_rl_interp_def c_avf_def ICEXT_def set_eq_iff)

lemma D_hv_out:
  "\<lbrakk>owl_rl_interp I; (z,a) \<in> IEXT I (IS I owl_hasValue);
    (z,p) \<in> IEXT I (IS I owl_onProperty); (x,z) \<in> IEXT I (IS I rdf_type)\<rbrakk>
     \<Longrightarrow> (x,a) \<in> IEXT I p"
  by (auto simp: owl_rl_interp_def c_hv_def ICEXT_def set_eq_iff)
lemma D_hv_in:
  "\<lbrakk>owl_rl_interp I; (z,a) \<in> IEXT I (IS I owl_hasValue);
    (z,p) \<in> IEXT I (IS I owl_onProperty); (x,a) \<in> IEXT I p\<rbrakk>
     \<Longrightarrow> (x,z) \<in> IEXT I (IS I rdf_type)"
  by (auto simp: owl_rl_interp_def c_hv_def ICEXT_def set_eq_iff)


section \<open>Derived subsumption lemmas\<close>

lemma D_eqc_sub1:
  assumes I: "owl_rl_interp I" and e: "(a,b) \<in> IEXT I (IS I owl_equivalentClass)"
  shows "(a,b) \<in> IEXT I (IS I rdfs_subClassOf)"
proof (rule D_sco_bwd[OF I])
  show "a \<in> IC I" using I e by (rule D_eqc_IC1)
  show "b \<in> IC I" using I e by (rule D_eqc_IC2)
  show "\<forall>x. (x,a) \<in> IEXT I (IS I rdf_type) \<longrightarrow> (x,b) \<in> IEXT I (IS I rdf_type)"
    using D_eqc_ext[OF I e] by (auto simp: ICEXT_def set_eq_iff)
qed

lemma D_eqc_sub2:
  assumes I: "owl_rl_interp I" and e: "(a,b) \<in> IEXT I (IS I owl_equivalentClass)"
  shows "(b,a) \<in> IEXT I (IS I rdfs_subClassOf)"
proof (rule D_sco_bwd[OF I])
  show "b \<in> IC I" using I e by (rule D_eqc_IC2)
  show "a \<in> IC I" using I e by (rule D_eqc_IC1)
  show "\<forall>x. (x,b) \<in> IEXT I (IS I rdf_type) \<longrightarrow> (x,a) \<in> IEXT I (IS I rdf_type)"
    using D_eqc_ext[OF I e] by (auto simp: ICEXT_def set_eq_iff)
qed

lemma D_eqp_sub1:
  assumes I: "owl_rl_interp I" and e: "(a,b) \<in> IEXT I (IS I owl_equivalentProperty)"
  shows "(a,b) \<in> IEXT I (IS I rdfs_subPropertyOf)"
  by (rule D_spo_bwd[OF I D_eqp_IP1[OF I e] D_eqp_IP2[OF I e]])
     (simp add: D_eqp_ext[OF I e])

lemma D_eqp_sub2:
  assumes I: "owl_rl_interp I" and e: "(a,b) \<in> IEXT I (IS I owl_equivalentProperty)"
  shows "(b,a) \<in> IEXT I (IS I rdfs_subPropertyOf)"
  by (rule D_spo_bwd[OF I D_eqp_IP2[OF I e] D_eqp_IP1[OF I e]])
     (simp add: D_eqp_ext[OF I e])

lemma D_svf_mono1:
  assumes I: "owl_rl_interp I"
    and a1: "(c1,y1) \<in> IEXT I (IS I owl_someValuesFrom)"
    and a2: "(c1,p) \<in> IEXT I (IS I owl_onProperty)"
    and a3: "(c2,y2) \<in> IEXT I (IS I owl_someValuesFrom)"
    and a4: "(c2,p) \<in> IEXT I (IS I owl_onProperty)"
    and a5: "(y1,y2) \<in> IEXT I (IS I rdfs_subClassOf)"
  shows "(c1,c2) \<in> IEXT I (IS I rdfs_subClassOf)"
proof (rule D_sco_bwd[OF I D_svf_IC[OF I a1] D_svf_IC[OF I a3]], intro allI impI)
  fix x assume "(x,c1) \<in> IEXT I (IS I rdf_type)"
  then obtain y where "(x,y) \<in> IEXT I p" and "(y,y1) \<in> IEXT I (IS I rdf_type)"
    using D_svf_out[OF I a1 a2] by blast
  then have "(y,y2) \<in> IEXT I (IS I rdf_type)" using D_sco[OF I a5] by blast
  thus "(x,c2) \<in> IEXT I (IS I rdf_type)"
    using D_svf_in[OF I a3 a4 \<open>(x,y) \<in> IEXT I p\<close>] by blast
qed

lemma D_svf_mono2:
  assumes I: "owl_rl_interp I"
    and a1: "(c1,y) \<in> IEXT I (IS I owl_someValuesFrom)"
    and a2: "(c1,p1) \<in> IEXT I (IS I owl_onProperty)"
    and a3: "(c2,y) \<in> IEXT I (IS I owl_someValuesFrom)"
    and a4: "(c2,p2) \<in> IEXT I (IS I owl_onProperty)"
    and a5: "(p1,p2) \<in> IEXT I (IS I rdfs_subPropertyOf)"
  shows "(c1,c2) \<in> IEXT I (IS I rdfs_subClassOf)"
proof (rule D_sco_bwd[OF I D_svf_IC[OF I a1] D_svf_IC[OF I a3]], intro allI impI)
  fix x assume "(x,c1) \<in> IEXT I (IS I rdf_type)"
  then obtain v where v1: "(x,v) \<in> IEXT I p1" and v2: "(v,y) \<in> IEXT I (IS I rdf_type)"
    using D_svf_out[OF I a1 a2] by blast
  have "(x,v) \<in> IEXT I p2" using D_spo[OF I a5 v1] .
  thus "(x,c2) \<in> IEXT I (IS I rdf_type)" using D_svf_in[OF I a3 a4 _ v2] by blast
qed

lemma D_avf_mono1:
  assumes I: "owl_rl_interp I"
    and a1: "(c1,y1) \<in> IEXT I (IS I owl_allValuesFrom)"
    and a2: "(c1,p) \<in> IEXT I (IS I owl_onProperty)"
    and a3: "(c2,y2) \<in> IEXT I (IS I owl_allValuesFrom)"
    and a4: "(c2,p) \<in> IEXT I (IS I owl_onProperty)"
    and a5: "(y1,y2) \<in> IEXT I (IS I rdfs_subClassOf)"
  shows "(c1,c2) \<in> IEXT I (IS I rdfs_subClassOf)"
proof (rule D_sco_bwd[OF I D_avf_IC[OF I a1] D_avf_IC[OF I a3]], intro allI impI)
  fix x assume h: "(x,c1) \<in> IEXT I (IS I rdf_type)"
  have "\<forall>v. (x,v) \<in> IEXT I p \<longrightarrow> (v,y2) \<in> IEXT I (IS I rdf_type)"
  proof (intro allI impI)
    fix v assume "(x,v) \<in> IEXT I p"
    hence "(v,y1) \<in> IEXT I (IS I rdf_type)" using D_avf_out[OF I a1 a2 h] by blast
    thus "(v,y2) \<in> IEXT I (IS I rdf_type)" using D_sco[OF I a5] by blast
  qed
  thus "(x,c2) \<in> IEXT I (IS I rdf_type)" using D_avf_in[OF I a3 a4] by blast
qed

lemma D_avf_mono2:
  assumes I: "owl_rl_interp I"
    and a1: "(c1,y) \<in> IEXT I (IS I owl_allValuesFrom)"
    and a2: "(c1,p1) \<in> IEXT I (IS I owl_onProperty)"
    and a3: "(c2,y) \<in> IEXT I (IS I owl_allValuesFrom)"
    and a4: "(c2,p2) \<in> IEXT I (IS I owl_onProperty)"
    and a5: "(p1,p2) \<in> IEXT I (IS I rdfs_subPropertyOf)"
  shows "(c2,c1) \<in> IEXT I (IS I rdfs_subClassOf)"
proof (rule D_sco_bwd[OF I D_avf_IC[OF I a3] D_avf_IC[OF I a1]], intro allI impI)
  fix x assume h: "(x,c2) \<in> IEXT I (IS I rdf_type)"
  have "\<forall>v. (x,v) \<in> IEXT I p1 \<longrightarrow> (v,y) \<in> IEXT I (IS I rdf_type)"
  proof (intro allI impI)
    fix v assume "(x,v) \<in> IEXT I p1"
    hence "(x,v) \<in> IEXT I p2" using D_spo[OF I a5] by blast
    thus "(v,y) \<in> IEXT I (IS I rdf_type)" using D_avf_out[OF I a3 a4 h] by blast
  qed
  thus "(x,c1) \<in> IEXT I (IS I rdf_type)" using D_avf_in[OF I a1 a2] by blast
qed

lemma D_dom_mono1:
  assumes I: "owl_rl_interp I"
    and a1: "(p,c1) \<in> IEXT I (IS I rdfs_domain)"
    and a2: "(c1,c2) \<in> IEXT I (IS I rdfs_subClassOf)"
  shows "(p,c2) \<in> IEXT I (IS I rdfs_domain)"
  by (rule D_dom_bwd[OF I D_dom_IP[OF I a1] D_sco_IC2[OF I a2]])
     (auto dest: D_dom[OF I a1] D_sco[OF I a2])

lemma D_dom_mono2:
  assumes I: "owl_rl_interp I"
    and a1: "(p2,c) \<in> IEXT I (IS I rdfs_domain)"
    and a2: "(p1,p2) \<in> IEXT I (IS I rdfs_subPropertyOf)"
  shows "(p1,c) \<in> IEXT I (IS I rdfs_domain)"
  by (rule D_dom_bwd[OF I D_spo_IP1[OF I a2] D_dom_IC[OF I a1]])
     (auto dest: D_spo[OF I a2] D_dom[OF I a1])

lemma D_rng_mono1:
  assumes I: "owl_rl_interp I"
    and a1: "(p,c1) \<in> IEXT I (IS I rdfs_range)"
    and a2: "(c1,c2) \<in> IEXT I (IS I rdfs_subClassOf)"
  shows "(p,c2) \<in> IEXT I (IS I rdfs_range)"
  by (rule D_rng_bwd[OF I D_rng_IP[OF I a1] D_sco_IC2[OF I a2]])
     (auto dest: D_rng[OF I a1] D_sco[OF I a2])

lemma D_rng_mono2:
  assumes I: "owl_rl_interp I"
    and a1: "(p2,c) \<in> IEXT I (IS I rdfs_range)"
    and a2: "(p1,p2) \<in> IEXT I (IS I rdfs_subPropertyOf)"
  shows "(p1,c) \<in> IEXT I (IS I rdfs_range)"
  by (rule D_rng_bwd[OF I D_spo_IP1[OF I a2] D_rng_IC[OF I a1]])
     (auto dest: D_spo[OF I a2] D_rng[OF I a1])

section \<open>Soundness of the built-in rules\<close>

lemma s_rdfs2: "owl_rl_interp I \<Longrightarrow> sat_rule I r_rdfs2"
  by (auto simp: sat_rule_def r_rdfs2_def PI_def D_type_IP dest: D_dom)
lemma s_rdfs3: "owl_rl_interp I \<Longrightarrow> sat_rule I r_rdfs3"
  by (auto simp: sat_rule_def r_rdfs3_def PI_def D_type_IP dest: D_rng)
lemma s_rdfs5: "owl_rl_interp I \<Longrightarrow> sat_rule I r_rdfs5"
  by (auto simp: sat_rule_def r_rdfs5_def PI_def D_spo_IP dest: D_spo_trans)
lemma s_rdfs7: "owl_rl_interp I \<Longrightarrow> sat_rule I r_rdfs7"
  by (auto simp: sat_rule_def r_rdfs7_def PI_def dest: D_spo D_spo_IP2)
lemma s_rdfs9: "owl_rl_interp I \<Longrightarrow> sat_rule I r_rdfs9"
  by (auto simp: sat_rule_def r_rdfs9_def PI_def D_type_IP dest: D_sco)
lemma s_rdfs11: "owl_rl_interp I \<Longrightarrow> sat_rule I r_rdfs11"
  by (auto simp: sat_rule_def r_rdfs11_def PI_def D_sco_IP dest: D_sco_trans)
lemma s_prp_trp: "owl_rl_interp I \<Longrightarrow> sat_rule I r_prp_trp"
  by (auto simp: sat_rule_def r_prp_trp_def PI_def dest: D_trp)
lemma s_prp_symp: "owl_rl_interp I \<Longrightarrow> sat_rule I r_prp_symp"
  by (auto simp: sat_rule_def r_prp_symp_def PI_def dest: D_sym)
lemma s_prp_inv1: "owl_rl_interp I \<Longrightarrow> sat_rule I r_prp_inv1"
  by (auto simp: sat_rule_def r_prp_inv1_def PI_def dest: D_inv1 D_inv_IP2)
lemma s_prp_inv2: "owl_rl_interp I \<Longrightarrow> sat_rule I r_prp_inv2"
  by (auto simp: sat_rule_def r_prp_inv2_def PI_def dest: D_inv2 D_inv_IP1)
lemma s_eq_sym: "owl_rl_interp I \<Longrightarrow> sat_rule I r_eq_sym"
  by (auto simp: sat_rule_def r_eq_sym_def PI_def dest: D_sameAs)
lemma s_scm_eqc1a: "owl_rl_interp I \<Longrightarrow> sat_rule I r_scm_eqc1a"
  by (auto simp: sat_rule_def r_scm_eqc1a_def PI_def D_sco_IP dest: D_eqc_sub1)
lemma s_scm_eqc1b: "owl_rl_interp I \<Longrightarrow> sat_rule I r_scm_eqc1b"
  by (auto simp: sat_rule_def r_scm_eqc1b_def PI_def D_sco_IP dest: D_eqc_sub2)
lemma s_scm_eqp1a: "owl_rl_interp I \<Longrightarrow> sat_rule I r_scm_eqp1a"
  by (auto simp: sat_rule_def r_scm_eqp1a_def PI_def D_spo_IP dest: D_eqp_sub1)
lemma s_scm_eqp1b: "owl_rl_interp I \<Longrightarrow> sat_rule I r_scm_eqp1b"
  by (auto simp: sat_rule_def r_scm_eqp1b_def PI_def D_spo_IP dest: D_eqp_sub2)
lemma s_cls_svf1: "owl_rl_interp I \<Longrightarrow> sat_rule I r_cls_svf1"
  by (auto simp: sat_rule_def r_cls_svf1_def PI_def D_type_IP dest: D_svf_in)
lemma s_cls_avf: "owl_rl_interp I \<Longrightarrow> sat_rule I r_cls_avf"
  by (auto simp: sat_rule_def r_cls_avf_def PI_def D_type_IP dest: D_avf_out)
lemma s_cls_hv1: "owl_rl_interp I \<Longrightarrow> sat_rule I r_cls_hv1"
  by (auto simp: sat_rule_def r_cls_hv1_def PI_def dest: D_hv_out D_onP_IP)
lemma s_cls_hv2: "owl_rl_interp I \<Longrightarrow> sat_rule I r_cls_hv2"
  by (auto simp: sat_rule_def r_cls_hv2_def PI_def D_type_IP dest: D_hv_in)
lemma s_scm_svf1: "owl_rl_interp I \<Longrightarrow> sat_rule I r_scm_svf1"
  by (auto simp: sat_rule_def r_scm_svf1_def PI_def D_sco_IP dest: D_svf_mono1)
lemma s_scm_svf2: "owl_rl_interp I \<Longrightarrow> sat_rule I r_scm_svf2"
  by (auto simp: sat_rule_def r_scm_svf2_def PI_def D_sco_IP dest: D_svf_mono2)
lemma s_scm_avf1: "owl_rl_interp I \<Longrightarrow> sat_rule I r_scm_avf1"
  by (auto simp: sat_rule_def r_scm_avf1_def PI_def D_sco_IP dest: D_avf_mono1)
lemma s_scm_avf2: "owl_rl_interp I \<Longrightarrow> sat_rule I r_scm_avf2"
  by (auto simp: sat_rule_def r_scm_avf2_def PI_def D_sco_IP dest: D_avf_mono2)
lemma s_scm_dom1: "owl_rl_interp I \<Longrightarrow> sat_rule I r_scm_dom1"
  by (auto simp: sat_rule_def r_scm_dom1_def PI_def dest: D_dom_mono1)
lemma s_scm_dom2: "owl_rl_interp I \<Longrightarrow> sat_rule I r_scm_dom2"
  by (auto simp: sat_rule_def r_scm_dom2_def PI_def dest: D_dom_mono2)
lemma s_scm_rng1: "owl_rl_interp I \<Longrightarrow> sat_rule I r_scm_rng1"
  by (auto simp: sat_rule_def r_scm_rng1_def PI_def dest: D_rng_mono1)
lemma s_scm_rng2: "owl_rl_interp I \<Longrightarrow> sat_rule I r_scm_rng2"
  by (auto simp: sat_rule_def r_scm_rng2_def PI_def dest: D_rng_mono2)
section \<open>T2: every arm of the shipped table is sound\<close>

theorem builtin_table_sound:
  "owl_rl_interp I \<Longrightarrow> \<forall>R \<in> set builtin_table. sat_rule I R"
  unfolding builtin_table_def
  by (simp add: s_rdfs2 s_rdfs3 s_rdfs5 s_rdfs7 s_rdfs9 s_rdfs11
      s_prp_trp s_prp_symp s_prp_inv1 s_prp_inv2 s_eq_sym
      s_scm_eqc1a s_scm_eqc1b s_scm_eqp1a s_scm_eqp1b
      s_cls_svf1 s_cls_avf s_cls_hv1 s_cls_hv2
      s_scm_svf1 s_scm_svf2 s_scm_avf1 s_scm_avf2
      s_scm_dom1 s_scm_dom2 s_scm_rng1 s_scm_rng2)

section \<open>T3: the absolute verdict\<close>

(* The ONLY place in the development where the semantics of the vocabulary is consumed.
   Read the difference from T1 carefully: T1 concludes entails_under, which quantifies
   over interpretations satisfying the USER's rules and nothing else; T3 concludes
   entails, which quantifies over interpretations satisfying the 26 conditions of
   owl_rl_interp.  T3 is available only because builtin_table_sound discharges every arm
   of THIS table against THOSE conditions. *)

theorem entails_of_builtin:
  fixes G :: "triple list" and C :: "hstep list"
  assumes ok: "check_cert builtin_table G C = None"
      and mem: "s \<in> set C"
  shows "entails TYPE('d) (set G) (sconcl s)"
proof (rule entails_of_entails_under)
  show "\<And>I :: 'd interp. owl_rl_interp I \<Longrightarrow> \<forall>R \<in> set builtin_table. sat_rule I R"
    by (rule builtin_table_sound)
  show "entails_under TYPE('d) builtin_table (set G) (sconcl s)"
    by (rule horn_certificate_sound[OF ok mem])
qed

theorem entails_of_builtin_lenient:
  fixes G :: "triple list" and C :: "hstep list"
  assumes ok: "check_cert_lenient builtin_table G C = None"
      and mem: "s \<in> set C"
  shows "entails TYPE('d) (set G) (sconcl s)"
proof (rule entails_of_entails_under)
  show "\<And>I :: 'd interp. owl_rl_interp I \<Longrightarrow> \<forall>R \<in> set builtin_table. sat_rule I R"
    by (rule builtin_table_sound)
  show "entails_under TYPE('d) builtin_table (set G) (sconcl s)"
    by (rule horn_certificate_sound_lenient[OF ok mem])
qed

section \<open>T4: the bridge to genuine simple interpretations (M22, conflict C6)\<close>

(* owl_rl_interp deliberately omits the domain conditions of RBS Table 5.1, because no
   arm consumes them and omitting them enlarges the model class.  This theorem records
   that the result nevertheless applies to an interpretation that DOES satisfy them, so
   nothing was lost by the omission. *)

theorem entails_simple:
  fixes I :: "'d interp"
  assumes wf: "wf_interp I"
      and cond: "owl_rl_interp I"
      and mod: "models I (set G)"
      and ok: "check_cert builtin_table G C = None"
      and mem: "s \<in> set C"
  shows "sat I (sconcl s)"
  using entails_of_builtin[OF ok mem, where 'd = 'd] cond mod
  by (simp add: entails_def)

section \<open>T5: the verdict is never over-claimed\<close>

theorem verdict_honest: "verdict_of R = Entailed \<Longrightarrow> R = builtin_table"
  by (simp add: verdict_of_def split: if_splits)

theorem a_user_rule_never_earns_the_absolute_verdict:
  "R \<noteq> builtin_table \<Longrightarrow> verdict_of R = EntailedUnderSuppliedRules"
  by (simp add: verdict_of_def)

end
