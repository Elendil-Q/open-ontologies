(* OO_Check.thy -- the certificate checker, and the built-in rule table.

   EXECUTABLE.  Nothing here mentions an interpretation, a domain, or truth.  Checking a
   Horn certificate is PURELY SYNTACTIC: not one line of the semantics is consulted.
   That is worth stating loudly, because it has a consequence for any differential test
   against another implementation -- two checkers built on wildly different and even
   mutually contradictory semantics will agree on every certificate and on every forgery.
   AGREEMENT ON ACCEPT/REJECT IS NOT EVIDENCE THAT TWO FORMALISATIONS' DEFINITIONS AGREE.
   The evidence lives in OO_Builtin_Sound: which arms each side can discharge, and from
   which conditions. *)

theory OO_Check
  imports OO_Format
begin

section \<open>Rejection reasons\<close>

datatype reason =
    R_index_out_of_range
  | R_arity_mismatch
  | R_binding_incomplete
  | R_binding_dup_key
  | R_body_mismatch nat
  | R_premise_unknown nat
  | R_head_mismatch

section \<open>The checker\<close>

(* DECISION M25, and UNCERTAINTY U10 which is a genuine coin-flip between two honest
   authors.  A duplicate key in the binding is MALFORMED and rejected.
   The reason it is a coin-flip: map_of is silently first-wins in Isabelle, so a
   duplicate key would otherwise be accepted with one of the two values chosen by an
   implementation detail of the lookup function.  Rejecting is the conservative reading.
   It is nevertheless a STRICTNESS with no soundness content -- see
   check_step_dup_key_not_needed in OO_Sound, which proves that removing this check
   preserves soundness -- so a differential disagreement here is a disagreement about
   taste, not about truth. *)

definition binding_covers :: "(string \<times> rdf_term) list \<Rightarrow> hrule \<Rightarrow> bool" where
  "binding_covers \<beta> r = list_all (\<lambda>v. map_of \<beta> v \<noteq> None) (rule_var_list r)"

(* DECISION M26 (conflict C11, uncertainty U12).  Premises are checked STRICTLY:
   positionally equal to the instantiated body AND present in the known set.
   Both strict and lenient are sound.  They differ on exactly one class of input:
   premises listed out of order but all asserted.  This is the single most likely place
   for a first differential disagreement with another implementation, and it is
   HARMLESS -- the stricter checker is the better-behaved one.  Do not "fix" it.
   The lenient judgement is defined below as well, and proved sound, so a report can
   carry both bits and a disagreement can be localised by a theorem instead of a guess. *)

fun body_strict ::
  "(string \<times> rdf_term) list \<Rightarrow> nat \<Rightarrow> pat_triple list \<Rightarrow> triple list \<Rightarrow> reason option" where
  "body_strict \<beta> j [] []             = None"
| "body_strict \<beta> j [] (p # ps)       = Some R_arity_mismatch"
| "body_strict \<beta> j (b # bs) []       = Some R_arity_mismatch"
| "body_strict \<beta> j (b # bs) (p # ps) =
     (if iptriple \<beta> b = Some p then body_strict \<beta> (Suc j) bs ps
      else Some (R_body_mismatch j))"

(* TRAP T9, guarded: this is POSITIONAL equality, not set equality.  With set equality
   and a rule whose body has two identical patterns, one known triple would discharge
   two body atoms. *)

fun premises_known :: "graph \<Rightarrow> nat \<Rightarrow> triple list \<Rightarrow> reason option" where
  "premises_known K j []       = None"
| "premises_known K j (p # ps) =
     (if p \<in> K then premises_known K (Suc j) ps else Some (R_premise_unknown j))"

(* DECISION M-IDX / C12 / U11.  An out-of-range rule index is a REJECTION (exit 1), not
   a parse error (exit 2).  It is detected here, by the checker, because the certificate
   line parses without consulting the table at all -- see DECISION D-PARSE-3 in
   OO_Parse, which differs from the brief's expectation and is an independent finding. *)

definition check_step :: "rtable \<Rightarrow> graph \<Rightarrow> hstep \<Rightarrow> reason option" where
  "check_step R K s =
     (if length R \<le> sidx s then Some R_index_out_of_range
      else
        (let r = R ! sidx s; b = sbind s in
          if \<not> distinct (map fst b) then Some R_binding_dup_key
          else if \<not> binding_covers b r then Some R_binding_incomplete
          else (case body_strict b 0 (rbody r) (sprem s) of Some e \<Rightarrow> Some e | None \<Rightarrow>
                (case premises_known K 0 (sprem s) of Some e \<Rightarrow> Some e | None \<Rightarrow>
                 if iptriple b (rhead r) = Some (sconcl s) then None
                 else Some R_head_mismatch))))"

(* DECISION M27, AND THE ONE PROPERTY NO SHIPPED FIXTURE CAN TEST (uncertainty U16,
   trap T8).  Steps accumulate with STRICT PREFIX visibility: the known set for step j is
   the asserted graph together with the conclusions of steps STRICTLY BEFORE j.  The
   conclusion is inserted only AFTER the step has been checked.

   This recursion IS the no-self-support property.  There is no separate test for it, and
   there cannot usefully be one: the induction in check_from_sound (OO_Sound) is FALSE if
   the conclusion is inserted before the step is checked.  Building the union of the
   graph and all conclusions once and checking every step against it is faster, simpler,
   and lets a two-step cycle certify itself.  DO NOT "optimise" this into a closure pass.
   Verified against the fixtures: every certificate fixture is a single line, and
   bad_self.tsv aims at this property and misses -- its edit also breaks body
   instantiation, so it is rejected for an unrelated reason.  Answer this by reading the
   loop, not by running a test. *)

fun check_from :: "rtable \<Rightarrow> graph \<Rightarrow> nat \<Rightarrow> hstep list \<Rightarrow> (nat \<times> reason) option" where
  "check_from R K j []       = None"
| "check_from R K j (s # ss) =
     (case check_step R K s of Some e \<Rightarrow> Some (j, e)
      | None \<Rightarrow> check_from R (insert (sconcl s) K) (Suc j) ss)"

(* DECISION M37.  Fail fast on the first failing step and report its index. *)

definition check_cert :: "rtable \<Rightarrow> triple list \<Rightarrow> hstep list \<Rightarrow> (nat \<times> reason) option" where
  "check_cert R G ss = check_from R (set G) 0 ss"

definition accepts :: "rtable \<Rightarrow> triple list \<Rightarrow> hstep list \<Rightarrow> bool" where
  "accepts R G ss = (check_cert R G ss = None)"

section \<open>The lenient judgement (conflict C11), defined so the boundary can be probed\<close>

(* Ignores the cited premise list entirely and asks only that the instantiated body lie
   in the known set.  Sound as well (check_cert_lenient_sound in OO_Sound), and strictly
   more permissive (strict_implies_lenient). *)

fun body_lenient ::
  "(string \<times> rdf_term) list \<Rightarrow> graph \<Rightarrow> nat \<Rightarrow> pat_triple list \<Rightarrow> reason option" where
  "body_lenient \<beta> K j []       = None"
| "body_lenient \<beta> K j (b # bs) =
     (case iptriple \<beta> b of None \<Rightarrow> Some R_binding_incomplete
      | Some t \<Rightarrow> if t \<in> K then body_lenient \<beta> K (Suc j) bs
                  else Some (R_premise_unknown j))"

definition check_step_lenient :: "rtable \<Rightarrow> graph \<Rightarrow> hstep \<Rightarrow> reason option" where
  "check_step_lenient R K s =
     (if length R \<le> sidx s then Some R_index_out_of_range
      else
        (let r = R ! sidx s; b = sbind s in
          (case body_lenient b K 0 (rbody r) of Some e \<Rightarrow> Some e | None \<Rightarrow>
           if iptriple b (rhead r) = Some (sconcl s) then None else Some R_head_mismatch)))"

fun check_from_lenient ::
  "rtable \<Rightarrow> graph \<Rightarrow> nat \<Rightarrow> hstep list \<Rightarrow> (nat \<times> reason) option" where
  "check_from_lenient R K j []       = None"
| "check_from_lenient R K j (s # ss) =
     (case check_step_lenient R K s of Some e \<Rightarrow> Some (j, e)
      | None \<Rightarrow> check_from_lenient R (insert (sconcl s) K) (Suc j) ss)"

definition check_cert_lenient ::
  "rtable \<Rightarrow> triple list \<Rightarrow> hstep list \<Rightarrow> (nat \<times> reason) option" where
  "check_cert_lenient R G ss = check_from_lenient R (set G) 0 ss"

section \<open>The built-in rule table\<close>

(* DECISION M40, AND A STATED LIMIT ON INDEPENDENCE.  The built-in table is TRANSCRIBED
   FROM THE FIXTURE tests/fixtures/horn/builtin_rules.tsv.  It is therefore SHARED INPUT
   between this formalisation and any other, and the rows themselves are not independent
   evidence.  What IS independent is which rows each side can JUSTIFY from the
   specification, and from which conditions -- that is OO_Builtin_Sound.
   Re-dumped field by field before transcription: 27 rows, NF = 5 + 3n holds for all 27,
   and the row order is load-bearing because good.tsv cites index 4.

   DECISION M33 and C7, A FINDING RECORDED AND DELIBERATELY NOT ACTED ON.  The first six
   rows are named rdfs2, rdfs3, rdfs5, rdfs7, rdfs9, rdfs11 in the fixture.  Those names
   come from the NON-NORMATIVE table in RDF 1.1 Semantics section 9.2.1.  Their true
   OWL 2 Profiles names are prp-dom, prp-rng, scm-spo, prp-spo1, cax-sco and scm-sco, and
   the rdfs* naming is additionally misleading about the model class, since these rows are
   discharged here against OWL 2 RDF-Based conditions and not RDFS ones.  The finding is
   recorded in the comment on each row.  It is NOT acted on in the data, because
   verdict_of decides the absolute verdict by equality against this table, so renaming a
   row here would downgrade EVERY certificate to entailed_under_supplied_rules.
   Correct as a finding, fatal as an edit. *)

definition PI :: "string \<Rightarrow> pat" where "PI u = Tm (Iri u)"

definition r_rdfs2 :: hrule where          (* true W3C name: prp-dom *)
  "r_rdfs2 = \<lparr> rname = ''rdfs2'',
               rbody = [(V ''s'', V ''p'', V ''o''), (V ''p'', PI rdfs_domain, V ''c'')],
               rhead = (V ''s'', PI rdf_type, V ''c'') \<rparr>"
definition r_rdfs3 :: hrule where          (* true W3C name: prp-rng *)
  "r_rdfs3 = \<lparr> rname = ''rdfs3'',
               rbody = [(V ''s'', V ''p'', V ''o''), (V ''p'', PI rdfs_range, V ''c'')],
               rhead = (V ''o'', PI rdf_type, V ''c'') \<rparr>"
definition r_rdfs5 :: hrule where          (* true W3C name: scm-spo *)
  "r_rdfs5 = \<lparr> rname = ''rdfs5'',
               rbody = [(V ''a'', PI rdfs_subPropertyOf, V ''b''),
                        (V ''b'', PI rdfs_subPropertyOf, V ''c'')],
               rhead = (V ''a'', PI rdfs_subPropertyOf, V ''c'') \<rparr>"
definition r_rdfs7 :: hrule where          (* true W3C name: prp-spo1 *)
  "r_rdfs7 = \<lparr> rname = ''rdfs7'',
               rbody = [(V ''s'', V ''p'', V ''o''), (V ''p'', PI rdfs_subPropertyOf, V ''q'')],
               rhead = (V ''s'', V ''q'', V ''o'') \<rparr>"
definition r_rdfs9 :: hrule where          (* true W3C name: cax-sco *)
  "r_rdfs9 = \<lparr> rname = ''rdfs9'',
               rbody = [(V ''x'', PI rdf_type, V ''a''), (V ''a'', PI rdfs_subClassOf, V ''b'')],
               rhead = (V ''x'', PI rdf_type, V ''b'') \<rparr>"
definition r_rdfs11 :: hrule where         (* true W3C name: scm-sco *)
  "r_rdfs11 = \<lparr> rname = ''rdfs11'',
                rbody = [(V ''a'', PI rdfs_subClassOf, V ''b''),
                         (V ''b'', PI rdfs_subClassOf, V ''c'')],
                rhead = (V ''a'', PI rdfs_subClassOf, V ''c'') \<rparr>"
definition r_prp_trp :: hrule where
  "r_prp_trp = \<lparr> rname = ''prp-trp'',
                 rbody = [(V ''p'', PI rdf_type, PI owl_TransitiveProperty),
                          (V ''x'', V ''p'', V ''y''), (V ''y'', V ''p'', V ''z'')],
                 rhead = (V ''x'', V ''p'', V ''z'') \<rparr>"
definition r_prp_symp :: hrule where
  "r_prp_symp = \<lparr> rname = ''prp-symp'',
                  rbody = [(V ''p'', PI rdf_type, PI owl_SymmetricProperty),
                           (V ''x'', V ''p'', V ''y'')],
                  rhead = (V ''y'', V ''p'', V ''x'') \<rparr>"
definition r_prp_inv1 :: hrule where
  "r_prp_inv1 = \<lparr> rname = ''prp-inv1'',
                  rbody = [(V ''p'', PI owl_inverseOf, V ''q''), (V ''x'', V ''p'', V ''y'')],
                  rhead = (V ''y'', V ''q'', V ''x'') \<rparr>"
definition r_prp_inv2 :: hrule where
  "r_prp_inv2 = \<lparr> rname = ''prp-inv2'',
                  rbody = [(V ''p'', PI owl_inverseOf, V ''q''), (V ''x'', V ''q'', V ''y'')],
                  rhead = (V ''y'', V ''p'', V ''x'') \<rparr>"
definition r_eq_sym :: hrule where
  "r_eq_sym = \<lparr> rname = ''eq-sym'',
                rbody = [(V ''a'', PI owl_sameAs, V ''b'')],
                rhead = (V ''b'', PI owl_sameAs, V ''a'') \<rparr>"
definition r_scm_eqc1a :: hrule where      (* scm-eqc1, arm 1 of 2 -- see M36 *)
  "r_scm_eqc1a = \<lparr> rname = ''scm-eqc1'',
                   rbody = [(V ''a'', PI owl_equivalentClass, V ''b'')],
                   rhead = (V ''a'', PI rdfs_subClassOf, V ''b'') \<rparr>"
definition r_scm_eqc1b :: hrule where      (* scm-eqc1, arm 2 of 2 *)
  "r_scm_eqc1b = \<lparr> rname = ''scm-eqc1'',
                   rbody = [(V ''a'', PI owl_equivalentClass, V ''b'')],
                   rhead = (V ''b'', PI rdfs_subClassOf, V ''a'') \<rparr>"
definition r_scm_eqp1a :: hrule where      (* scm-eqp1, arm 1 of 2 *)
  "r_scm_eqp1a = \<lparr> rname = ''scm-eqp1'',
                   rbody = [(V ''a'', PI owl_equivalentProperty, V ''b'')],
                   rhead = (V ''a'', PI rdfs_subPropertyOf, V ''b'') \<rparr>"
definition r_scm_eqp1b :: hrule where      (* scm-eqp1, arm 2 of 2 *)
  "r_scm_eqp1b = \<lparr> rname = ''scm-eqp1'',
                   rbody = [(V ''a'', PI owl_equivalentProperty, V ''b'')],
                   rhead = (V ''b'', PI rdfs_subPropertyOf, V ''a'') \<rparr>"
definition r_cls_svf1 :: hrule where
  "r_cls_svf1 = \<lparr> rname = ''cls-svf1'',
                  rbody = [(V ''r'', PI owl_onProperty, V ''p''),
                           (V ''r'', PI owl_someValuesFrom, V ''c''),
                           (V ''x'', V ''p'', V ''y''), (V ''y'', PI rdf_type, V ''c'')],
                  rhead = (V ''x'', PI rdf_type, V ''r'') \<rparr>"
definition r_cls_avf :: hrule where
  "r_cls_avf = \<lparr> rname = ''cls-avf'',
                 rbody = [(V ''r'', PI owl_onProperty, V ''p''),
                          (V ''r'', PI owl_allValuesFrom, V ''c''),
                          (V ''x'', PI rdf_type, V ''r''), (V ''x'', V ''p'', V ''y'')],
                 rhead = (V ''y'', PI rdf_type, V ''c'') \<rparr>"
definition r_cls_hv1 :: hrule where
  "r_cls_hv1 = \<lparr> rname = ''cls-hv1'',
                 rbody = [(V ''r'', PI owl_onProperty, V ''p''),
                          (V ''r'', PI owl_hasValue, V ''v''), (V ''x'', PI rdf_type, V ''r'')],
                 rhead = (V ''x'', V ''p'', V ''v'') \<rparr>"
definition r_cls_hv2 :: hrule where
  "r_cls_hv2 = \<lparr> rname = ''cls-hv2'',
                 rbody = [(V ''r'', PI owl_onProperty, V ''p''),
                          (V ''r'', PI owl_hasValue, V ''v''), (V ''x'', V ''p'', V ''v'')],
                 rhead = (V ''x'', PI rdf_type, V ''r'') \<rparr>"
definition r_scm_svf1 :: hrule where
  "r_scm_svf1 = \<lparr> rname = ''scm-svf1'',
                  rbody = [(V ''c1'', PI owl_someValuesFrom, V ''y1''),
                           (V ''c1'', PI owl_onProperty, V ''p''),
                           (V ''c2'', PI owl_someValuesFrom, V ''y2''),
                           (V ''c2'', PI owl_onProperty, V ''p''),
                           (V ''y1'', PI rdfs_subClassOf, V ''y2'')],
                  rhead = (V ''c1'', PI rdfs_subClassOf, V ''c2'') \<rparr>"
definition r_scm_svf2 :: hrule where
  "r_scm_svf2 = \<lparr> rname = ''scm-svf2'',
                  rbody = [(V ''c1'', PI owl_someValuesFrom, V ''y''),
                           (V ''c1'', PI owl_onProperty, V ''p1''),
                           (V ''c2'', PI owl_someValuesFrom, V ''y''),
                           (V ''c2'', PI owl_onProperty, V ''p2''),
                           (V ''p1'', PI rdfs_subPropertyOf, V ''p2'')],
                  rhead = (V ''c1'', PI rdfs_subClassOf, V ''c2'') \<rparr>"
definition r_scm_avf1 :: hrule where
  "r_scm_avf1 = \<lparr> rname = ''scm-avf1'',
                  rbody = [(V ''c1'', PI owl_allValuesFrom, V ''y1''),
                           (V ''c1'', PI owl_onProperty, V ''p''),
                           (V ''c2'', PI owl_allValuesFrom, V ''y2''),
                           (V ''c2'', PI owl_onProperty, V ''p''),
                           (V ''y1'', PI rdfs_subClassOf, V ''y2'')],
                  rhead = (V ''c1'', PI rdfs_subClassOf, V ''c2'') \<rparr>"
(* ROW 22.  THE HEAD IS REVERSED RELATIVE TO ROW 20, AND THAT IS CORRECT.
   allValuesFrom is ANTITONE in the property: if IEXT p1 subset IEXT p2 and
   ICEXT ci = {x : for all y, (x,y) in IEXT pi --> y in ICEXT c}, then ICEXT c2 subset
   ICEXT c1, so it is c2 that is the subclass.  Verified semantically in
   OO_Builtin_Sound (D_avf_mono2), not by trusting the fixture.  A transcription that
   "tidies" this into symmetry with row 20 introduces an UNSOUND rule. *)
definition r_scm_avf2 :: hrule where
  "r_scm_avf2 = \<lparr> rname = ''scm-avf2'',
                  rbody = [(V ''c1'', PI owl_allValuesFrom, V ''y''),
                           (V ''c1'', PI owl_onProperty, V ''p1''),
                           (V ''c2'', PI owl_allValuesFrom, V ''y''),
                           (V ''c2'', PI owl_onProperty, V ''p2''),
                           (V ''p1'', PI rdfs_subPropertyOf, V ''p2'')],
                  rhead = (V ''c2'', PI rdfs_subClassOf, V ''c1'') \<rparr>"
definition r_scm_dom1 :: hrule where
  "r_scm_dom1 = \<lparr> rname = ''scm-dom1'',
                  rbody = [(V ''p'', PI rdfs_domain, V ''c1''),
                           (V ''c1'', PI rdfs_subClassOf, V ''c2'')],
                  rhead = (V ''p'', PI rdfs_domain, V ''c2'') \<rparr>"
definition r_scm_dom2 :: hrule where
  "r_scm_dom2 = \<lparr> rname = ''scm-dom2'',
                  rbody = [(V ''p2'', PI rdfs_domain, V ''c''),
                           (V ''p1'', PI rdfs_subPropertyOf, V ''p2'')],
                  rhead = (V ''p1'', PI rdfs_domain, V ''c'') \<rparr>"
definition r_scm_rng1 :: hrule where
  "r_scm_rng1 = \<lparr> rname = ''scm-rng1'',
                  rbody = [(V ''p'', PI rdfs_range, V ''c1''),
                           (V ''c1'', PI rdfs_subClassOf, V ''c2'')],
                  rhead = (V ''p'', PI rdfs_range, V ''c2'') \<rparr>"
definition r_scm_rng2 :: hrule where
  "r_scm_rng2 = \<lparr> rname = ''scm-rng2'',
                  rbody = [(V ''p2'', PI rdfs_range, V ''c''),
                           (V ''p1'', PI rdfs_subPropertyOf, V ''p2'')],
                  rhead = (V ''p1'', PI rdfs_range, V ''c'') \<rparr>"

definition builtin_table :: rtable where
  "builtin_table = [r_rdfs2, r_rdfs3, r_rdfs5, r_rdfs7, r_rdfs9, r_rdfs11,
                    r_prp_trp, r_prp_symp, r_prp_inv1, r_prp_inv2, r_eq_sym,
                    r_scm_eqc1a, r_scm_eqc1b, r_scm_eqp1a, r_scm_eqp1b,
                    r_cls_svf1, r_cls_avf, r_cls_hv1, r_cls_hv2,
                    r_scm_svf1, r_scm_svf2, r_scm_avf1, r_scm_avf2,
                    r_scm_dom1, r_scm_dom2, r_scm_rng1, r_scm_rng2]"

lemma builtin_table_length: "length builtin_table = 27"
  by (simp add: builtin_table_def)

lemma builtin_index_4: "builtin_table ! 4 = r_rdfs9"
  by (simp add: builtin_table_def)

section \<open>The verdict\<close>

(* DECISION M33 and U13.  The verdict compares the supplied table to the embedded table
   as an ORDERED LIST, element-wise on (name, body, head), variable names literal, with
   no alpha-renaming and no permutation tolerance.  A permuted or renamed built-in table
   therefore receives the WEAKER verdict.  The error direction is conservative; do not
   make this cleverer.

   WHY THIS MATTERS MORE THAN ANYTHING ELSE IN THE FILE.  Without the distinction this
   layer is a machine for turning an assumption into a fact with a proof attached.  A
   one-line user rule reading "every supplier is compliant" -- which is exactly the extra
   row that tests/fixtures/horn/user_rules.tsv appends, and it exists to exercise this --
   makes certificates check green for ever.  The theorem that applies in that case,
   horn_certificate_sound, concludes entails_under, which is a claim about the user's
   assumptions and not about the world. *)

datatype verdict = Entailed | EntailedUnderSuppliedRules

definition verdict_of :: "rtable \<Rightarrow> verdict" where
  "verdict_of R = (if R = builtin_table then Entailed else EntailedUnderSuppliedRules)"

end
