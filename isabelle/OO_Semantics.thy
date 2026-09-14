(* OO_Semantics.thy -- interpretations, truth of a triple, the semantic conditions, and
   the two entailment relations.

   THIS THEORY MUST NEVER ENTER THE CODE-GENERATION CLOSURE.  It quantifies over an
   arbitrary domain type and over interpretations; export_code would fail on any constant
   that mentions sat.  That breakage is a feature: it is what keeps the executable
   checker free of the model theory.

   Primary sources, quoted where a decision turns on the wording:
     RDF11  = RDF 1.1 Semantics, W3C Recommendation 25 February 2014.
     RBS    = OWL 2 Web Ontology Language RDF-Based Semantics (Second Edition),
              W3C Recommendation 11 December 2012.
     PROF   = OWL 2 Web Ontology Language Profiles (Second Edition),
              W3C Recommendation 11 December 2012. *)

theory OO_Semantics
  imports OO_Format
begin

section \<open>Interpretations\<close>

(* DECISION M3.  IL is PARTIAL, and therefore den is partial.
   Rests on RDF11 section 5, which lists among the components of a simple interpretation
   "A partial mapping IL from literals into IR", and states that if IL(E) is undefined
   then any triple containing that literal is false.
   WHY IT MATTERS: totalising IL would delete every interpretation in which some literal
   fails to denote.  The model class shrinks, every soundness theorem over it is weaker
   while looking identical, and the proof assistant reports success throughout.  The cost
   of being faithful is one option.

   DECISION M4.  Blank nodes are RIGID: IB is a component of the interpretation, and
   entailment quantifies over IB along with everything else.
   Rests on RDF11 section 5.1.  NOTE THE DIRECTION OF SAFETY, which is easy to get
   backwards.  Write |=2 for the relation defined here and |=1 for the W3C's
   "for every I there EXISTS an assignment A".  Then |=2 implies |=1: given I and a
   witness A with [I+A] |= G, |=2 yields [I+A] |= t, so A itself witnesses |=1.  The
   converse fails: G = { _:b rdf:type ex:A } |=1 ( _:c rdf:type ex:A ) by re-choosing the
   witness, but not |=2, since IB b and IB c are unrelated.  So |=2 is STRICTLY SMALLER,
   a soundness theorem proved for it is STRONGER, and it transfers to the W3C relation
   for free.  Stated frankly: the theorem below is not literally the W3C's graph
   entailment relation, it implies it.

   DECISION M6.  IEXT is total on the domain in the representation.  Every condition
   below relativises to IP exactly where the specification's quantifier does, and nowhere
   else.  Rests on RDF11 section 5 item 3, which gives IEXT as a mapping from IP. *)

record 'd interp =
  IR   :: "'d set"
  IP   :: "'d set"
  IEXT :: "'d \<Rightarrow> ('d \<times> 'd) set"
  IS   :: "string \<Rightarrow> 'd"
  IB   :: "string \<Rightarrow> 'd"
  IL   :: "string \<Rightarrow> 'd option"

fun den :: "'d interp \<Rightarrow> rdf_term \<Rightarrow> 'd option" where
  "den I (Iri u)   = Some (IS I u)"
| "den I (Bnode b) = Some (IB I b)"
| "den I (Lit l)   = IL I l"

(* DECISION M5.  Truth of a triple requires the PREDICATE's denotation to lie in IP, and
   this is the SINGLE truth condition for every triple whatever its predicate.
   Rests on RDF11 section 5, verbatim: "if E is a ground triple s p o . then I(E) = true
   if I(s), I(p) and I(o) are all defined and <I(s),I(o)> is in IEXT(I(p)), otherwise
   I(E)= false", together with section 5's statement that IEXT is a mapping FROM IP,
   so I(p) in IP is what makes IEXT(I(p)) the relevant extension.

   WHY IT MATTERS, and it is the sharpest trap in the whole exercise: drop the IP clause
   and triples become true whose predicate denotes a non-property.  Seven rows of the
   built-in table (rdfs2, rdfs3, cls-hv2, scm-eqc1 twice, scm-eqp1 twice) have a head
   predicate that no body triple forces into IP; without this clause that proof
   obligation VANISHES rather than being discharged, and the vanishing is invisible to
   any accept/reject comparison because the checker never consults the semantics.

   NOTE that there is no case distinction on the predicate here.  A formalisation that
   gives rdfs:subClassOf, rdfs:subPropertyOf, rdfs:domain or rdfs:range triples their own
   truth clause is not an RDF semantics: RDF11 section 5 gives ONE truth condition for
   all triples, and the vocabulary's meaning enters only through conditions on IEXT. *)

fun sat :: "'d interp \<Rightarrow> triple \<Rightarrow> bool" where
  "sat I (s,p,q) =
      (\<exists>a b c. den I s = Some a \<and> den I p = Some b \<and> den I q = Some c
                \<and> b \<in> IP I \<and> (a,c) \<in> IEXT I b)"

definition models :: "'d interp \<Rightarrow> graph \<Rightarrow> bool" where
  "models I G = (\<forall>t \<in> G. sat I t)"

(* DECISION M7.  ICEXT and IC are DEFINITIONS, not conditions.
   Rests on RDF11 section 9, which introduces ICEXT(y) = {x : <x,y> in IEXT(I(rdf:type))}
   as an abbreviation, and on RBS Table 5.2, which gives rdfs:Class the row "= IC".
   A definition cannot shrink the model class; a condition can. *)

definition ICEXT :: "'d interp \<Rightarrow> 'd \<Rightarrow> 'd set" where
  "ICEXT I y = {x. (x,y) \<in> IEXT I (IS I rdf_type)}"

definition IC :: "'d interp \<Rightarrow> 'd set" where
  "IC I = ICEXT I (IS I rdfs_Class)"

(* DECISION M22 (conflict C6).  wf_interp collects the DOMAIN conditions -- IR nonempty,
   IP contained in IR, IEXT into IR x IR, IS/IB/IL landing in IR.  They are faithful:
   RBS Table 5.1 gives "IP | S | subset of IR" and IEXT(x) subset of IR x IR.  They are
   nevertheless NOT conjuncts of owl_rl_interp, because NO arm of the built-in table
   consumes any of them.  Leaving them out enlarges the model class, which makes
   entails HARDER to establish and the soundness theorem STRONGER.
   wf_interp is used only in the bridge theorem entails_simple (T4), which says the
   result still applies to genuine simple interpretations.

   DECISION M-SORT (trap T5).  There is deliberately NO condition separating classes from
   properties, and the domain is a single untyped set.  Rests on RDF11 section 9
   verbatim: "RDFS does not partition the universe into disjoint categories of classes,
   properties and individuals ... it also permits classes which contain themselves and
   properties which apply to themselves."  A Description-Logic-trained formaliser adds
   IP inter IC = {} without noticing; that would shrink the model class. *)

definition wf_interp :: "'d interp \<Rightarrow> bool" where
  "wf_interp I \<longleftrightarrow>
     IR I \<noteq> {} \<and> IP I \<subseteq> IR I
     \<and> (\<forall>x. IEXT I x \<subseteq> IR I \<times> IR I)
     \<and> (\<forall>u. IS I u \<in> IR I) \<and> (\<forall>b. IB I b \<in> IR I)
     \<and> (\<forall>l v. IL I l = Some v \<longrightarrow> v \<in> IR I)"

section \<open>Semantic conditions, one per specification table row\<close>

(* DECISION M8.  Exactly THREE consequences of the axiomatic triple tables are imported,
   not the tables themselves.
   Rests on RDF11 sections 8 and 9, which assert among the RDF and RDFS axiomatic triples
       rdf:type rdf:type rdf:Property .
       rdf:Alt rdfs:subClassOf rdfs:Container .
       rdfs:isDefinedBy rdfs:subPropertyOf rdfs:seeAlso .
   (all three re-read in the Recommendation while writing this file).  Truth of a triple
   requires its predicate's denotation to be in IP (M5), so each axiomatic triple yields
   exactly one IP membership.  PROF section 4.3 declines to include the axiomatic
   triples, so importing the whole tables would be a strengthening the profile does not
   make; importing these three consequences is the minimum the table needs.
   Consumed by exactly seven rows: rdfs2, rdfs3, cls-hv2 (rdf:type);
   scm-eqc1 arms a and b (rdfs:subClassOf); scm-eqp1 arms a and b (rdfs:subPropertyOf). *)

definition c_type_IP :: "'d interp \<Rightarrow> bool" where
  "c_type_IP I \<longleftrightarrow> IS I rdf_type \<in> IP I"
definition c_sco_IP :: "'d interp \<Rightarrow> bool" where
  "c_sco_IP I \<longleftrightarrow> IS I rdfs_subClassOf \<in> IP I"
definition c_spo_IP :: "'d interp \<Rightarrow> bool" where
  "c_spo_IP I \<longleftrightarrow> IS I rdfs_subPropertyOf \<in> IP I"

(* DECISION M9, THE LARGEST SINGLE DECISION.  RBS Table 5.8 is an IFF for all four of
   rdfs:subClassOf, rdfs:subPropertyOf, rdfs:domain and rdfs:range (the "iff" cell spans
   all four rows; re-fetched and confirmed verbatim while writing this file).  Both
   directions are therefore encoded, split into separately named halves so that the
   consumption of each is visible to a reviewer.
   The target semantics is consequently OWL 2 RDF-BASED, not RDFS.  Twelve arms --
   scm-eqc1 (x2), scm-eqp1 (x2), scm-svf1, scm-svf2, scm-avf1, scm-avf2, scm-dom1,
   scm-dom2, scm-rng1, scm-rng2 -- are UNPROVABLE without the "if" (backward) direction,
   because each concludes a subClassOf, subPropertyOf, domain or range triple that no
   body triple asserts.  The verdict word "entailed" means: true in every interpretation
   satisfying these conditions and the asserted graph.  It does NOT mean "RDFS entailed"
   and it does NOT mean "true in every interpretation" simpliciter.

   TRAP T2, guarded here: the membership conjuncts (c1 in IC, p in IP) are dropped in the
   forward direction by nobody, because there they are a consequence; dropping them from
   the BACKWARD direction would be a strengthening, forcing a subClassOf triple between
   any two things with nested extensions including non-classes.  It looks like tidying,
   it makes the proofs easier, and it never fails.  They are kept. *)

definition c_sco_fwd :: "'d interp \<Rightarrow> bool" where
  "c_sco_fwd I \<longleftrightarrow> (\<forall>c1 c2. (c1,c2) \<in> IEXT I (IS I rdfs_subClassOf) \<longrightarrow>
       c1 \<in> IC I \<and> c2 \<in> IC I \<and> ICEXT I c1 \<subseteq> ICEXT I c2)"
definition c_sco_bwd :: "'d interp \<Rightarrow> bool" where
  "c_sco_bwd I \<longleftrightarrow> (\<forall>c1 c2. c1 \<in> IC I \<longrightarrow> c2 \<in> IC I \<longrightarrow> ICEXT I c1 \<subseteq> ICEXT I c2 \<longrightarrow>
       (c1,c2) \<in> IEXT I (IS I rdfs_subClassOf))"

definition c_spo_fwd :: "'d interp \<Rightarrow> bool" where
  "c_spo_fwd I \<longleftrightarrow> (\<forall>p1 p2. (p1,p2) \<in> IEXT I (IS I rdfs_subPropertyOf) \<longrightarrow>
       p1 \<in> IP I \<and> p2 \<in> IP I \<and> IEXT I p1 \<subseteq> IEXT I p2)"
definition c_spo_bwd :: "'d interp \<Rightarrow> bool" where
  "c_spo_bwd I \<longleftrightarrow> (\<forall>p1 p2. p1 \<in> IP I \<longrightarrow> p2 \<in> IP I \<longrightarrow> IEXT I p1 \<subseteq> IEXT I p2 \<longrightarrow>
       (p1,p2) \<in> IEXT I (IS I rdfs_subPropertyOf))"

(* DECISION M10.  Transitivity of subClassOf and subPropertyOf is kept as a separate
   condition even though Table 5.8's iff makes it derivable.
   Rests on RDF11 section 9, where transitivity is a condition in its own right.
   Kept for DIAGNOSTIC value: the six rdfs* arms then sit in a strictly weaker fragment
   than the twelve arms that need Table 5.8's backward direction, and the consumption map
   in OO_Builtin_Sound shows exactly which arm needs which.

   DECISION M11.  Reflexivity of subClassOf and subPropertyOf is NOT encoded.  No arm
   consumes it, and encoding it would shrink the model class for nothing. *)

definition c_sco_trans :: "'d interp \<Rightarrow> bool" where
  "c_sco_trans I \<longleftrightarrow> (\<forall>a b c. (a,b) \<in> IEXT I (IS I rdfs_subClassOf) \<longrightarrow>
       (b,c) \<in> IEXT I (IS I rdfs_subClassOf) \<longrightarrow> (a,c) \<in> IEXT I (IS I rdfs_subClassOf))"
definition c_spo_trans :: "'d interp \<Rightarrow> bool" where
  "c_spo_trans I \<longleftrightarrow> (\<forall>a b c. (a,b) \<in> IEXT I (IS I rdfs_subPropertyOf) \<longrightarrow>
       (b,c) \<in> IEXT I (IS I rdfs_subPropertyOf) \<longrightarrow> (a,c) \<in> IEXT I (IS I rdfs_subPropertyOf))"

definition c_dom_fwd :: "'d interp \<Rightarrow> bool" where
  "c_dom_fwd I \<longleftrightarrow> (\<forall>p c. (p,c) \<in> IEXT I (IS I rdfs_domain) \<longrightarrow>
       p \<in> IP I \<and> c \<in> IC I \<and> (\<forall>x y. (x,y) \<in> IEXT I p \<longrightarrow> x \<in> ICEXT I c))"
definition c_dom_bwd :: "'d interp \<Rightarrow> bool" where
  "c_dom_bwd I \<longleftrightarrow> (\<forall>p c. p \<in> IP I \<longrightarrow> c \<in> IC I \<longrightarrow>
       (\<forall>x y. (x,y) \<in> IEXT I p \<longrightarrow> x \<in> ICEXT I c) \<longrightarrow> (p,c) \<in> IEXT I (IS I rdfs_domain))"

definition c_rng_fwd :: "'d interp \<Rightarrow> bool" where
  "c_rng_fwd I \<longleftrightarrow> (\<forall>p c. (p,c) \<in> IEXT I (IS I rdfs_range) \<longrightarrow>
       p \<in> IP I \<and> c \<in> IC I \<and> (\<forall>x y. (x,y) \<in> IEXT I p \<longrightarrow> y \<in> ICEXT I c))"
definition c_rng_bwd :: "'d interp \<Rightarrow> bool" where
  "c_rng_bwd I \<longleftrightarrow> (\<forall>p c. p \<in> IP I \<longrightarrow> c \<in> IC I \<longrightarrow>
       (\<forall>x y. (x,y) \<in> IEXT I p \<longrightarrow> y \<in> ICEXT I c) \<longrightarrow> (p,c) \<in> IEXT I (IS I rdfs_range))"

(* DECISION M12.  owl:sameAs: the FORWARD direction only.
   RBS Table 5.9 gives "iff a1 = a2" (confirmed verbatim).  Both readings are faithful;
   this is a weakest-conditions choice, not a correctness one.  The converse would force
   owl:sameAs to hold reflexively across the ENTIRE universe, and NO arm of this table
   consumes that: eq-ref is absent, and eq-sym needs only the forward direction (from
   (x,y) in IEXT(sameAs) get x = y, so (y,x) = (x,y) in IEXT, and sameAs in IP comes from
   the premise's own truth via M5).  Symmetry alone would be the true minimum and is
   implied by what is written here. *)

definition c_sameAs_fwd :: "'d interp \<Rightarrow> bool" where
  "c_sameAs_fwd I \<longleftrightarrow> (\<forall>a b. (a,b) \<in> IEXT I (IS I owl_sameAs) \<longrightarrow> a = b)"

(* DECISION M13.  equivalentClass, equivalentProperty, inverseOf: forward direction only.
   RBS Tables 5.9 and 5.12 give iffs; the converses are consumed by nothing.

   DECISION M14.  inverseOf keeps BOTH INCLUSIONS of the set equality and BOTH IP
   conjuncts.  prp-inv1 and prp-inv2 have head predicates (?q and ?p respectively) that
   no body triple forces into IP, so the IP conjuncts are load-bearing; and the two arms
   use opposite inclusions.  RBS Table 5.12: owl:inverseOf subset of IP x IP, with
   IEXT(p1) = { <x,y> : <y,x> in IEXT(p2) }. *)

definition c_eqc_fwd :: "'d interp \<Rightarrow> bool" where
  "c_eqc_fwd I \<longleftrightarrow> (\<forall>c1 c2. (c1,c2) \<in> IEXT I (IS I owl_equivalentClass) \<longrightarrow>
       c1 \<in> IC I \<and> c2 \<in> IC I \<and> ICEXT I c1 = ICEXT I c2)"
definition c_eqp_fwd :: "'d interp \<Rightarrow> bool" where
  "c_eqp_fwd I \<longleftrightarrow> (\<forall>p1 p2. (p1,p2) \<in> IEXT I (IS I owl_equivalentProperty) \<longrightarrow>
       p1 \<in> IP I \<and> p2 \<in> IP I \<and> IEXT I p1 = IEXT I p2)"
definition c_inv_fwd :: "'d interp \<Rightarrow> bool" where
  "c_inv_fwd I \<longleftrightarrow> (\<forall>p1 p2. (p1,p2) \<in> IEXT I (IS I owl_inverseOf) \<longrightarrow>
       p1 \<in> IP I \<and> p2 \<in> IP I \<and> IEXT I p1 = {(x,y). (y,x) \<in> IEXT I p2})"

(* DECISION M15.  SymmetricProperty and TransitiveProperty: the universally quantified
   part only, NOT the "p in IP" conjunct.  RBS Table 5.13 reads
   "x in ICEXT(owl:SymmetricProperty) iff x in IP and for all y,z ...".  The IP conjunct
   is dropped because in both prp-symp and prp-inv the head predicate is the SAME ?p that
   the body's own triple (?x ?p ?y) already forces into IP through M5.  Keeping it would
   be faithful but redundant; dropping it is the weaker condition. *)

definition c_sym_fwd :: "'d interp \<Rightarrow> bool" where
  "c_sym_fwd I \<longleftrightarrow> (\<forall>p. p \<in> ICEXT I (IS I owl_SymmetricProperty) \<longrightarrow>
       (\<forall>x y. (x,y) \<in> IEXT I p \<longrightarrow> (y,x) \<in> IEXT I p))"
definition c_trp_fwd :: "'d interp \<Rightarrow> bool" where
  "c_trp_fwd I \<longleftrightarrow> (\<forall>p. p \<in> ICEXT I (IS I owl_TransitiveProperty) \<longrightarrow>
       (\<forall>x y z. (x,y) \<in> IEXT I p \<longrightarrow> (y,z) \<in> IEXT I p \<longrightarrow> (x,z) \<in> IEXT I p))"

(* DECISION M16, THE SHARPEST TRAP (T1).  RBS Table 5.6: the OUTER connective is an
   IF-THEN, and the CONSEQUENT is a SET EQUALITY.  Both are load-bearing and they pull in
   opposite directions, which is why this row is so easy to get wrong.

   The specification says twice that the outer connective is an implication: "All the
   semantic conditions are 'if-then' conditions, since the corresponding OWL 2 language
   constructs are class expressions".  Tables 5.8 and 5.9 three sections away ARE iffs,
   and a formaliser carrying that habit into 5.6 shrinks the model class while every
   proof still succeeds.

   The consequent really is an EQUALITY, and both inclusions are consumed:
     superset half  -- cls-svf1 and cls-hv2 (conclude membership in the restriction);
     subset half    -- cls-avf and cls-hv1 (read a consequence off membership);
     both halves    -- scm-svf1, scm-svf2, scm-avf1, scm-avf2.
   Writing only the subset inclusion is the SAFE error: cls-svf1, cls-hv2, scm-svf* and
   scm-avf* simply refuse to go through.  The DANGEROUS moment is the repair -- faced
   with a failing cls-svf1 the natural move is to add a fresh axiom asserting the missing
   direction in slightly different words.  That is a strengthening in a place the
   specification did not strengthen, it turns everything green, and nobody writes it
   down.  The equality is written here, once, as the specification has it. *)

definition c_svf :: "'d interp \<Rightarrow> bool" where
  "c_svf I \<longleftrightarrow> (\<forall>z c p. (z,c) \<in> IEXT I (IS I owl_someValuesFrom) \<longrightarrow>
       (z,p) \<in> IEXT I (IS I owl_onProperty) \<longrightarrow>
       ICEXT I z = {x. \<exists>y. (x,y) \<in> IEXT I p \<and> y \<in> ICEXT I c})"
definition c_avf :: "'d interp \<Rightarrow> bool" where
  "c_avf I \<longleftrightarrow> (\<forall>z c p. (z,c) \<in> IEXT I (IS I owl_allValuesFrom) \<longrightarrow>
       (z,p) \<in> IEXT I (IS I owl_onProperty) \<longrightarrow>
       ICEXT I z = {x. \<forall>y. (x,y) \<in> IEXT I p \<longrightarrow> y \<in> ICEXT I c})"
definition c_hv :: "'d interp \<Rightarrow> bool" where
  "c_hv I \<longleftrightarrow> (\<forall>z a p. (z,a) \<in> IEXT I (IS I owl_hasValue) \<longrightarrow>
       (z,p) \<in> IEXT I (IS I owl_onProperty) \<longrightarrow>
       ICEXT I z = {x. (x,a) \<in> IEXT I p})"

(* DECISION M17 and M18.  The typing rows of RBS Tables 5.2 and 5.3 are MANDATORY, and
   five arms cannot be proved without them.  Re-fetched verbatim while writing this file:
     Table 5.2:  owl:Restriction    | ICEXT(...) SUBSET of IC     (subset, never equality)
     Table 5.3:  owl:someValuesFrom | subset of ICEXT(owl:Restriction) x IC
                 owl:allValuesFrom  | subset of ICEXT(owl:Restriction) x IC
                 owl:onProperty     | subset of ICEXT(owl:Restriction) x IP
   scm-svf1, scm-svf2, scm-avf1 and scm-avf2 conclude a rdfs:subClassOf triple, and
   c_sco_bwd's antecedent demands c1, c2 in IC; nothing else in the condition set supplies
   it, because those rules' premises mention only someValuesFrom/allValuesFrom/onProperty.
   cls-hv1's head predicate is the variable ?p, forced into IP only by the onProperty row.
   M18: Table 5.2 writes SUBSET for owl:Restriction, not equality, and that is what is
   written here. *)

definition c_restr_IC :: "'d interp \<Rightarrow> bool" where
  "c_restr_IC I \<longleftrightarrow> ICEXT I (IS I owl_Restriction) \<subseteq> IC I"
definition c_svf_typ :: "'d interp \<Rightarrow> bool" where
  "c_svf_typ I \<longleftrightarrow> (\<forall>z c. (z,c) \<in> IEXT I (IS I owl_someValuesFrom) \<longrightarrow>
       z \<in> ICEXT I (IS I owl_Restriction) \<and> c \<in> IC I)"
definition c_avf_typ :: "'d interp \<Rightarrow> bool" where
  "c_avf_typ I \<longleftrightarrow> (\<forall>z c. (z,c) \<in> IEXT I (IS I owl_allValuesFrom) \<longrightarrow>
       z \<in> ICEXT I (IS I owl_Restriction) \<and> c \<in> IC I)"
definition c_onp_typ :: "'d interp \<Rightarrow> bool" where
  "c_onp_typ I \<longleftrightarrow> (\<forall>z p. (z,p) \<in> IEXT I (IS I owl_onProperty) \<longrightarrow>
       z \<in> ICEXT I (IS I owl_Restriction) \<and> p \<in> IP I)"

(* The model class.  Note what is NOT a conjunct: wf_interp (M22), any sortal separation
   (M-SORT), reflexivity of subClassOf (M11), the converse of sameAs (M12), the
   axiomatic triple TABLES as opposed to three of their consequences (M8), and the
   Table 5.2 equality ICEXT(rdf:Property) = IP -- which is spec-faithful but consumed by
   no arm, so adding it would only shrink the model class. *)

definition owl_rl_interp :: "'d interp \<Rightarrow> bool" where
  "owl_rl_interp I \<longleftrightarrow>
       c_type_IP I \<and> c_sco_IP I \<and> c_spo_IP I
     \<and> c_sco_fwd I \<and> c_sco_bwd I \<and> c_spo_fwd I \<and> c_spo_bwd I
     \<and> c_sco_trans I \<and> c_spo_trans I
     \<and> c_dom_fwd I \<and> c_dom_bwd I \<and> c_rng_fwd I \<and> c_rng_bwd I
     \<and> c_sameAs_fwd I \<and> c_eqc_fwd I \<and> c_eqp_fwd I \<and> c_inv_fwd I
     \<and> c_sym_fwd I \<and> c_trp_fwd I
     \<and> c_svf I \<and> c_avf I \<and> c_hv I
     \<and> c_restr_IC I \<and> c_svf_typ I \<and> c_avf_typ I \<and> c_onp_typ I"

section \<open>Entailment\<close>

(* DECISION M21 (conflict C10).  The domain type is an explicit parameter, passed as
   TYPE('d) of type 'd itself.  HOL cannot quantify over types inside a proposition, so
   the statement below is SCHEMATIC in 'd rather than a single proposition quantifying
   over all domain types.  An impredicative-Prop system can write the quantifier
   directly, and its top-level statement will therefore LOOK different for reasons of
   logic, not of modelling.  Recorded here so that a reviewer comparing two
   formalisations does not read a presentational difference as divergence.
   UNCERTAINTY U6, stated as unsure: whether the schematic HOL statement is equivalent to
   the set-theoretic "for all domains" statement is routine for range-restricted Horn
   rules but is NOT formalised here. *)

definition entails :: "'d itself \<Rightarrow> graph \<Rightarrow> triple \<Rightarrow> bool" where
  "entails TYPE('d) G t \<longleftrightarrow>
     (\<forall>I :: 'd interp. owl_rl_interp I \<longrightarrow> models I G \<longrightarrow> sat I t)"

(* DECISION M19 (trap T7).  Rule satisfaction quantifies over TERM SUBSTITUTIONS, not
   over valuations into the domain.  Rests on PROF section 4.3, which states the RL/RDF
   rules as schemas over triple patterns whose variables range over terms.
   NOTE THE DIRECTION OF SAFETY, which is the opposite of what "more faithful-sounding"
   suggests: quantifying over domain valuations would SHRINK the class of rule-satisfying
   interpretations, hence shrink the class quantified over in entails_under, hence make
   entailed_under_supplied_rules a WEAKER claim than it appears.  Term substitutions is
   the safe side. *)

definition sat_rule :: "'d interp \<Rightarrow> hrule \<Rightarrow> bool" where
  "sat_rule I R \<longleftrightarrow>
     (\<forall>\<sigma>. (\<forall>u \<in> set (rbody R). sat I (apt \<sigma> u)) \<longrightarrow> sat I (apt \<sigma> (rhead R)))"

(* DECISION M20.  entails_under carries NO vocabulary conditions and NO domain conditions
   WHATEVER.  The user's rules are the only assumption, and the theorem says so.
   That asymmetry is deliberate and structural: it is what makes the two verdicts come
   apart as a matter of what is quantified over, rather than by convention in a report
   string.  A one-line rule table reading "every supplier is compliant" then yields
   exactly what it should -- a conclusion true in every interpretation that satisfies
   that assumption, which is a claim about the user's assumption and not about the
   world. *)

definition entails_under :: "'d itself \<Rightarrow> rtable \<Rightarrow> graph \<Rightarrow> triple \<Rightarrow> bool" where
  "entails_under TYPE('d) Rs G t \<longleftrightarrow>
     (\<forall>I :: 'd interp. (\<forall>R \<in> set Rs. sat_rule I R) \<longrightarrow> models I G \<longrightarrow> sat I t)"

lemma entails_of_entails_under:
  assumes tbl: "\<And>I :: 'd interp. owl_rl_interp I \<Longrightarrow> \<forall>R \<in> set Rs. sat_rule I R"
    and eu: "entails_under TYPE('d) Rs G t"
  shows "entails TYPE('d) G t"
  using assms by (auto simp: entails_def entails_under_def)

end
