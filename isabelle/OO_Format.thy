(* OO_Format.thy -- syntax of terms, triples, rule patterns, rules and certificate steps.

   INDEPENDENT SECOND FORMALISATION.  Nothing under lean/ was read, listed, grepped or
   reasoned about by the author of this file.  Sources used: RDF 1.1 Semantics (W3C REC
   25 Feb 2014), OWL 2 Web Ontology Language Profiles (W3C REC 11 Dec 2012) section 4.3,
   OWL 2 RDF-Based Semantics (W3C REC 11 Dec 2012) section 5, and the fixture DATA under
   tests/fixtures/horn/.

   This theory carries NO semantics.  It is pure syntax, so that the checker (OO_Check)
   can be executable and the model theory (OO_Semantics) can be classical, with the two
   meeting only in OO_Sound. *)

theory OO_Format
  imports Main "HOL-Library.Code_Target_Nat"
begin

section \<open>Terms\<close>

(* DECISION M1.  Terms are opaque byte strings, compared by syntactic equality.  No
   datatype-aware comparison of literals.
   Rests on: no rule in the fixture table is datatype-sensitive, and OWL 2 Profiles
   section 4.3 states the RL/RDF rules over triple patterns without any value-space
   side condition.  SCOPED CLAIM: if cls-maxc2 (which compares two object terms for
   equality of VALUE) is ever added, "01"^^xsd:nonNegativeInteger is one value and two
   terms and this decision becomes unsound for that rule.

   DECISION M38.  string = char list, NOT String.literal.  String.literal is ASCII-only
   in the logic (typedef literal = "{cs. ALL c:set cs. ~ digit7 c}") and its generated
   SML raises on a non-ASCII byte, so a UTF-8 IRI would exist in the running checker with
   no counterpart in the logical type and the theorem would not apply to that run.
   Verified against the Isabelle2025-2 sources on this machine. *)

datatype rdf_term = Iri string | Bnode string | Lit string

type_synonym triple = "rdf_term \<times> rdf_term \<times> rdf_term"
type_synonym graph  = "triple set"

(* DECISION M2.  Generalized triples: any term in any position, subject and predicate
   included.  There is NO RDF well-formedness side condition anywhere in this
   development.
   Rests on: OWL 2 Profiles section 4.3, which permits blank nodes and literals in all
   positions of the RL/RDF rules, and RDF 1.1 Semantics Appendix A (generalized RDF).
   Consequence: a conclusion may be a triple that cannot be written in concrete RDF.
   That is deliberate; see M31. *)

section \<open>Vocabulary\<close>

(* The IRIs whose meaning the built-in table depends on.  These are bare IRIs, with the
   N-Triples angle brackets stripped: see DECISION D-PARSE-2 in OO_Parse.  RDF 1.1
   Semantics section 5 maps IRIs, not their concrete syntax, so IS is a function on
   IRIs and not on N-Triples spellings. *)

definition rdf_type :: string where
  "rdf_type = ''http://www.w3.org/1999/02/22-rdf-syntax-ns#type''"
definition rdfs_Class :: string where
  "rdfs_Class = ''http://www.w3.org/2000/01/rdf-schema#Class''"
definition rdfs_subClassOf :: string where
  "rdfs_subClassOf = ''http://www.w3.org/2000/01/rdf-schema#subClassOf''"
definition rdfs_subPropertyOf :: string where
  "rdfs_subPropertyOf = ''http://www.w3.org/2000/01/rdf-schema#subPropertyOf''"
definition rdfs_domain :: string where
  "rdfs_domain = ''http://www.w3.org/2000/01/rdf-schema#domain''"
definition rdfs_range :: string where
  "rdfs_range = ''http://www.w3.org/2000/01/rdf-schema#range''"
definition owl_sameAs :: string where
  "owl_sameAs = ''http://www.w3.org/2002/07/owl#sameAs''"
definition owl_equivalentClass :: string where
  "owl_equivalentClass = ''http://www.w3.org/2002/07/owl#equivalentClass''"
definition owl_equivalentProperty :: string where
  "owl_equivalentProperty = ''http://www.w3.org/2002/07/owl#equivalentProperty''"
definition owl_inverseOf :: string where
  "owl_inverseOf = ''http://www.w3.org/2002/07/owl#inverseOf''"
definition owl_SymmetricProperty :: string where
  "owl_SymmetricProperty = ''http://www.w3.org/2002/07/owl#SymmetricProperty''"
definition owl_TransitiveProperty :: string where
  "owl_TransitiveProperty = ''http://www.w3.org/2002/07/owl#TransitiveProperty''"
definition owl_Restriction :: string where
  "owl_Restriction = ''http://www.w3.org/2002/07/owl#Restriction''"
definition owl_onProperty :: string where
  "owl_onProperty = ''http://www.w3.org/2002/07/owl#onProperty''"
definition owl_someValuesFrom :: string where
  "owl_someValuesFrom = ''http://www.w3.org/2002/07/owl#someValuesFrom''"
definition owl_allValuesFrom :: string where
  "owl_allValuesFrom = ''http://www.w3.org/2002/07/owl#allValuesFrom''"
definition owl_hasValue :: string where
  "owl_hasValue = ''http://www.w3.org/2002/07/owl#hasValue''"

section \<open>Rule patterns and rules\<close>

datatype pat = V string | Tm rdf_term
type_synonym pat_triple = "pat \<times> pat \<times> pat"

(* DECISION M36.  A W3C rule whose consequent is a conjunction is split into one Horn
   arm per conjunct.  scm-eqc1 and scm-eqp1 each become two rows.
   Rests on: OWL 2 Profiles Table 9, where scm-eqc1 licenses both C1 sco C2 and
   C2 sco C1; and the fixture, which has already taken this reading (rows 11/12 and
   13/14 share a name).

   DECISION M-NAME (this file).  rname is a LABEL, not a key.  Two rows may carry the
   same name.  Nothing in the checker or the semantics looks a rule up by name. *)

record hrule =
  rname :: string
  rbody :: "pat_triple list"
  rhead :: "pat_triple"

type_synonym rtable = "hrule list"

(* DECISION M23.  The rule index is 0-based into an ORDERED list.
   Rests on: the fixture good.tsv cites index 4, and row 5 of builtin_rules.tsv counting
   from one -- that is rdfs9, whose body (?x type ?a), (?a sco ?b) and head (?x type ?b)
   are exactly what good.tsv's binding and premises instantiate.  Verified field by
   field against the fixture; no other reading makes good.tsv check.

   DECISION M27/M28.  sprem lists the premises the step cites, in the SUPPLIED TABLE's
   body order, not any W3C table's order.  The fixture's rows 0-5 reverse the W3C order
   and rows 15-18 swap the first two atoms, so body order is a property of the table
   that is in force and of nothing else. *)

record hstep =
  sidx   :: nat
  sbind  :: "(string \<times> rdf_term) list"
  sconcl :: triple
  sprem  :: "triple list"

section \<open>Instantiation at two levels\<close>

(* DECISION M-BIND (conflict C9 in the brief).  Two representations of a binding, with a
   bridge.

   The SEMANTICS quantifies over a TOTAL function string => rdf_term.  That is the right
   notion for rule satisfaction: a rule is satisfied when every substitution making the
   body true makes the head true, and nothing should turn on which variables a
   substitution happens to mention.

   The CHECKER carries the finite association list that the certificate file supplies,
   because that is what is executable.

   tot_of bridges them.  Lemmas B1/B2 in OO_Sound show the finite map and its total
   extension agree wherever the finite map is defined, which is everywhere the checker
   looks. *)

type_synonym bnd = "string \<Rightarrow> rdf_term"

fun ap :: "bnd \<Rightarrow> pat \<Rightarrow> rdf_term" where
  "ap \<sigma> (V x)  = \<sigma> x"
| "ap \<sigma> (Tm c) = c"

fun apt :: "bnd \<Rightarrow> pat_triple \<Rightarrow> triple" where
  "apt \<sigma> (s,p,q) = (ap \<sigma> s, ap \<sigma> p, ap \<sigma> q)"

(* DECISION M24.  Binding keys are written WITHOUT the leading question mark; rule
   variables are written WITH it.  Rests on the fixture: good.tsv's binding keys are
   x, a, b while builtin_rules.tsv row 4 writes ?x, ?a, ?b.  The question mark is
   stripped at parse time (OO_Parse), so by the time a pattern reaches ipat the
   variable name is the bare one.  If this were wrong nothing would instantiate and
   every certificate would be rejected: the error is loud, not silent. *)

fun ipat :: "(string \<times> rdf_term) list \<Rightarrow> pat \<Rightarrow> rdf_term option" where
  "ipat \<beta> (Tm c) = Some c"
| "ipat \<beta> (V x)  = map_of \<beta> x"

definition iptriple :: "(string \<times> rdf_term) list \<Rightarrow> pat_triple \<Rightarrow> triple option" where
  "iptriple \<beta> tp =
     (case tp of (s,p,q) \<Rightarrow>
        (case ipat \<beta> s of None \<Rightarrow> None | Some a \<Rightarrow>
         (case ipat \<beta> p of None \<Rightarrow> None | Some b \<Rightarrow>
          (case ipat \<beta> q of None \<Rightarrow> None | Some c \<Rightarrow> Some (a,b,c)))))"

lemma iptriple_simp [simp]:
  "iptriple \<beta> (s,p,q) =
     (case ipat \<beta> s of None \<Rightarrow> None | Some a \<Rightarrow>
      (case ipat \<beta> p of None \<Rightarrow> None | Some b \<Rightarrow>
       (case ipat \<beta> q of None \<Rightarrow> None | Some c \<Rightarrow> Some (a,b,c))))"
  by (simp add: iptriple_def)

fun pat_vars1 :: "pat \<Rightarrow> string list" where
  "pat_vars1 (V x)  = [x]"
| "pat_vars1 (Tm _) = []"

fun pat_var_list :: "pat_triple \<Rightarrow> string list" where
  "pat_var_list (s,p,q) = pat_vars1 s @ pat_vars1 p @ pat_vars1 q"

definition rule_var_list :: "hrule \<Rightarrow> string list" where
  "rule_var_list r = remdups (concat (map pat_var_list (rbody r @ [rhead r])))"

(* The total extension of a finite binding.  The default is never reached on any
   variable the checker consults; see coverage_implied in OO_Sound. *)
definition tot_of :: "(string \<times> rdf_term) list \<Rightarrow> bnd" where
  "tot_of \<beta> = (\<lambda>v. case map_of \<beta> v of Some t \<Rightarrow> t | None \<Rightarrow> Iri [])"

end
