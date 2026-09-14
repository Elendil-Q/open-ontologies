(* OO_Parse.thy -- from TSV field lists to the datatypes.  EXECUTABLE.

   The untrusted driver does the file IO and the splitting on LF and TAB; it hands this
   theory a list of rows, each a list of byte strings.  Everything from there on is
   verified.  Splitting is the only logic outside the theorem, and it is four lines --
   which is only possible because the format has NO ESCAPING LAYER: an N-Triples spelling
   cannot contain a raw TAB or LF, so no unescaping is needed and no real logic is
   pushed into untrusted code. *)

theory OO_Parse
  imports OO_Check
begin

section \<open>Decimal naturals\<close>

definition digit_of :: "char \<Rightarrow> nat option" where
  "digit_of c = (let k = of_char c :: nat in if 48 \<le> k \<and> k \<le> 57 then Some (k - 48) else None)"

fun parse_nat_acc :: "nat \<Rightarrow> string \<Rightarrow> nat option" where
  "parse_nat_acc acc [] = Some acc"
| "parse_nat_acc acc (c # cs) =
     (case digit_of c of None \<Rightarrow> None | Some d \<Rightarrow> parse_nat_acc (acc * 10 + d) cs)"

definition parse_nat :: "string \<Rightarrow> nat option" where
  "parse_nat s = (if s = [] then None else parse_nat_acc 0 s)"

section \<open>Terms and patterns\<close>

(* DECISION D-PARSE-2, AND IT IS A REAL CHOICE.  The N-Triples delimiters are STRIPPED:
   <IRI> becomes Iri IRI, _:b becomes Bnode b, anything else becomes Lit with the field
   kept VERBATIM (a literal's quotes, language tag and datatype suffix are part of the
   term and are never decomposed -- M1 says terms are opaque).
   Rests on RDF 1.1 Semantics section 5, where IS maps IRIs, not their concrete syntax;
   keeping the angle brackets would make IS a function on N-Triples spellings instead.

   WHY THE CHOICE IS SAFE FOR A DIFFERENTIAL TEST, and this is worth stating because it
   looks like a place two implementations could diverge: the same function is applied to
   the rule file, the graph file and the certificate file, so it is a RENAMING of terms
   that is applied uniformly.  The checker compares terms only for equality.  Any
   injective renaming therefore leaves every accept/reject decision unchanged.  The
   choice is visible only in the SEMANTICS, where it decides which string IS is applied
   to -- and there it is the faithful one.

   Dispatch is on the first byte and, for IRIs, the last: a field that opens with < but
   does not close with > is NOT an IRI and falls through to Lit rather than being
   silently truncated. *)

definition parse_term :: "string \<Rightarrow> rdf_term" where
  "parse_term s =
     (if s \<noteq> [] \<and> hd s = CHR ''<'' \<and> last s = CHR ''>'' \<and> 2 \<le> length s
        then Iri (butlast (tl s))
      else if take 2 s = ''_:'' then Bnode (drop 2 s)
      else Lit s)"

(* DECISION M24, applied.  A rule field beginning with ? is a VARIABLE and the question
   mark is stripped; every other rule field is a ground term.  A certificate field is
   never a pattern, so parse_term is used there and a field spelled ?x in a graph or a
   certificate becomes the literal term ?x.  That asymmetry is correct: rule fields are
   patterns, data fields are terms. *)

definition parse_pat :: "string \<Rightarrow> pat" where
  "parse_pat s = (if s \<noteq> [] \<and> hd s = CHR ''?'' then V (tl s) else Tm (parse_term s))"

section \<open>Grouping fields\<close>

fun group2 :: "'a list \<Rightarrow> ('a \<times> 'a) list option" where
  "group2 [] = Some []"
| "group2 [x] = None"
| "group2 (a # b # r) = (case group2 r of None \<Rightarrow> None | Some ts \<Rightarrow> Some ((a,b) # ts))"

fun group3 :: "'a list \<Rightarrow> ('a \<times> 'a \<times> 'a) list option" where
  "group3 [] = Some []"
| "group3 [x] = None"
| "group3 [x,y] = None"
| "group3 (a # b # c # r) = (case group3 r of None \<Rightarrow> None | Some ts \<Rightarrow> Some ((a,b,c) # ts))"

fun seq_opt :: "'a option list \<Rightarrow> 'a list option" where
  "seq_opt [] = Some []"
| "seq_opt (x # xs) =
     (case x of None \<Rightarrow> None
      | Some v \<Rightarrow> (case seq_opt xs of None \<Rightarrow> None | Some vs \<Rightarrow> Some (v # vs)))"

definition mk_pt :: "string \<times> string \<times> string \<Rightarrow> pat_triple" where
  "mk_pt f = (case f of (a,b,c) \<Rightarrow> (parse_pat a, parse_pat b, parse_pat c))"

definition mk_tr :: "string \<times> string \<times> string \<Rightarrow> triple" where
  "mk_tr f = (case f of (a,b,c) \<Rightarrow> (parse_term a, parse_term b, parse_term c))"

section \<open>Rows\<close>

(* Rule row: name TAB n TAB (3n body fields) TAB (3 head fields), so the field count is
   5 + 3n.  Re-verified against tests/fixtures/horn/builtin_rules.tsv: the invariant holds
   for all 27 rows, for all 28 rows of user_rules.tsv, and for all 3 of short_rules.tsv. *)

definition pat3_of :: "string list \<Rightarrow> pat_triple option" where
  "pat3_of fs = (if length fs = 3 then Some (mk_pt (fs ! 0, fs ! 1, fs ! 2)) else None)"

definition tr3_of :: "string list \<Rightarrow> triple option" where
  "tr3_of fs = (if length fs = 3 then Some (mk_tr (fs ! 0, fs ! 1, fs ! 2)) else None)"

definition parse_rule_row :: "string list \<Rightarrow> hrule option" where
  "parse_rule_row fs =
     (if length fs < 5 then None else
      (case parse_nat (fs ! 1) of None \<Rightarrow> None | Some n \<Rightarrow>
       (if length fs \<noteq> 5 + 3 * n then None else
        (case group3 (take (3 * n) (drop 2 fs)) of None \<Rightarrow> None | Some bs \<Rightarrow>
         (case pat3_of (drop (2 + 3 * n) fs) of None \<Rightarrow> None | Some h \<Rightarrow>
          Some \<lparr> rname = fs ! 0, rbody = map mk_pt bs, rhead = h \<rparr>)))))"

definition parse_graph_row :: "string list \<Rightarrow> triple option" where
  "parse_graph_row fs = tr3_of fs"

(* DECISION D-PARSE-3, AN INDEPENDENT FINDING THAT CONTRADICTS THE BRIEF THIS WORK WAS
   GIVEN.  The brief asserts that a certificate line "cannot be fully parsed without the
   rule table", because the premise count m is not in the file and equals the length of
   the cited rule's body, so that parsing must be table-relative.

   THAT IS FALSE, and the arithmetic shows it.  The field count is
       NF = 2 + 2k + 3 + 3m
   and k IS in the file, as field 2.  So m = (NF - 5 - 2k) / 3 is recoverable from the
   line alone.  Checked against good.tsv: NF = 17, k = 3, giving m = 2, which is the body
   length of rule 4 (rdfs9).  Parsing is therefore TABLE-INDEPENDENT, and the table is
   consulted only by the checker.

   The consequence is not cosmetic.  Under table-relative parsing an out-of-range rule
   index makes the line unparseable, which forces it to be reported as a PARSE ERROR
   (exit 2).  Under this reading it parses cleanly and is REJECTED by check_step with
   R_index_out_of_range (exit 1), which is what the fixture bad_index.tsv should get and
   what a rejection ought to be.  If another implementation reports exit 2 for
   bad_index.tsv, this is why, and it is a difference of parser architecture rather than
   of judgement about the certificate.

   A wrong premise count is then caught by the checker as R_arity_mismatch, comparing the
   parsed premise list against the cited rule's actual body length. *)

definition parse_cert_row :: "string list \<Rightarrow> hstep option" where
  "parse_cert_row fs =
     (if length fs < 5 then None else
      (case parse_nat (fs ! 0) of None \<Rightarrow> None | Some i \<Rightarrow>
       (case parse_nat (fs ! 1) of None \<Rightarrow> None | Some k \<Rightarrow>
        (if length fs < 5 + 2 * k then None else
         (case group2 (take (2 * k) (drop 2 fs)) of None \<Rightarrow> None | Some bp \<Rightarrow>
          (case tr3_of (take 3 (drop (2 + 2 * k) fs)) of None \<Rightarrow> None | Some c \<Rightarrow>
           (case group3 (drop (5 + 2 * k) fs) of None \<Rightarrow> None | Some ps \<Rightarrow>
            Some \<lparr> sidx = i,
                   sbind = map (\<lambda>q. (fst q, parse_term (snd q))) bp,
                   sconcl = c,
                   sprem = map mk_tr ps \<rparr>)))))))"

definition parse_rules :: "string list list \<Rightarrow> rtable option" where
  "parse_rules ls = seq_opt (map parse_rule_row ls)"

definition parse_graph :: "string list list \<Rightarrow> triple list option" where
  "parse_graph ls = seq_opt (map parse_graph_row ls)"

definition parse_cert :: "string list list \<Rightarrow> hstep list option" where
  "parse_cert ls = seq_opt (map parse_cert_row ls)"

section \<open>The whole run, as one function\<close>

(* DECISION M-EXIT (C12, U11).  Three outcomes, mapped by the driver to exit codes:
     Ok v         -> 0, and the verdict word is v
     Rejected j e -> 1, naming the first failing step and why
     ParseError   -> 2
   A differential test should compare the ACCEPT/REJECT BIT and the VERDICT WORD as
   primary, and the exit code and reason as secondary with a declared tolerance. *)

datatype outcome = Ok verdict | Rejected nat reason | ParseError

definition run_check ::
  "string list list \<Rightarrow> string list list \<Rightarrow> string list list \<Rightarrow> outcome" where
  "run_check rl gl cl =
     (case parse_rules rl of None \<Rightarrow> ParseError | Some R \<Rightarrow>
      (case parse_graph gl of None \<Rightarrow> ParseError | Some G \<Rightarrow>
       (case parse_cert cl of None \<Rightarrow> ParseError | Some C \<Rightarrow>
        (case check_cert R G C of
           None \<Rightarrow> Ok (verdict_of R)
         | Some (j,e) \<Rightarrow> Rejected j e))))"

(* The lenient bit, computed alongside so a report can carry both (conflict C11). *)
definition run_check_lenient ::
  "string list list \<Rightarrow> string list list \<Rightarrow> string list list \<Rightarrow> outcome" where
  "run_check_lenient rl gl cl =
     (case parse_rules rl of None \<Rightarrow> ParseError | Some R \<Rightarrow>
      (case parse_graph gl of None \<Rightarrow> ParseError | Some G \<Rightarrow>
       (case parse_cert cl of None \<Rightarrow> ParseError | Some C \<Rightarrow>
        (case check_cert_lenient R G C of
           None \<Rightarrow> Ok (verdict_of R)
         | Some (j,e) \<Rightarrow> Rejected j e))))"

end
