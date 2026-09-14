(* OO_Export.thy -- code generation.

   THE TRUST BOUNDARY, stated rather than implied.
   INSIDE:  the Isabelle kernel; OO_Format, OO_Check, OO_Parse (the executable part);
            OO_Semantics, OO_Sound, OO_Builtin_Sound (the theorems); and the code
            generator itself, which is TRUSTED, NOT VERIFIED -- exactly as the compiler
            is on any other side of any comparison.
   OUTSIDE: file IO, splitting bytes on LF and TAB, exit codes, JSON, and the claim that
            the engine's asserted.tsv is the store it says it is.

   OO_Semantics MUST NEVER ENTER THE EXPORT CLOSURE.  It quantifies over an arbitrary
   domain type and over interpretations, and export_code fails on any constant lacking
   code equations.  If a single exported constant came to mention sat, this build would
   break -- and that breakage is a feature, because it is what keeps the running checker
   free of the model theory. *)

theory OO_Export
  imports OO_Parse
begin

(* Byte-level conversion for the untrusted driver.  The verified core is over
   string = char list (DECISION M38), so the driver must turn native SML bytes into
   Isabelle chars and back.  char_of is total on 0..255, so every byte round-trips and a
   non-ASCII UTF-8 IRI is carried through unchanged -- which is the whole reason for
   M38.  Note the driver must use SML's OWN String.explode on a native byte string, not
   Isabelle's, which is the one that raises on non-ASCII. *)

definition chr_of_nat :: "nat \<Rightarrow> char" where "chr_of_nat n = char_of n"
definition nat_of_chr :: "char \<Rightarrow> nat" where "nat_of_chr c = of_char c"

lemma chr_nat_roundtrip: "n < 256 \<Longrightarrow> nat_of_chr (chr_of_nat n) = n"
  by (simp add: chr_of_nat_def nat_of_chr_def)

(* Sanity: the things that must be executable, are. *)
value "length builtin_table"
value "verdict_of builtin_table"

export_code
  run_check run_check_lenient
  check_cert check_cert_lenient accepts
  verdict_of builtin_table
  parse_rules parse_graph parse_cert
  Ok Rejected ParseError Entailed EntailedUnderSuppliedRules
  R_index_out_of_range R_arity_mismatch R_binding_incomplete R_binding_dup_key
  R_body_mismatch R_premise_unknown R_head_mismatch
  Iri Bnode Lit V Tm
  nat_of_integer integer_of_nat chr_of_nat nat_of_chr
  in SML module_name OOHorn file_prefix "oo_horn"

end
