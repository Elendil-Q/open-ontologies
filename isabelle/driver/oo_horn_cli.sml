(* oo_horn_cli.sml -- the UNTRUSTED command-line wrapper.  NO THEOREM COVERS THIS FILE.

   It exists so the Isabelle checker can be driven exactly as `lean/HMain.lean` drives
   the Lean one:

       oo-horn-isabelle check RULES.tsv ASSERTED.tsv CERT.tsv

   with the SAME exit-code discipline: 0 accepted, 1 rejected, 2 unreadable or
   unparseable.  That symmetry is the whole point -- a differential test that had to
   translate one side's exit codes into the other's would be comparing the translation.

   Two extra modes, both harness conveniences and neither part of any theorem:

       oo-horn-isabelle batch MANIFEST.tsv
           one `RULES<TAB>ASSERTED<TAB>CERT` per line, one JSON object per line out,
           each carrying the exit code it would have produced.  Hundreds of rows in one
           process, because starting a process per certificate is the only thing that
           makes the comparison slow.

       oo-horn-isabelle table RULES.tsv
           prints the verdict word `verdict_of` assigns to that rule table, i.e.
           whether the file IS the table embedded in OO_Check.thy.  This is what makes
           the verdict comparison mean anything: the Lean side pins
           tests/fixtures/horn/builtin_rules.tsv against its own `Builtin.asHorn`, and
           this pins the same bytes against Isabelle's `builtin_table`, so the two
           embedded tables are shown equal THROUGH the fixture rather than assumed.

   Everything outside the verified core is here and in oo_horn_driver.sml: file IO,
   splitting bytes on LF and TAB, JSON, exit codes.  Splitting is four lines, which is
   possible only because the format has no escaping layer.

   It uses SML's OWN String.explode on a native byte string, not Isabelle's, so a
   non-ASCII byte is carried into the verified core unchanged (DECISION M38). *)

fun toChar c = OOHorn.chr_of_nat (OOHorn.nat_of_integer (IntInf.fromInt (Char.ord c)));
fun toStr s  = List.map toChar (String.explode s);
fun natToInt n = IntInf.toInt (OOHorn.integer_of_nat n);

exception ReadError of string;

fun readFile path =
  (let val s = TextIO.openIn path
       val d = TextIO.inputAll s
   in TextIO.closeIn s; d end)
  handle IO.Io _ => raise ReadError path
       | OS.SysErr _ => raise ReadError path;

(* the whole of the untrusted parsing *)
fun splitOn c s = String.fields (fn x => x = c) s;
fun rows text =
  List.map (fn line => List.map toStr (splitOn #"\t" line))
           (List.filter (fn l => l <> "") (splitOn #"\n" text));

fun reasonStr r = case r of
    OOHorn.R_index_out_of_range => "index_out_of_range"
  | OOHorn.R_arity_mismatch     => "arity_mismatch"
  | OOHorn.R_binding_incomplete => "binding_incomplete"
  | OOHorn.R_binding_dup_key    => "binding_dup_key"
  | OOHorn.R_body_mismatch j    => "body_mismatch:" ^ Int.toString (natToInt j)
  | OOHorn.R_premise_unknown j  => "premise_unknown:" ^ Int.toString (natToInt j)
  | OOHorn.R_head_mismatch      => "head_mismatch";

fun verdictStr v = case v of
    OOHorn.Entailed                   => "entailed"
  | OOHorn.EntailedUnderSuppliedRules => "entailed_under_supplied_rules";

fun outcomeStr oc = case oc of
    OOHorn.Ok v           => "ok " ^ verdictStr v
  | OOHorn.Rejected (j,r) => "rejected step=" ^ Int.toString (natToInt j) ^
                             " reason=" ^ reasonStr r
  | OOHorn.ParseError     => "parse_error";

fun exitCode oc = case oc of
    OOHorn.Ok _       => 0
  | OOHorn.Rejected _ => 1
  | OOHorn.ParseError => 2;

fun jsonStr s =
  "\"" ^ String.translate (fn #"\"" => "\\\"" | #"\\" => "\\\\" | c => String.str c) s ^ "\"";

(* The theorem each outcome names, and what it means.  The relativised verdict names the
   conditional theorem BECAUSE nothing discharges a user-supplied rule: the certificate
   carries it as an assumption.  Same discipline as lean/HMain.lean, deliberately, so a
   report from either side reads the same. *)
fun theoremOf v = case v of
    OOHorn.Entailed                   => "OOHorn.run_check_entailed_sound"
  | OOHorn.EntailedUnderSuppliedRules => "OOHorn.run_check_sound";

fun meansOf v = case v of
    OOHorn.Entailed =>
      "every conclusion is true in every model of the asserted graph"
  | OOHorn.EntailedUnderSuppliedRules =>
      "every conclusion is true in every model of the asserted graph THAT ALSO SATISFIES \
      \the supplied rules; the rules themselves are assumed, not checked";

(* One JSON object per run, carrying BOTH the strict and the lenient judgement.  The
   strict one is the verdict and the exit code; the lenient one is reported beside it
   because strict_implies_lenient makes a disagreement between the two a KNOWN class of
   input (premises listed out of order but all asserted) rather than a surprise. *)
fun reportJson rulesF assertedF certF strict lenient =
  let
    val head =
      "{\"checker\":\"isabelle-OOHorn\"" ^
      ",\"rules\":" ^ jsonStr rulesF ^
      ",\"asserted\":" ^ jsonStr assertedF ^
      ",\"certificate\":" ^ jsonStr certF ^
      ",\"strict\":" ^ jsonStr (outcomeStr strict) ^
      ",\"lenient\":" ^ jsonStr (outcomeStr lenient) ^
      ",\"exit\":" ^ Int.toString (exitCode strict)
    val body = case strict of
        OOHorn.Ok v =>
          ",\"ok\":true,\"verdict\":" ^ jsonStr (verdictStr v) ^
          ",\"theorem\":" ^ jsonStr (theoremOf v) ^
          ",\"means\":" ^ jsonStr (meansOf v)
      | OOHorn.Rejected (j,r) =>
          ",\"ok\":false,\"step\":" ^ Int.toString (natToInt j) ^
          ",\"reason\":" ^ jsonStr (reasonStr r)
      | OOHorn.ParseError => ",\"ok\":false,\"error\":\"parse\""
  in head ^ body ^ "}" end;

fun runOne rulesF assertedF certF =
  let
    val R = rows (readFile rulesF)
    val G = rows (readFile assertedF)
    val C = rows (readFile certF)
    val strict  = OOHorn.run_check R G C
    val lenient = OOHorn.run_check_lenient R G C
  in
    (reportJson rulesF assertedF certF strict lenient, exitCode strict)
  end
  handle ReadError p =>
    (* An unreadable file is exit 2, the same as an unparseable one and the same as the
       Lean side.  It must never look like a rejection: exit 1 says a step was checked
       and found wanting, and nothing was checked here. *)
    ("{\"checker\":\"isabelle-OOHorn\",\"ok\":false,\"error\":\"read\",\"path\":" ^
     jsonStr p ^ ",\"exit\":2}", 2);

(* OS.Process.exit only offers success and failure, so exact exit codes go through
   Posix.Process.exit. *)
fun exitWith 0 = OS.Process.exit OS.Process.success
  | exitWith n = Posix.Process.exit (Word8.fromInt n);

fun checkMode r a c =
  let val (json, code) = runOne r a c
  in
    print (json ^ "\n");
    if code = 2 then TextIO.output (TextIO.stdErr, "cannot read or parse one of the inputs\n")
    else ();
    exitWith code
  end;

fun batchMode manifest =
  let
    val text = readFile manifest
    val lines = List.filter (fn l => l <> "") (splitOn #"\n" text)
    fun one line =
      case splitOn #"\t" line of
        [r,a,c] => print (#1 (runOne r a c) ^ "\n")
      | _ => print ("{\"checker\":\"isabelle-OOHorn\",\"ok\":false,\"error\":\"manifest\"," ^
                    "\"line\":" ^ jsonStr line ^ ",\"exit\":3}\n")
  in
    List.app one lines;
    exitWith 0
  end
  handle ReadError p =>
    (TextIO.output (TextIO.stdErr, "cannot read manifest " ^ p ^ "\n"); exitWith 2);

(* Is this file the table embedded in OO_Check.thy?  verdict_of answers by equality
   against builtin_table, so `entailed` here means the bytes ARE the embedded table. *)
fun tableMode rulesF =
  let val R = rows (readFile rulesF)
  in
    case OOHorn.parse_rules R of
      NONE => (print "{\"checker\":\"isabelle-OOHorn\",\"ok\":false,\"error\":\"parse\"}\n";
               exitWith 2)
    | SOME rs =>
        (print ("{\"checker\":\"isabelle-OOHorn\",\"table_verdict\":" ^
                jsonStr (verdictStr (OOHorn.verdict_of rs)) ^ "}\n");
         exitWith 0)
  end
  handle ReadError p =>
    (TextIO.output (TextIO.stdErr, "cannot read " ^ p ^ "\n"); exitWith 2);

fun usage () =
  (TextIO.output (TextIO.stdErr,
     "usage: oo-horn-isabelle check RULES.tsv ASSERTED.tsv CERT.tsv\n\
     \       oo-horn-isabelle batch MANIFEST.tsv\n\
     \       oo-horn-isabelle table RULES.tsv\n");
   exitWith 2);

fun main () =
  case CommandLine.arguments () of
     ["check", r, a, c] => checkMode r a c
   | [r, a, c]          => checkMode r a c      (* the shape run_checker.sh already uses *)
   | ["batch", m]       => batchMode m
   | ["table", r]       => tableMode r
   | _                  => usage ();
