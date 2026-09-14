(* oo_horn_driver.sml -- the UNTRUSTED driver.  NO THEOREM COVERS THIS FILE.

   It does file IO, splits bytes on LF and TAB, converts bytes to and from the verified
   core's char type, prints a report, and chooses an exit code.  Splitting is the only
   logic in it, and it is four lines -- which is possible only because the format has no
   escaping layer: an N-Triples spelling cannot contain a raw TAB or LF, so nothing has
   to be unescaped and no real logic is pushed outside the theorem.

   Note it uses SML's OWN String.explode on a native byte string, not Isabelle's. *)

fun toChar c = OOHorn.chr_of_nat (OOHorn.nat_of_integer (IntInf.fromInt (Char.ord c)));
fun toStr s  = List.map toChar (String.explode s);
fun fromChar c = Char.chr (IntInf.toInt (OOHorn.integer_of_nat (OOHorn.nat_of_chr c)));
fun fromStr cs = String.implode (List.map fromChar cs);
fun natToInt n = IntInf.toInt (OOHorn.integer_of_nat n);

fun readFile path =
  let val s = TextIO.openIn path
      val d = TextIO.inputAll s
  in TextIO.closeIn s; d end;

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

fun report rulesF assertedF certF =
  let
    val R = rows (readFile rulesF)
    val G = rows (readFile assertedF)
    val C = rows (readFile certF)
    val strict  = OOHorn.run_check R G C
    val lenient = OOHorn.run_check_lenient R G C
  in
    print ("{\"rules\":\"" ^ rulesF ^
           "\",\"asserted\":\"" ^ assertedF ^
           "\",\"certificate\":\"" ^ certF ^
           "\",\"strict\":\"" ^ outcomeStr strict ^
           "\",\"lenient\":\"" ^ outcomeStr lenient ^
           "\",\"checker\":\"isabelle-OOHorn\"" ^
           ",\"absolute_theorem\":\"OOHorn.run_check_entailed_sound\"" ^
           ",\"conditional_theorem\":\"OOHorn.run_check_sound\"}\n");
    exitCode strict
  end;

(* OS.Process.exit only offers success and failure, so exact exit codes go through
   Posix.Process.exit. *)
fun exitWith 0 = OS.Process.exit OS.Process.success
  | exitWith n = Posix.Process.exit (Word8.fromInt n);

fun getEnv k = case OS.Process.getEnv k of SOME v => v | NONE => "";

fun mainEnv () =
  let
    val r = getEnv "OO_RULES"
    val a = getEnv "OO_ASSERTED"
    val c = getEnv "OO_CERT"
  in
    if r = "" orelse a = "" orelse c = ""
    then (print "usage: set OO_RULES, OO_ASSERTED and OO_CERT\n"; exitWith 3)
    else exitWith (report r a c)
  end;

fun main () =
  case CommandLine.arguments () of
     [r,a,c] => exitWith (report r a c)
   | _       => mainEnv ();
