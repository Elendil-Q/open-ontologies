import Fol.Witness
import Std.Data.HashMap

/-!
# Reading the two files, and binding them to each other

`Fol/Syntax.lean` documents the formats. This module turns the bytes into the `Form` list and the
`FinModel` the checker is proved about, and recomputes the digest that ties the second file to the
first.

It is NOT part of the theorem. A parse error is exit 2, never an accepted certificate and never a
rejected one either: "I could not read the file" and "this is not a model" are different answers
and the exit codes keep them apart. The same rule as `lean/Dl/Parse.lean`, for the same reason.

## Why the parser is stricter than soundness needs

`FinModel`'s three fields are total, so every symbol has an interpretation whether the file
mentioned it or not, and `check` validates whatever structure comes out from scratch. Soundness
therefore survives any amount of silent defaulting. Attribution does not. A model file missing a
row certifies a DIFFERENT OBJECT from the one the solver produced, and a report that says "the
solver's model was checked" would then be false while the theorem stayed true. That is the
mis-attribution shape this project exists to catch, so every route to it is closed here:

* a declared symbol with no row is exit 2, so the defaults are never exercised through this
  parser at all;
* a row for a symbol that was never declared is exit 2, so the `decl` lines really are the
  signature of the model rather than a hint;
* a second row for the same slot is exit 2, rather than one of the two silently winning;
* a symbol declared at two arities is exit 2, which is the file-level half of G3.3;
* a row whose length is not the declared carrier size, and an index outside it, are exit 2. The
  `Fin` bound is checked HERE, at the boundary, with `if h : i < n + 1 then .ok ⟨i, h⟩`, so nothing
  downstream can hold an out-of-range element.

## The digest

`problemDigest` is computed over the CANONICAL RE-SERIALISATION of the parsed problem, not over
the file bytes: the lines `ROLE <TAB> showForm f` in file order, joined with newlines, hashed with
FNV-1a 64 and printed as 16 lowercase hex digits. Labels are excluded because they are diagnostic.
Spacing is normalised because `showForm` writes single spaces whatever the input had. The role is
included because it is what a report reads to decide whether a non-entailment was even asked
about, and a file whose `goal_negated` had been relabelled `axiom` would otherwise digest the
same.

There is exactly ONE printer, and the driver's diagnostic line uses it too, so the digest and the
error message cannot disagree about what a formula says.

**It identifies, it does not commit.** FNV-1a is not a cryptographic hash and the algorithm is
written out so that two independent implementations can agree, not so that one can be defended
against someone who controls the file. The mismatch message prints the digest the checker
computed, which gives away nothing that was not already computable from `problem.tsv` by anyone
holding it. Anyone needing a commitment should hash the file with something built for that. This
is decision 0003 item 5, in the same words, for the same reason.
-/
namespace Fol.Parse

/-! ## The canonical printer -/

def showTerm : Term → String
  | .var k => "var " ++ toString k
  | .const c => "const " ++ c

def showForm : Form → String
  | .app1 p t => "app1 " ++ p ++ " " ++ showTerm t
  | .app2 p t u => "app2 " ++ p ++ " " ++ showTerm t ++ " " ++ showTerm u
  | .eq t u => "eq " ++ showTerm t ++ " " ++ showTerm u
  | .tru => "tru"
  | .fls => "fls"
  | .neg f => "neg " ++ showForm f
  | .and f g => "and " ++ showForm f ++ " " ++ showForm g
  | .or f g => "or " ++ showForm f ++ " " ++ showForm g
  | .imp f g => "imp " ++ showForm f ++ " " ++ showForm g
  | .all k f => "all " ++ toString k ++ " " ++ showForm f
  | .ex k f => "ex " ++ toString k ++ " " ++ showForm f

/-! ## The digest -/

/-- FNV-1a, 64 bit, over the UTF-8 bytes. Offset basis 14695981039346656037, prime
1099511628211, `UInt64` arithmetic wrapping at 2^64. Written out rather than taken from a library
so that the Rust writer can reproduce it exactly; `String.hash` would not do, being an opaque
extern with no specification a second implementation could target. -/
def fnv1a64 (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Sixteen lowercase hex digits, most significant first, zero padded. -/
def hex16 (x : UInt64) : String :=
  let n := x.toNat
  (List.range 16).foldl (fun acc i => acc.push (hexDigit ((n / (16 ^ (15 - i))) % 16))) ""

/-! ## `problem.tsv` -/

/-- One line of `problem.tsv`. `label` is diagnostic and is not digested. -/
structure Entry where
  role : String
  label : String
  form : Form
deriving Repr, Inhabited

def canonical (es : List Entry) : String :=
  String.intercalate "\n" (es.map (fun e => e.role ++ "\t" ++ showForm e.form))

def problemDigest (es : List Entry) : String := hex16 (fnv1a64 (canonical es))

/-- Split on spaces, dropping empties. A symbol contains no space, because the writer in
`src/tptp.rs` refuses to emit one that does, so this is exact for the token streams it writes. A
symbol that slipped through with a space in it would split here into two tokens and either fail to
parse or parse into a DIFFERENT formula, and the digest is what catches the second case. -/
def tokens (s : String) : List String :=
  (s.splitOn " ").filter (fun t => !t.isEmpty)

def term? : List String → Option (Term × List String)
  | "var" :: n :: ts => (n.toNat?).map (fun k => (Term.var k, ts))
  | "const" :: c :: ts => some (.const c, ts)
  | _ => none

/-- Prefix parser for a formula. Every constructor has a fixed arity, so no parentheses are needed
and the grammar is unambiguous. The fuel is the token count, which strictly bounds the recursion
because each step consumes at least one token. -/
def form? : Nat → List String → Option (Form × List String)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: ts =>
    match t with
    | "tru" => some (.tru, ts)
    | "fls" => some (.fls, ts)
    | "app1" => match ts with
      | p :: ts' => do
          let (a, ts2) ← term? ts'
          some (.app1 p a, ts2)
      | [] => none
    | "app2" => match ts with
      | p :: ts' => do
          let (a, ts1) ← term? ts'
          let (b, ts2) ← term? ts1
          some (.app2 p a b, ts2)
      | [] => none
    | "eq" => do
        let (a, ts1) ← term? ts
        let (b, ts2) ← term? ts1
        some (.eq a b, ts2)
    | "neg" => (form? fuel ts).map (fun p => (.neg p.1, p.2))
    | "and" => do
        let (f, ts1) ← form? fuel ts
        let (g, ts2) ← form? fuel ts1
        some (.and f g, ts2)
    | "or" => do
        let (f, ts1) ← form? fuel ts
        let (g, ts2) ← form? fuel ts1
        some (.or f g, ts2)
    | "imp" => do
        let (f, ts1) ← form? fuel ts
        let (g, ts2) ← form? fuel ts1
        some (.imp f g, ts2)
    | "all" => match ts with
      | n :: ts' => do
          let k ← n.toNat?
          let (f, ts2) ← form? fuel ts'
          some (.all k f, ts2)
      | [] => none
    | "ex" => match ts with
      | n :: ts' => do
          let k ← n.toNat?
          let (f, ts2) ← form? fuel ts'
          some (.ex k f, ts2)
      | [] => none
    | _ => none

/-- A whole field must be exactly one formula, with nothing left over. -/
def parseForm (s : String) : Option Form :=
  let ts := tokens s
  match form? (ts.length + 1) ts with
  | some (f, []) => some f
  | _ => none

/-- Read `problem.tsv`.

An EMPTY formula list is refused. Every structure satisfies the empty list, so a certificate over
one would report `model_checked` and say nothing at all; an exporter bug that dropped every
formula would otherwise produce a clean green run, which is precisely the assurance-laundering
shape decision 0005 section 7 records happening inside this repository already. -/
def parseProblem (content : String) : Except String (List Entry) := do
  let mut out : Array Entry := #[]
  let mut n := 0
  for line in (content.replace "\r\n" "\n").splitOn "\n" do
    n := n + 1
    if line.isEmpty then continue
    match line.splitOn "\t" with
    | [role, label, f] =>
      if role != "axiom" && role != "goal_negated" then
        throw s!"problem line {n}: the role must be axiom or goal_negated, not {role}"
      match parseForm f with
      | some form => out := out.push { role := role, label := label, form := form }
      | none => throw s!"problem line {n}: not a well-formed formula"
    | _ => throw s!"problem line {n}: expected three tab-separated fields"
  if out.isEmpty then
    throw "the problem carries no formulas; every structure satisfies an empty problem, so a certificate over one would say nothing"
  return out.toList

/-! ## `model.tsv` -/

/-- The header of a model file: everything that is not a table row. -/
structure Header where
  d1 : Array Sym := #[]
  d2 : Array Sym := #[]
  dc : Array Sym := #[]
  card : Option Nat := none
  digest : Option String := none
  source : String := "hand"
  search : String := ""
deriving Inhabited

/-- Pass one. Reads the declarations, so row order and declaration order are both irrelevant. -/
def readHeader (lines : List String) : Except String Header := do
  let mut h : Header := {}
  let mut n := 0
  for line in lines do
    n := n + 1
    if line.isEmpty then continue
    match line.splitOn "\t" with
    | ["domain", k] =>
      if h.card.isSome then throw s!"model line {n}: a second domain line"
      match k.toNat? with
      | none => throw s!"model line {n}: {k} is not a carrier size"
      | some c => h := { h with card := some c }
    | ["problem", d] =>
      if h.digest.isSome then throw s!"model line {n}: a second problem digest"
      h := { h with digest := some d }
    | ["source", s] => h := { h with source := s }
    | ["cardinality_search", s] => h := { h with search := s }
    | ["decl1", s] =>
      if h.d1.contains s then throw s!"model line {n}: {s} is declared unary twice"
      if h.d2.contains s then throw s!"model line {n}: {s} is declared at two arities"
      h := { h with d1 := h.d1.push s }
    | ["decl2", s] =>
      if h.d2.contains s then throw s!"model line {n}: {s} is declared binary twice"
      if h.d1.contains s then throw s!"model line {n}: {s} is declared at two arities"
      h := { h with d2 := h.d2.push s }
    | ["declc", s] =>
      if h.dc.contains s then throw s!"model line {n}: {s} is declared a constant twice"
      h := { h with dc := h.dc.push s }
    | ["p1", _, _] => pure ()
    | ["p2", _, _, _] => pure ()
    | ["const", _, _] => pure ()
    | _ => throw s!"model line {n}: not a well-formed model line"
  return h

/-- The lookup tables a `FinModel` closes over. Hash tables rather than association lists, so a
symbol lookup costs one hash rather than a scan of the file; that is a representation choice
inside the parser and `Fol/Semantics.lean` only ever sees the functions. -/
structure Tables (n : Nat) where
  u : Std.HashMap Sym (Array Bool) := ∅
  b : Std.HashMap (Sym × Nat) (Array Bool) := ∅
  k : Std.HashMap Sym (Fin n) := ∅

def Tables.toModel {n : Nat} (t : Tables (n+1)) : FinModel (n+1) where
  p1 := fun p x => (t.u.getD p #[]).getD x.val false
  p2 := fun r x y => (t.b.getD (r, x.val) #[]).getD y.val false
  const := fun c => t.k.getD c 0

/-- A bit row of exactly `n` characters, each `0` or `1`. -/
def bits (n : Nat) (s : String) : Except String (Array Bool) := do
  let cs := s.toList
  if cs.length != n then
    throw s!"a table row has {cs.length} bits, the declared carrier is {n}"
  let mut out : Array Bool := #[]
  for c in cs do
    if c == '1' then out := out.push true
    else if c == '0' then out := out.push false
    else throw s!"a table row contains {c}, which is neither 0 nor 1"
  return out

/-- An index inside the declared carrier. -/
def idx (n : Nat) (s : String) : Except String (Fin (n+1)) :=
  match s.toNat? with
  | none => throw s!"{s} is not a carrier index"
  | some i =>
    if h : i < n + 1 then .ok ⟨i, h⟩
    else throw s!"index {i} is outside the declared carrier of {n+1}"

/-- The result of reading `model.tsv`. The carrier size is DATA, so the boundary carries it. -/
structure ParsedModel where
  n : Nat
  model : FinModel (n+1)
  decl1 : List Sym
  decl2 : List Sym
  declc : List Sym
  digest : String
  source : String
  search : String

def parseModel (content : String) : Except String ParsedModel := do
  let lines := (content.replace "\r\n" "\n").splitOn "\n"
  let h ← readHeader lines
  let digest ← match h.digest with
    | none => throw "the model carries no problem digest, so nothing binds it to a problem"
    | some d => pure d
  match h.card with
  | none => throw "the model declares no carrier size"
  | some 0 =>
      throw "the model declares an empty carrier; a first-order structure cannot have one"
  | some (n+1) =>
    let mut t : Tables (n+1) := {}
    let mut ln := 0
    for line in lines do
      ln := ln + 1
      if line.isEmpty then continue
      match line.splitOn "\t" with
      | ["p1", s, row] =>
          if !h.d1.contains s then
            throw s!"model line {ln}: a unary row for {s}, which is not declared unary"
          if t.u.contains s then throw s!"model line {ln}: a second unary row for {s}"
          t := { t with u := t.u.insert s (← bits (n+1) row) }
      | ["p2", s, i, row] =>
          if !h.d2.contains s then
            throw s!"model line {ln}: a binary row for {s}, which is not declared binary"
          let j ← idx n i
          if t.b.contains (s, j.val) then
            throw s!"model line {ln}: a second binary row for {s} at {j.val}"
          t := { t with b := t.b.insert (s, j.val) (← bits (n+1) row) }
      | ["const", s, i] =>
          if !h.dc.contains s then
            throw s!"model line {ln}: a denotation for {s}, which is not declared a constant"
          if t.k.contains s then throw s!"model line {ln}: a second denotation for {s}"
          let j ← idx n i
          t := { t with k := t.k.insert s j }
      | _ => pure ()
    -- Completeness. Without these the totality of `FinModel` would quietly fill the gaps and the
    -- object certified would not be the object the file describes.
    for s in h.d1 do
      if !t.u.contains s then throw s!"{s} is declared unary and has no row"
    for s in h.d2 do
      for i in [0:n+1] do
        if !t.b.contains (s, i) then throw s!"{s} is declared binary and has no row {i}"
    for s in h.dc do
      if !t.k.contains s then throw s!"{s} is declared a constant and has no denotation"
    return { n := n, model := t.toModel, decl1 := h.d1.toList, decl2 := h.d2.toList,
             declc := h.dc.toList, digest := digest, source := h.source, search := h.search }

/-! ## The worked example, pinned

`Fol/Syntax.lean` documents the format with a worked example and quotes its digest. That digest is
the value measured below, so a change to `showForm`, to `canonical` or to the hash fails the build
here rather than drifting silently away from the format the Rust writer has to target.

`#guard` evaluates at elaboration time and proves nothing: this is boundary machinery, outside the
theorem, exactly like the rest of this file. What it buys is that the documented format and the
implemented one cannot come apart without somebody noticing. -/

private def workedProblem : String :=
  "axiom\tbackground_1\tall 0 neg and app1 thing var 0 app1 lit var 0\n" ++
  "axiom\tind_typing_1\tapp1 thing const i:a\n" ++
  "axiom\towl_1_subClassOf\tall 0 imp app1 c:Person var 0 ex 1 and app2 op:worksFor var 0 var 1 app1 c:Company var 1\n" ++
  "axiom\towl_2_classAssertion\tapp1 c:Person const i:a\n" ++
  "goal_negated\tgoal_classAssertion\tneg app1 c:Company const i:a\n"

#guard (parseProblem workedProblem).toOption.map problemDigest == some "4403d8aaa0c422f7"

/-! And the round trip: the canonical printer and the parser agree, so a problem file written by
the Rust `checkfmt` printer and read back here is the same formula list. Whitespace in the input
is normalised away by `showForm`, which is why the digest is taken over this rather than over the
bytes. -/
#guard ((parseProblem workedProblem).toOption.map (fun es =>
  es.all (fun e => parseForm (showForm e.form) == some e.form))) == some true

end Fol.Parse
