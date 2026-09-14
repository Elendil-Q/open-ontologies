import Dl.Check
import Std.Data.HashMap

/-!
# Reading the two files

`Dl/Syntax.lean` documents the format. This module turns the bytes into the `Axiom` list and
the `Interp` the checker is proved about.

It is NOT part of the theorem. A parse error is exit 2, never an accepted certificate, and
never a rejected one either: "I could not read the file" and "this is not a model" are
different answers and the exit codes keep them apart.

The three extension maps are built as hash tables and handed to `Interp` as closures over
them, so an atomic concept lookup costs one hash rather than a scan of the file. That is a
representation choice inside the parser; `Dl/Semantics.lean` only ever sees the functions.
-/
namespace Dl.Parse

/-- Split on spaces, dropping empties. IRIs keep their `<...>` spelling and contain no
space, so this is exact for the token streams the emitter writes. -/
def tokens (s : String) : List String :=
  (s.splitOn " ").filter (fun t => !t.isEmpty)

/-- Prefix parser for a concept. Every constructor has a fixed arity, so no parentheses are
needed and the grammar is unambiguous. The fuel is the token count, which strictly bounds
the recursion because each step consumes at least one token. -/
def concept? : Nat → List String → Option (Concept × List String)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: ts =>
    match t with
    | "top" => some (.top, ts)
    | "bot" => some (.bot, ts)
    | "atom" => match ts with
      | a :: ts' => some (.atom a, ts')
      | [] => none
    | "not" => (concept? fuel ts).map (fun p => (.neg p.1, p.2))
    | "and" => do
        let (c, ts1) ← concept? fuel ts
        let (d, ts2) ← concept? fuel ts1
        some (.and c d, ts2)
    | "or" => do
        let (c, ts1) ← concept? fuel ts
        let (d, ts2) ← concept? fuel ts1
        some (.or c d, ts2)
    | "some" => match ts with
      | r :: ts' => (concept? fuel ts').map (fun p => (.ex r p.1, p.2))
      | [] => none
    | "all" => match ts with
      | r :: ts' => (concept? fuel ts').map (fun p => (.all r p.1, p.2))
      | [] => none
    | "min" => match ts with
      | n :: r :: ts' => do
          let k ← n.toNat?
          let (c, ts2) ← concept? fuel ts'
          some (.min k r c, ts2)
      | _ => none
    | "max" => match ts with
      | n :: r :: ts' => do
          let k ← n.toNat?
          let (c, ts2) ← concept? fuel ts'
          some (.max k r c, ts2)
      | _ => none
    | _ => none

/-- A whole field must be exactly one concept, with nothing left over. -/
def parseConcept (s : String) : Option Concept :=
  let ts := tokens s
  match concept? (ts.length + 1) ts with
  | some (c, []) => some c
  | _ => none

def parseAxiomLine (line : String) : Option Axiom :=
  match line.splitOn "\t" with
  | ["sub", c, d] => do some (.sub (← parseConcept c) (← parseConcept d))
  | ["disjoint", c, d] => do some (.disjoint (← parseConcept c) (← parseConcept d))
  | ["domain", r, c] => do some (.dom r (← parseConcept c))
  | ["range", r, c] => do some (.rng r (← parseConcept c))
  | ["subrole", r, s] => some (.subrole r s)
  | ["trans", r] => some (.trans r)
  | ["sym", r] => some (.sym r)
  | ["inv", r, s] => some (.inv r s)
  | ["invfunc", r] => some (.invfunc r)
  | ["inst", a, c] => do some (.inst a (← parseConcept c))
  | ["rel", a, r, b] => some (.rel a r b)
  | ["indiv", a] => some (.indiv a)
  | ["nonempty", c] => do some (.nonempty (← parseConcept c))
  | _ => none

def parseAxioms (content : String) : Except String (List Axiom) := do
  let mut out : Array Axiom := #[]
  let mut n := 0
  for line in (content.replace "\r\n" "\n").splitOn "\n" do
    n := n + 1
    if line.isEmpty then continue
    match parseAxiomLine line with
    | some a => out := out.push a
    | none => throw s!"axioms line {n}: not a well-formed axiom"
  return out.toList

/-- The lookup tables an `Interp` closes over. -/
structure Tables where
  dom : Array Name := #[]
  cmap : Std.HashMap Name (List Name) := ∅
  rmap : Std.HashMap (Name × Name) (List Name) := ∅
  imap : Std.HashMap Name Name := ∅

/-- An individual with no `ind` line denotes the empty name, which is in no domain, so the
`indiv` axiom and the `indInDom` clause of `WellFormed` both fail rather than succeed by
accident. Silence is never taken for agreement. -/
def Tables.toInterp (t : Tables) : Interp where
  dom := t.dom.toList
  cext := fun a => t.cmap.getD a []
  rext := fun r x => t.rmap.getD (r, x) []
  ind := fun a => t.imap.getD a ""

def parseModel (content : String) : Except String Interp := do
  let mut t : Tables := {}
  let mut n := 0
  for line in (content.replace "\r\n" "\n").splitOn "\n" do
    n := n + 1
    if line.isEmpty then continue
    match line.splitOn "\t" with
    | ["domain", e] => t := { t with dom := t.dom.push e }
    | ["class", c, e] => t := { t with cmap := t.cmap.insert c (e :: t.cmap.getD c []) }
    | ["edge", x, r, y] => t := { t with rmap := t.rmap.insert (r, x) (y :: t.rmap.getD (r, x) []) }
    | ["ind", a, e] => t := { t with imap := t.imap.insert a e }
    | _ => throw s!"model line {n}: not a well-formed model fact"
  return t.toInterp

end Dl.Parse
