import OOCert.Rules

/-!
# Certificate files

Two tab-separated files, both written by the engine's interner so that a term
is spelled identically wherever it appears. Tabs and newlines cannot occur
inside an N-Triples term (they are escaped), so splitting on them is exact.

* `asserted.tsv`: one triple per line, `s TAB p TAB o`.
* `derivations.tsv`: one step per line,
  `rule TAB s TAB p TAB o [TAB ps TAB pp TAB po]*`, conclusion first, then
  the premises in the order `Rules.lean` documents.

This module is not part of the proof. A parse error is a rejected certificate,
never an accepted one.
-/
namespace OOCert.Parse

def tripleOf? : List String → Option Triple
  | [s, p, o] => some ⟨s, p, o⟩
  | _ => none

def groupTriples : List String → Option (List Triple)
  | [] => some []
  | s :: p :: o :: rest => (groupTriples rest).map (⟨s, p, o⟩ :: ·)
  | _ => none

def parseTriples (content : String) : Except String (List Triple) := do
  let mut out : Array Triple := #[]
  let mut n := 0
  for line in content.splitOn "\n" do
    n := n + 1
    if line.isEmpty then continue
    match tripleOf? (line.splitOn "\t") with
    | some t => out := out.push t
    | none => throw s!"asserted.tsv line {n}: expected three tab-separated terms"
  return out.toList

def parseSteps (content : String) : Except String (List Step) := do
  let mut out : Array Step := #[]
  let mut n := 0
  for line in content.splitOn "\n" do
    n := n + 1
    if line.isEmpty then continue
    match line.splitOn "\t" with
    | rule :: s :: p :: o :: prem =>
      match Rule.ofName? rule, groupTriples prem with
      | some r, some ps => out := out.push ⟨r, ps, ⟨s, p, o⟩⟩
      | none, _ => throw s!"derivations.tsv line {n}: unknown rule '{rule}'"
      | _, none => throw s!"derivations.tsv line {n}: premises are not whole triples"
    | _ => throw s!"derivations.tsv line {n}: expected rule, conclusion, premises"
  return out.toList

end OOCert.Parse
