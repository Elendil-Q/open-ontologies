import OOCert.Horn
import OOCert.HornBuiltin
import OOCert.Parse

/-!
# A file format for rule sets and Horn certificates

Not part of any proof. A parse error is a rejected certificate, never an
accepted one, exactly as `Parse.lean` says of the built-in format.

* `rules.tsv`: `name TAB bodyLength TAB (s TAB p TAB o)* TAB hs TAB hp TAB ho`.
  A field beginning with `?` is a variable; anything else is a term in its
  N-Triples spelling. N-Triples terms begin with `<`, `_:` or `"`, so the
  encoding is unambiguous.
* `horn.tsv`: `ruleIndex TAB bindCount TAB (var TAB term)* TAB cs TAB cp TAB co
  TAB (ps TAB pp TAB po)*`.
-/
namespace OOCert.HornParse

def patOf (s : String) : Pat :=
  if s.startsWith "?" then .var (s.drop 1).toString else .const s

def patStr : Pat → String
  | .const c => c
  | .var v => "?" ++ v

def ruleStr (r : RulePattern) : String :=
  String.intercalate "\t"
    ([r.name, toString r.body.length] ++
     (r.body.map (fun a => [patStr a.s, patStr a.p, patStr a.o])).flatten ++
     [patStr r.head.s, patStr r.head.p, patStr r.head.o])

def groupAtoms : List String → Option (List AtomPat)
  | [] => some []
  | s :: p :: o :: rest => (groupAtoms rest).map (⟨patOf s, patOf p, patOf o⟩ :: ·)
  | _ => none

def groupPairs : List String → Option (List (Var × Term))
  | [] => some []
  | v :: t :: rest => (groupPairs rest).map ((v, t) :: ·)
  | _ => none

def parseRules (content : String) : Except String (List RulePattern) := do
  let mut out : Array RulePattern := #[]
  let mut n := 0
  for line in content.splitOn "\n" do
    n := n + 1
    if line.isEmpty then continue
    match line.splitOn "\t" with
    | name :: k :: rest =>
      match k.toNat? with
      | none => throw s!"rules line {n}: body length is not a number"
      | some m =>
        if rest.length ≠ 3 * m + 3 then
          throw s!"rules line {n}: expected {3 * m + 3} pattern fields, got {rest.length}"
        else
          match groupAtoms (rest.take (3 * m)), groupAtoms (rest.drop (3 * m)) with
          | some body, some [head] => out := out.push ⟨name, body, head⟩
          | _, _ => throw s!"rules line {n}: malformed patterns"
    | _ => throw s!"rules line {n}: expected name, body length, patterns"
  return out.toList

def parseHornSteps (content : String) : Except String (List HornStep) := do
  let mut out : Array HornStep := #[]
  let mut n := 0
  for line in content.splitOn "\n" do
    n := n + 1
    if line.isEmpty then continue
    match line.splitOn "\t" with
    | idx :: nb :: rest =>
      match idx.toNat?, nb.toNat? with
      | some i, some k =>
        match groupPairs (rest.take (2 * k)), rest.drop (2 * k) with
        | some binds, cs :: cp :: co :: prem =>
          match Parse.groupTriples prem with
          | some ps => out := out.push ⟨i, binds, ps, ⟨cs, cp, co⟩⟩
          | none => throw s!"horn line {n}: premises are not whole triples"
        | _, _ => throw s!"horn line {n}: malformed bindings or conclusion"
      | _, _ => throw s!"horn line {n}: rule index or bind count is not a number"
    | _ => throw s!"horn line {n}: expected index, bind count, bindings, conclusion"
  return out.toList

end OOCert.HornParse
