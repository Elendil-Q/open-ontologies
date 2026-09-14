import Shacl.Term

/-!
# Reading N-Triples

Not part of any theorem. A parse error is a refusal, never a verdict, and
`ShaclMain.lean` exits with the code reserved for "a file could not be read".

N-Triples rather than Turtle because Turtle needs prefix resolution, base
resolution and a real grammar, and every one of those is a place to be subtly
wrong about which term a shape mentions. The bridge in
`tests/shacl_core_verified_test.rs` hands this module N-Triples produced by the
engine's own parser with an explicit base IRI, so relative IRIs are already
resolved and literals are already in one canonical spelling. That moves the hard
part of reading RDF out of this development and into a component that is measured
elsewhere, and it says so rather than pretending the whole path is verified.

What is accepted: one triple per line, terms separated by whitespace, a trailing
`.`, blank lines and `#` comments. Literals may carry `^^<datatype>` or `@lang`.
Escapes inside a literal are preserved exactly as written, never decoded, which is
the term model `Shacl/Term.lean` documents.
-/
namespace Shacl.Parse

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'

def skipWs : List Char → List Char
  | [] => []
  | c :: rest => if isWs c then skipWs rest else c :: rest

/-- Characters up to the first `stop`, and what follows it. -/
def takeUntil (stop : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
      if c == stop then some ([], rest)
      else (takeUntil stop rest).map fun p => (c :: p.1, p.2)

def takeWhile (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
      if p c then
        let (a, b) := takeWhile p rest
        (c :: a, b)
      else ([], c :: rest)

def isLangChar (c : Char) : Bool := c.isAlpha || c.isDigit || c == '-'

/-- Read one term and return it in the canonical N-Triples spelling this
development uses everywhere else. -/
def readTerm (cs : List Char) : Option (Term × List Char) :=
  match skipWs cs with
  | '<' :: rest =>
      match takeUntil '>' rest with
      | some (body, tail) => some (String.ofList ('<' :: body ++ ['>']), tail)
      | none => none
  | '_' :: ':' :: rest =>
      let (label, tail) := takeWhile (fun c => !isWs c && c != '.') rest
      if label.isEmpty then none else some (String.ofList ('_' :: ':' :: label), tail)
  | '"' :: rest =>
      match splitLex rest with
      | none => none
      | some (lex, tail) =>
        match tail with
        | '^' :: '^' :: '<' :: dtRest =>
            match takeUntil '>' dtRest with
            | some (dt, tail2) =>
                some (String.ofList ('"' :: lex ++ '"' :: '^' :: '^' :: '<' :: dt ++ ['>']), tail2)
            | none => none
        | '@' :: langRest =>
            let (tag, tail2) := takeWhile isLangChar langRest
            if tag.isEmpty then none
            else some (String.ofList ('"' :: lex ++ '"' :: '@' :: tag), tail2)
        | _ => some (String.ofList ('"' :: lex ++ ['"']), tail)
  | _ => none

def parseLine (n : Nat) (cs : List Char) : Except String (Option Triple) :=
  match skipWs cs with
  | [] => .ok none
  | '#' :: _ => .ok none
  | rest =>
    match readTerm rest with
    | none => .error s!"line {n}: could not read a subject"
    | some (s, r1) =>
      match readTerm r1 with
      | none => .error s!"line {n}: could not read a predicate"
      | some (p, r2) =>
        match readTerm r2 with
        | none => .error s!"line {n}: could not read an object"
        | some (o, r3) =>
          match skipWs r3 with
          | '.' :: _ => .ok (some ⟨s, p, o⟩)
          | _ => .error s!"line {n}: expected '.' after the object"

def parseNTriples (content : String) : Except String Graph := do
  let mut out : Array Triple := #[]
  let mut n := 0
  for line in content.splitOn "\n" do
    n := n + 1
    match ← parseLine n line.toList with
    | some t => out := out.push t
    | none => pure ()
  return out.toList

end Shacl.Parse
