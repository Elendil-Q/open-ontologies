/-!
# Terms, triples, and the one place a SHACL checker must look inside a term

A term is kept in its N-Triples spelling: `<iri>`, `_:label`, or a literal with
its quotes and its datatype or language tag. Two terms are the same term when
their spellings are the same string. That is the convention `lean/OOCert/Triple.lean`
uses for the derivation checker, and the bridge in `ShaclMain.lean` reads the same
kind of file, so the two layers agree on what a term is.

`OOCert.Triple` is deliberately NOT imported here, for two reasons and the second
is the load-bearing one.

1. Build isolation. The two directories are developed independently and a broken
   edit in one should not take the other's proofs down with it.
2. **The discipline is different.** `OOCert/Triple.lean` says in its own header that
   "the checker never looks inside a term". A SHACL checker cannot honour that:
   `sh:datatype` and `sh:nodeKind` are questions ABOUT the spelling, and answering
   them means taking a literal apart. So this module does the one thing that one
   refuses to do, and it says so here rather than inheriting a promise it breaks.

## What this term model cannot express

Stated up front, because every limit below shows up as a wrong answer somewhere in
the W3C suite and it is better to name them than to discover them.

* **Two spellings of one value are two terms.** `"1"^^xsd:integer` and
  `"01"^^xsd:integer` denote the same integer and are distinct terms here, so
  `sh:hasValue`, `sh:in` and `sh:maxCount` count them separately. RDF itself is on
  this side of the line for term equality. SHACL's comparison constraints
  (`sh:lessThan`, `sh:minInclusive`) are value-based, so they do NOT go through
  term equality: they go through `cmpTerms` below, which reads a value out of the
  spelling for the datatypes it knows and declines for the rest.
* **Escapes are not normalised.** `"aAb"` and `"aAb"` are one value and two
  terms. Nothing here unescapes a lexical form.
* **IRIs are not normalised.** No percent-decoding, no case folding of the scheme,
  no relative-IRI resolution. The bridge resolves relative IRIs before the term
  reaches Lean, so what arrives is already absolute; that resolution is outside
  the proof.
* **Blank node labels are constants.** Two graphs that are isomorphic but use
  different labels are different graphs here. SHACL conformance is not affected by
  blank node identity in the fragment covered, but a validation RESULT naming a
  blank node is only meaningful relative to the file it was read from.
* **Language tags are compared as written, apart from ASCII case.** BCP 47 says
  `EN` and `en` are the same tag, and `langMatches` below folds ASCII case for
  exactly that reason. It does not do anything else BCP 47 asks for: no canonical
  form, no extlang collapsing, no validity check on the subtag grammar.
* **A lexical form's LENGTH is not the value's length.** `"a\\nb"` is a three-character
  value written with four characters, because nothing here decodes an escape. So
  `strRep` below hands back the characters of a spelling only when that spelling
  carries NO backslash, and answers `unknown` when it does. `sh:minLength` and
  `sh:maxLength` are then right for every literal without an escape and refuse on
  the rest, rather than being silently wrong on the rest.
* **Lexical spaces are known for nine datatypes and no more.** See `lexOK`.
* **Value comparison is known for four families and no more.** See `cmpTerms`.
-/
namespace Shacl

/-- A term in N-Triples spelling. -/
abbrev Term := String

structure Triple where
  s : Term
  p : Term
  o : Term
deriving DecidableEq, Repr, Inhabited

/-- A graph is a list of triples. Duplicates are allowed and are ignored by
everything that matters: membership is what the specification asks about, never
multiplicity. -/
abbrev Graph := List Triple

/-! ## Vocabulary, in N-Triples spelling -/
namespace V

def type : Term := "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>"
def subClassOf : Term := "<http://www.w3.org/2000/01/rdf-schema#subClassOf>"
def first : Term := "<http://www.w3.org/1999/02/22-rdf-syntax-ns#first>"
def rest : Term := "<http://www.w3.org/1999/02/22-rdf-syntax-ns#rest>"
def nil : Term := "<http://www.w3.org/1999/02/22-rdf-syntax-ns#nil>"
def rdfsClass : Term := "<http://www.w3.org/2000/01/rdf-schema#Class>"
def langString : Term := "<http://www.w3.org/1999/02/22-rdf-syntax-ns#langString>"
def xsdString : Term := "<http://www.w3.org/2001/XMLSchema#string>"
def xsdBoolean : Term := "<http://www.w3.org/2001/XMLSchema#boolean>"
def xsdInteger : Term := "<http://www.w3.org/2001/XMLSchema#integer>"
def xsdByte : Term := "<http://www.w3.org/2001/XMLSchema#byte>"
def xsdDecimal : Term := "<http://www.w3.org/2001/XMLSchema#decimal>"
def xsdDate : Term := "<http://www.w3.org/2001/XMLSchema#date>"
def xsdDateTime : Term := "<http://www.w3.org/2001/XMLSchema#dateTime>"
def rdfHTML : Term := "<http://www.w3.org/1999/02/22-rdf-syntax-ns#HTML>"

end V

/-! ## Taking a term apart -/

/-- The three RDF node kinds. A spelling that is none of them is classified by
`kindOf` as `none`, which satisfies no `sh:nodeKind` value. Refusing to classify a
spelling this module does not recognise is the conservative direction: it can cost
a false violation, never a false pass. -/
inductive Kind where
  | iri
  | blank
  | lit
deriving DecidableEq, Repr

/-! Every predicate below takes the term apart as a `List Char` rather than with
`String.startsWith` and friends. That is not a style preference. `String` operations
are indexed by UTF-8 byte positions, and the Lean KERNEL cannot reduce that
arithmetic on a string it did not receive as a literal, so a witness like
`Shacl/Witness.lean`'s would stop being provable by computation the moment a term
was taken apart and put back together. Working in `List Char` keeps every fact about
a concrete term decidable in the kernel, with no `native_decide` anywhere. -/

def isIriSpelling (t : Term) : Bool :=
  match t.toList with
  | '<' :: rest => !rest.isEmpty && rest.getLast? == some '>'
  | _ => false

def isBlankSpelling (t : Term) : Bool :=
  match t.toList with
  | '_' :: ':' :: rest => !rest.isEmpty
  | _ => false

/-- A literal taken apart. `lex` is the lexical form still in its N-Triples
escaping; `dt` is the datatype IRI in `<...>` spelling, filled in with
`xsd:string` for a plain literal and `rdf:langString` for a language-tagged one,
exactly as RDF 1.1 requires. -/
structure Lit where
  lex : String
  dt : Term
  lang : Option String
deriving DecidableEq, Repr

/-- Split the characters after an opening quote at the first UNESCAPED `"`,
returning the lexical form and whatever follows the closing quote. A backslash
consumes the next character whatever it is, which is the N-Triples escaping rule,
so `"a\"b"` has the four-character lexical form `a\"b` and not the one-character
form `a`. -/
def splitLex : List Char → Option (List Char × List Char)
  | [] => none
  | '\\' :: c :: rest => (splitLex rest).map fun p => ('\\' :: c :: p.1, p.2)
  | '"' :: rest => some ([], rest)
  | c :: rest => (splitLex rest).map fun p => (c :: p.1, p.2)

/-- Read a term as a literal, or refuse. -/
def asLiteral (t : Term) : Option Lit :=
  match t.toList with
  | '"' :: rest =>
    match splitLex rest with
    | none => none
    | some (lex, after) =>
      match after with
      | [] => some ⟨String.ofList lex, V.xsdString, none⟩
      | '@' :: tag =>
          if tag.isEmpty then none else some ⟨String.ofList lex, V.langString, some (String.ofList tag)⟩
      | '^' :: '^' :: iri =>
          let d := String.ofList iri
          if isIriSpelling d then some ⟨String.ofList lex, d, none⟩ else none
      | _ => none
  | _ => none

/-- The node kind of a term, or `none` when the spelling is not recognised. -/
def kindOf (t : Term) : Option Kind :=
  if isIriSpelling t then some .iri
  else if isBlankSpelling t then some .blank
  else if (asLiteral t).isSome then some .lit
  else none

/-- The six values `sh:nodeKind` can take. -/
inductive NodeKind where
  | iri
  | blankNode
  | literal
  | blankNodeOrIRI
  | blankNodeOrLiteral
  | iriOrLiteral
deriving DecidableEq, Repr

def NodeKind.admits : NodeKind → Kind → Bool
  | .iri, .iri => true
  | .blankNode, .blank => true
  | .literal, .lit => true
  | .blankNodeOrIRI, .blank => true
  | .blankNodeOrIRI, .iri => true
  | .blankNodeOrLiteral, .blank => true
  | .blankNodeOrLiteral, .lit => true
  | .iriOrLiteral, .iri => true
  | .iriOrLiteral, .lit => true
  | _, _ => false

/-! ## Lexical spaces, for the five datatypes this module is willing to judge -/

def isDigits (cs : List Char) : Bool := !cs.isEmpty && cs.all Char.isDigit

/-- The lexical space of `xsd:integer`: an optional sign then at least one digit.
Leading zeros are allowed, which is what the XSD specification says. -/
def isIntLex (s : String) : Bool :=
  match s.toList with
  | '-' :: rest => isDigits rest
  | '+' :: rest => isDigits rest
  | cs => isDigits cs

/-- The natural number a digit string denotes. Written over `List Char` for the
same kernel-reduction reason as the predicates above; `String.toNat?` folds over
byte positions and does not reduce. -/
def natOfDigits (cs : List Char) : Nat :=
  cs.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

/-- The integer a lexical form denotes, when it is in `xsd:integer`'s lexical space. -/
def intValue (s : String) : Option Int :=
  match s.toList with
  | '-' :: rest => if isDigits rest then some (-(Int.ofNat (natOfDigits rest))) else none
  | '+' :: rest => if isDigits rest then some (Int.ofNat (natOfDigits rest)) else none
  | cs => if isDigits cs then some (Int.ofNat (natOfDigits cs)) else none

/-- An exact decimal value: `mant` divided by ten to the `scale`. No floating
point anywhere, so two spellings of one number compare equal and nothing rounds. -/
structure Dec where
  mant : Int
  scale : Nat
deriving DecidableEq, Repr

def takeDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
      if c.isDigit then
        let (a, b) := takeDigits rest
        (c :: a, b)
      else ([], c :: rest)

/-- The lexical space of `xsd:decimal` without its sign: digits with an optional
fractional part, or a bare fractional part. `4.`, `.5` and `4.0` are all in it. -/
def decUnsigned (cs : List Char) : Option Dec :=
  let (ip, r) := takeDigits cs
  match r with
  | [] => if ip.isEmpty then none else some ⟨Int.ofNat (natOfDigits ip), 0⟩
  | '.' :: fr =>
      let (fp, r2) := takeDigits fr
      if !r2.isEmpty then none
      else if ip.isEmpty && fp.isEmpty then none
      else some ⟨Int.ofNat (natOfDigits (ip ++ fp)), fp.length⟩
  | _ => none

def decOfLex (s : String) : Option Dec :=
  match s.toList with
  | '-' :: rest => (decUnsigned rest).map (fun d => ⟨-d.mant, d.scale⟩)
  | '+' :: rest => decUnsigned rest
  | cs => decUnsigned cs

/-! ## The Gregorian calendar, for `xsd:date` and `xsd:dateTime`

Written in `Nat` throughout. `Int` division in Lean rounds toward zero, the usual
day-number algorithms rely on that in one direction and on flooring in the other,
and the difference is exactly the kind of off-by-one that would be invisible in
this suite and wrong in a real graph. Restricting to years from 1 CE keeps every
division on a non-negative number, where all the conventions agree.

The price is stated rather than hidden: a lexical form with a NEGATIVE year, or the
year `0000`, is not judged at all. It is well formed XSD (`0000` in XSD 1.1, not in
1.0, which is itself a reason not to answer), and this module says `none` rather
than guessing either way. -/

def isLeapYear (y : Nat) : Bool := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

def daysInMonth (y m : Nat) : Nat :=
  if m == 2 then (if isLeapYear y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30
  else if 1 ≤ m && m ≤ 12 then 31
  else 0

/-- Days from 0001-01-01, which is day zero, on the proleptic Gregorian calendar. -/
def dayNumber (y m d : Nat) : Nat :=
  let n := y - 1
  let yearDays := n * 365 + n / 4 - n / 100 + n / 400
  let monthDays := (List.range (m - 1)).foldl (fun acc i => acc + daysInMonth y (i + 1)) 0
  yearDays + monthDays + (d - 1)

/-- Exactly `n` characters, or nothing. -/
def takeExactly : Nat → List Char → Option (List Char × List Char)
  | 0, cs => some ([], cs)
  | _ + 1, [] => none
  | n + 1, c :: cs => (takeExactly n cs).map fun p => (c :: p.1, p.2)

/-- Exactly `n` digits, as a number. -/
def digitsN (n : Nat) (cs : List Char) : Option (Nat × List Char) :=
  match takeExactly n cs with
  | none => none
  | some (ds, rest) => if ds.all Char.isDigit then some (natOfDigits ds, rest) else none

/-- A timezone offset in minutes east of UTC. XSD caps it at fourteen hours. -/
def parseOffset (cs : List Char) : Option Int :=
  match digitsN 2 cs with
  | none => none
  | some (h, r1) =>
      match r1 with
      | ':' :: r2 =>
          match digitsN 2 r2 with
          | none => none
          | some (mi, r3) =>
              if !r3.isEmpty then none
              else if h > 14 || mi > 59 then none
              else if h == 14 && mi != 0 then none
              else some (Int.ofNat (h * 60 + mi))
      | _ => none

/-- The timezone at the END of a lexical form: absent, `Z`, or a signed offset.
Anything else, including trailing junk, is not a timezone. -/
def parseTzEnd : List Char → Option (Option Int)
  | [] => some none
  | ['Z'] => some (some 0)
  | '+' :: rest => (parseOffset rest).map some
  | '-' :: rest => (parseOffset rest).map (fun m => some (-m))
  | _ => none

/-- `yyyy-mm-dd`, with the day checked against the month and the year. -/
def parseDateBody (cs : List Char) : Option (Nat × Nat × Nat × List Char) :=
  let (ds, r0) := takeDigits cs
  if ds.length < 4 then none
  else if ds.length > 4 && ds.head? == some '0' then none
  else
    let y := natOfDigits ds
    match r0 with
    | '-' :: r1 =>
        match digitsN 2 r1 with
        | none => none
        | some (mo, r2) =>
            match r2 with
            | '-' :: r3 =>
                match digitsN 2 r3 with
                | none => none
                | some (d, r4) =>
                    if mo < 1 || mo > 12 then none
                    else if d < 1 || d > daysInMonth y mo then none
                    else some (y, mo, d, r4)
            | _ => none
    | _ => none

/-- `hh:mm:ss` with optional fractional seconds. Returns the seconds since
midnight as an exact scaled decimal, plus a carry of one day for the `24:00:00`
form, which XSD allows and which denotes midnight starting the next day. -/
def parseTimeBody (cs : List Char) : Option (Dec × Nat × List Char) :=
  match digitsN 2 cs with
  | none => none
  | some (h, r1) =>
      match r1 with
      | ':' :: r2 =>
          match digitsN 2 r2 with
          | none => none
          | some (mi, r3) =>
              match r3 with
              | ':' :: r4 =>
                  match digitsN 2 r4 with
                  | none => none
                  | some (sec, r5) =>
                      let (fd, r6) :=
                        match r5 with
                        | '.' :: fr => let (a, b) := takeDigits fr; (a, b)
                        | _ => ([], r5)
                      if (match r5 with | '.' :: _ => fd.isEmpty | _ => false) then none
                      else if h > 24 || mi > 59 || sec > 59 then none
                      else if h == 24 && (mi != 0 || sec != 0 || !(fd.all (· == '0'))) then none
                      else
                        let carry := if h == 24 then 1 else 0
                        let base := (if h == 24 then 0 else h) * 3600 + mi * 60 + sec
                        let scale := fd.length
                        some (⟨Int.ofNat (base * 10 ^ scale + natOfDigits fd), scale⟩, carry, r6)
              | _ => none
      | _ => none

/-- What reading a date or dateTime lexical form can produce. `illFormed` is a
verdict about the lexical space; `notJudged` is this module declining. -/
inductive DtRead where
  /-- The seconds from 0001-01-01T00:00:00 in the form's OWN timezone, and that
  timezone's offset in minutes when the form carried one. -/
  | ok (local_ : Dec) (tz : Option Int)
  | illFormed
  | notJudged
deriving Repr

/-- Is this lexical form a year this module is willing to read? -/
def yearJudgeable (cs : List Char) : Bool :=
  match cs with
  | '-' :: _ => false
  | _ => let (ds, _) := takeDigits cs; !(ds.length ≥ 4 && ds.all (· == '0'))

def readDate (s : String) : DtRead :=
  let cs := s.toList
  if !yearJudgeable cs then .notJudged
  else
    match parseDateBody cs with
    | none => .illFormed
    | some (y, m, d, rest) =>
        match parseTzEnd rest with
        | none => .illFormed
        | some tz => .ok ⟨Int.ofNat (dayNumber y m d * 86400), 0⟩ tz

def readDateTime (s : String) : DtRead :=
  let cs := s.toList
  if !yearJudgeable cs then .notJudged
  else
    match parseDateBody cs with
    | none => .illFormed
    | some (y, m, d, r0) =>
        match r0 with
        | 'T' :: r1 =>
            match parseTimeBody r1 with
            | none => .illFormed
            | some (tod, carry, r2) =>
                match parseTzEnd r2 with
                | none => .illFormed
                | some tz =>
                    let days := Int.ofNat ((dayNumber y m d + carry) * 86400)
                    .ok ⟨days * Int.ofNat (10 ^ tod.scale) + tod.mant, tod.scale⟩ tz
        | _ => .illFormed

def dtLexOK : DtRead → Option Bool
  | .ok _ _ => some true
  | .illFormed => some false
  | .notJudged => none

/-- **Is this literal well formed for its datatype?**

`some true` yes, `some false` no, `none` this module does not know the datatype's
lexical space and will not guess.

SHACL requires a value node to be a well-formed literal of the named datatype, not
merely a literal carrying the right datatype IRI, so this question cannot be
skipped. It can, however, be declined, and declining is what `none` is for: the
evaluator turns a `none` into a refusal to answer rather than into a verdict. That
is the whole difference between a validator that is quiet about what it does not
know and one that says `conforms` because it did not look.

The nine it does know are `xsd:string` (every lexical form), `rdf:langString`
(every lexical form, given a tag), `rdf:HTML` (every lexical form: RDF 1.1
Concepts says "the lexical space is the set of Unicode strings", so HTML parsing
never fails and there is nothing to reject), `xsd:boolean`, `xsd:integer`,
`xsd:byte`, `xsd:decimal`, `xsd:date` and `xsd:dateTime`. The last two are judged
by a real calendar, leap years included, and decline rather than answer on a
negative year or on `0000`; see the calendar section above.

The lexical form is still N-Triples-escaped when it gets here. For every datatype
above except `rdf:HTML` no well-formed value contains a character that needs
escaping, so the check is exact for them; `rdf:HTML` accepts every string, so the
escaping cannot change the answer there either. It would not be exact for a
datatype whose lexical space
includes quotes or newlines, which is one more reason the list is short. -/
def lexOK (l : Lit) : Option Bool :=
  if l.dt = V.xsdString then some true
  else if l.dt = V.langString then some l.lang.isSome
  else if l.dt = V.xsdBoolean then
    some (l.lex = "true" || l.lex = "false" || l.lex = "1" || l.lex = "0")
  else if l.dt = V.xsdInteger then some (isIntLex l.lex)
  else if l.dt = V.rdfHTML then some true
  else if l.dt = V.xsdByte then
    some (match intValue l.lex with
          | some v => -128 ≤ v && v ≤ 127
          | none => false)
  else if l.dt = V.xsdDecimal then some (decOfLex l.lex).isSome
  else if l.dt = V.xsdDate then dtLexOK (readDate l.lex)
  else if l.dt = V.xsdDateTime then dtLexOK (readDateTime l.lex)
  else none

/-! ## The string a term denotes, for the two length constraints

`sh:minLength` and `sh:maxLength` are defined over the SPARQL `STRLEN(str(v))` of
the value node, with the extra rule that a blank node always violates them. So the
question a length constraint asks is not "how long is this spelling" but "how long
is the string this spelling denotes", and those differ exactly when the spelling
carries a backslash escape, which nothing in this development decodes. -/

/-- The characters of the string a term denotes.

* `chars cs` the term denotes the string `cs`, exactly.
* `noString` the term is a blank node. SHACL says a blank node violates
  `sh:minLength` and `sh:maxLength` whatever the bound is, so this is a verdict and
  not a refusal.
* `unknown` the spelling carries a backslash, so its characters are not the
  denoted string's characters and this module will not guess how many there are. -/
inductive StrRep where
  | chars (cs : List Char)
  | noString
  | unknown
deriving DecidableEq, Repr

def hasBackslash (s : String) : Bool := s.toList.any (fun c => c == '\\')

/-- The body of an IRI spelling, without the angle brackets. -/
def iriBody (t : Term) : List Char :=
  match t.toList with
  | '<' :: rest => rest.dropLast
  | cs => cs

/-- `str(v)` as a character list, or a reason there is not one. For an IRI this is
the IRI itself; for a literal it is the lexical form, tag and datatype dropped. -/
def strRep (t : Term) : StrRep :=
  if isBlankSpelling t then .noString
  else if isIriSpelling t then
    (let body := iriBody t
     if body.any (fun c => c == '\\') then .unknown else .chars body)
  else
    match asLiteral t with
    | some l => if hasBackslash l.lex then .unknown else .chars l.lex.toList
    | none => .unknown

/-! ## Language tags, for `sh:languageIn` and `sh:uniqueLang` -/

def toLowerAscii (cs : List Char) : List Char := cs.map Char.toLower

/-- BCP 47 basic filtering, section 3.3.1: a basic language range matches a
language tag when the tag is the range, or the tag continues the range at a subtag
boundary. Comparison is ASCII case-insensitive, which is what BCP 47 requires;
nothing else BCP 47 says is implemented, and `*` is NOT treated as the wildcard
range because `sh:languageIn` takes tags rather than ranges in every test this is
measured against. -/
def langMatches (range tag : String) : Bool :=
  let r := toLowerAscii range.toList
  let t := toLowerAscii tag.toList
  if r.isPrefixOf t then (t.length == r.length) || (t.drop r.length).head? == some '-'
  else false

/-- The language tag of a term, when it has one. -/
def langOf (t : Term) : Option String :=
  match asLiteral t with
  | some l => l.lang
  | none => none

/-! ## Comparing two terms by VALUE

The Recommendation defines `sh:minExclusive`, `sh:maxExclusive`, `sh:minInclusive`,
`sh:maxInclusive`, `sh:lessThan` and `sh:lessThanOrEquals` through a SPARQL
expression: for `sh:minExclusive` the condition is that `$minExclusive < $value`
RETURNS TRUE. That phrasing carries the whole of SPARQL's three-valued behaviour.
`<` is defined only for two numerics, two simple literals or `xsd:string`s, two
`xsd:boolean`s and two `xsd:dateTime`s; every other pair of operands is a TYPE
ERROR, and a type error does not return true, so it is a violation.

This module therefore answers with three possibilities rather than two, and the
distinction between the second and the third is the point of the whole file.

* `some k` for `k` one of `lt`, `eq`, `gt`: the two are comparable and this is the
  order.
* `some incomparable`: SPARQL's `<` RAISES A TYPE ERROR here, and that is a
  verdict. An IRI or a blank node on either side, a language-tagged literal, or two
  literals from different families are all in this case.
* `some unordered`: the two have the same type and the order relation still does
  not put them in an order. Only `xsd:dateTime` does this, and only when one form
  carries a timezone and the other does not; see below. Also a verdict.
* `none`: this development does not know. A literal of a datatype outside the four
  families implemented, or a lexical form carrying an escape. The evaluator turns
  this into a refusal to answer, never into a verdict.

## What is and is not implemented

Implemented: `xsd:integer` and `xsd:decimal` (as exact scaled integers, so
`"4"^^xsd:integer` and `"4.0"^^xsd:decimal` compare EQUAL and no rounding happens
anywhere), `xsd:string` and plain literals, `xsd:boolean`, and `xsd:dateTime`.

NOT implemented, and therefore `none`: `xsd:float` and `xsd:double`, which are
binary floating point with `NaN` and two zeros; every derived integer type
(`xsd:byte`, `xsd:int`, `xsd:unsignedLong` and the rest), which SPARQL treats as
numeric and which this module declines rather than half-handles; `xsd:date`, whose
lexical space IS judged above but which the suite never compares. Declining costs a
refusal. Guessing would cost a wrong answer, and the second is worse.

## The timezone rule for `xsd:dateTime`, which is where the care is

Two forms that both carry a timezone are compared as instants. Two that both lack
one are compared as written. A MIXED pair is the interesting case, and XSD 1.0's
order relation for `dateTime` settles it: the form without a timezone stands for
any instant within fourteen hours either side, so the pair is ordered only when the
timezoned instant falls entirely outside that window, and is UNORDERED otherwise.

That is not an implementation convenience. `core/node/minInclusive-002` and
`core/node/minInclusive-003` are the Working Group's approved tests for exactly this
pair of cases, and both require the mixed comparisons to come out as violations:
`$minInclusive <= $value` does not return true when the two are unordered. An
implementation that instead gave the untimezoned form an implicit timezone, as
XPath's `op:dateTime-less-than` does, would answer `conforms` for at least one of
the value nodes in `minInclusive-003` and would fail that test. -/

/-- The result of SPARQL's `<` family on two RDF terms, as far as this development
is willing to commit. `incomparable` is a verdict, not an absence of one. -/
inductive Cmp where
  | lt
  | eq
  | gt
  /-- SPARQL's `<` is a type error on this pair of operands. -/
  | incomparable
  /-- Same type, and the order relation still does not order them. Only a
  timezoned `xsd:dateTime` against an untimezoned one, within fourteen hours. -/
  | unordered
deriving DecidableEq, Repr

/-- The families SPARQL's `<` is defined within. -/
inductive Fam where
  | num
  | str
  | boolean
  | dateTime
deriving DecidableEq, Repr

/-- Where a term sits: in a family, definitely in none, or not classified. -/
inductive Classified where
  | inFam (φ : Fam)
  /-- Definitely outside every family SPARQL's `<` is defined on, so `<` is a type
  error on this term whatever the other operand is. -/
  | noFam
  | unknown
deriving DecidableEq, Repr

def famOf (t : Term) : Classified :=
  if isIriSpelling t then .noFam
  else if isBlankSpelling t then .noFam
  else
    match asLiteral t with
    | none => .unknown
    | some l =>
        if l.lang.isSome then .noFam
        else if l.dt = V.xsdString then .inFam .str
        else if l.dt = V.xsdBoolean then .inFam .boolean
        else if l.dt = V.xsdInteger then .inFam .num
        else if l.dt = V.xsdDecimal then .inFam .num
        else if l.dt = V.xsdDateTime then .inFam .dateTime
        else .unknown

/-- The number a literal denotes, for the two numeric datatypes implemented.
`none` means the literal is ILL TYPED for its datatype, which SPARQL treats as
having no value at all. -/
def numValue (l : Lit) : Option Dec :=
  if l.dt = V.xsdInteger then (intValue l.lex).map (fun v => ⟨v, 0⟩)
  else if l.dt = V.xsdDecimal then decOfLex l.lex
  else none

def cmpDec (a b : Dec) : Cmp :=
  let x := a.mant * Int.ofNat (10 ^ b.scale)
  let y := b.mant * Int.ofNat (10 ^ a.scale)
  if x < y then .lt else if x = y then .eq else .gt

/-- Codepoint order, which is the collation SPARQL's `<` uses on strings. -/
def cmpChars : List Char → List Char → Cmp
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
      if a.toNat < b.toNat then .lt
      else if b.toNat < a.toNat then .gt
      else cmpChars as bs

def boolValue (lex : String) : Option Bool :=
  if lex = "true" || lex = "1" then some true
  else if lex = "false" || lex = "0" then some false
  else none

/-- Fourteen hours in seconds, the width of XSD's timezone window. -/
def tzWindowSeconds : Int := 14 * 3600

/-- Shift an exact number of seconds by a whole number of seconds, keeping the
scale so nothing rounds. -/
def decShift (d : Dec) (secs : Int) : Dec :=
  ⟨d.mant + secs * Int.ofNat (10 ^ d.scale), d.scale⟩

/-- Compare two `xsd:dateTime` readings. See the section header for the timezone
rule; `unordered` is a verdict and `none` is a refusal. -/
def cmpDateTime : DtRead → DtRead → Option Cmp
  | .notJudged, _ => none
  | _, .notJudged => none
  | .illFormed, _ => some .incomparable
  | _, .illFormed => some .incomparable
  | .ok a ta, .ok b tb =>
      match ta, tb with
      | some oa, some ob =>
          some (cmpDec (decShift a (-(oa * 60))) (decShift b (-(ob * 60))))
      | none, none => some (cmpDec a b)
      | some oa, none =>
          -- `a` is an instant; `b` stands for the window around its local value.
          let ai := decShift a (-(oa * 60))
          if cmpDec ai (decShift b (-tzWindowSeconds)) == .lt then some .lt
          else if cmpDec ai (decShift b tzWindowSeconds) == .gt then some .gt
          else some .unordered
      | none, some ob =>
          let bi := decShift b (-(ob * 60))
          if cmpDec (decShift a tzWindowSeconds) bi == .lt then some .lt
          else if cmpDec (decShift a (-tzWindowSeconds)) bi == .gt then some .gt
          else some .unordered

/-- Compare two literals known to be in the same family. -/
def cmpSameFam : Fam → Lit → Lit → Option Cmp
  | .num, a, b =>
      match numValue a, numValue b with
      | some x, some y => some (cmpDec x y)
      | _, _ => some .incomparable
  | .str, a, b =>
      if hasBackslash a.lex || hasBackslash b.lex then none
      else some (cmpChars a.lex.toList b.lex.toList)
  | .boolean, a, b =>
      match boolValue a.lex, boolValue b.lex with
      | some x, some y => some (if x = y then .eq else if x then .gt else .lt)
      | _, _ => some .incomparable
  | .dateTime, a, b => cmpDateTime (readDateTime a.lex) (readDateTime b.lex)

/-- **The comparison.** See the section header for what each answer means. -/
def cmpTerms (a b : Term) : Option Cmp :=
  match famOf a, famOf b with
  | .noFam, _ => some .incomparable
  | _, .noFam => some .incomparable
  | .unknown, _ => none
  | _, .unknown => none
  | .inFam φ, .inFam ψ =>
      if φ = ψ then
        match asLiteral a, asLiteral b with
        | some la, some lb => cmpSameFam φ la lb
        | _, _ => none
      else some .incomparable

end Shacl
