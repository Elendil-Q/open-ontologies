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
  this side of the line for term equality, but SHACL's comparison constraints
  (`sh:lessThan`, `sh:minInclusive`) are value-based and are therefore not
  implemented at all rather than implemented wrongly.
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
* **Language tags are compared as written.** BCP 47 says `EN` and `en` are the same
  tag. Here they are two tags. Nothing in the covered fragment compares tags, so
  this costs nothing today; `sh:languageIn` is not implemented.
* **A lexical form's LENGTH is not the value's length.** `"a\\nb"` is a three-character
  value written with four characters, because nothing here decodes an escape. That is
  why `sh:minLength` and `sh:maxLength` are not implemented rather than implemented
  over the spelling: they would be right for every literal without an escape and
  silently wrong for the rest, which is the worst of the three options.
* **Lexical spaces are known for five datatypes and no more.** See `lexOK`.
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

/-- **Is this literal well formed for its datatype?**

`some true` yes, `some false` no, `none` this module does not know the datatype's
lexical space and will not guess.

SHACL requires a value node to be a well-formed literal of the named datatype, not
merely a literal carrying the right datatype IRI, so this question cannot be
skipped. It can, however, be declined, and declining is what `none` is for: the
evaluator turns a `none` into a refusal to answer rather than into a verdict. That
is the whole difference between a validator that is quiet about what it does not
know and one that says `conforms` because it did not look.

The five it does know are `xsd:string` (every lexical form), `rdf:langString`
(every lexical form, given a tag), `xsd:boolean`, `xsd:integer` and `xsd:byte`.
Those are the datatypes the W3C core suite names in a `sh:datatype` constraint,
apart from `xsd:date` and `rdf:HTML`, which land in `none`.

The lexical form is still N-Triples-escaped when it gets here. For the five
datatypes above no well-formed value contains a character that needs escaping, so
the check is exact for them; it would not be for a datatype whose lexical space
includes quotes or newlines, which is one more reason the list is short. -/
def lexOK (l : Lit) : Option Bool :=
  if l.dt = V.xsdString then some true
  else if l.dt = V.langString then some l.lang.isSome
  else if l.dt = V.xsdBoolean then
    some (l.lex = "true" || l.lex = "false" || l.lex = "1" || l.lex = "0")
  else if l.dt = V.xsdInteger then some (isIntLex l.lex)
  else if l.dt = V.xsdByte then
    some (match intValue l.lex with
          | some v => -128 ≤ v && v ≤ 127
          | none => false)
  else none

end Shacl
