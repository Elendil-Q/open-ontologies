import Shacl.Shape

/-!
# The specification

What it means for a focus node to conform to a shape. Nothing in this file
computes anything: `Conf` is a `Prop`, the counting constraints quantify over
lists of value nodes rather than over any enumeration procedure, and the subclass
closure is an inductive relation rather than a fixpoint. `Shacl/Eval.lean` gives a
decision procedure and `Shacl/Agreement.lean` proves the two agree.

## Where this comes from

SHACL's normative validators are the prose ones in Appendix D of the
Recommendation. The document says of its own SPARQL definitions that they
"represent potential validators ... included for illustration purposes only and
have no formal status otherwise". So a direct reading of the prose is closer to the
normative text than a translation into SPARQL is, and it puts no SPARQL engine in
the trust path.

Each clause below is that prose, restated. The clauses that are NOT the prose are
called out where they occur, and there are two of them:

* `datatype` demands `lexOK l = some true`, so a literal whose datatype this
  development declines to judge (`lexOK = none`) does NOT conform. The evaluator
  refuses to answer in that case rather than reporting the violation this
  specification would license, which is the more conservative of the two.
* `klass` reads `rdfs:subClassOf*` off the data graph only. The Recommendation says
  the same, and an engine that reasons first will disagree with both.
* The four value-range clauses and the two length clauses read `cmpTerms` and
  `strRep` from `Shacl/Term.lean`, and both of those have a third answer. Where they
  decline, these clauses say the node does NOT conform and the evaluator refuses to
  answer instead, which is again the more conservative of the two.

## Why `Conf` ignores `named`

`named` carries the `sh:sourceShape` IRI for the report. A shape's identity must
not be able to change whether a node conforms, so the clause for it is a
pass-through. That is a property worth stating rather than assuming, and
`Agreement.lean` states it as `conf_named`.
-/
namespace Shacl

/-- `v` is a value node of `f` along `pa`. The whole of the path semantics covered,
by recursion on the path.

A sequence path holds when some intermediate node joins the two halves, which is
the SPARQL property-path semantics and is NOT the same as "there is a triple".
`zeroOrOne` admits the focus node itself, so a focus node with no outgoing triple
still has exactly one value node, and `core/path/path-zeroOrOne-001` is the
Working Group's test that a validator does not forget that. -/
def IsValue (G : Graph) : Path → Term → Term → Prop
  | .pred p, f, v => (⟨f, p, v⟩ : Triple) ∈ G
  | .inv p, f, v => (⟨v, p, f⟩ : Triple) ∈ G
  | .seq a b, f, v => ∃ m, IsValue G a f m ∧ IsValue G b m v
  | .alt a b, f, v => IsValue G a f v ∨ IsValue G b f v
  | .zeroOrOne a, f, v => v = f ∨ IsValue G a f v

/-- The value nodes of a shape that may or may not carry a path. On a property
shape they are the nodes reached along the path; on a node shape the single value
node is the focus node itself, which is what the Recommendation says and what makes
`sh:equals` on a node shape mean anything at all. -/
def IsValueOrSelf (G : Graph) : Option Path → Term → Term → Prop
  | none, f, v => v = f
  | some pa, f, v => IsValue G pa f v

/-- `rdfs:subClassOf*`, read off the data graph and nothing else. Reflexive and
transitive by construction. -/
inductive SubClassStar (G : Graph) : Term → Term → Prop
  | refl (a : Term) : SubClassStar G a a
  | step {a b c : Term} :
      (⟨a, V.subClassOf, b⟩ : Triple) ∈ G → SubClassStar G b c → SubClassStar G a c

/-- A SHACL instance of a class: a node with an `rdf:type` value that is a
subclass, reflexively and transitively, of the class. -/
def IsInstance (G : Graph) (c x : Term) : Prop :=
  ∃ t, (⟨x, V.type, t⟩ : Triple) ∈ G ∧ SubClassStar G t c

/-- `cmpTerms a b` is known, and the order it reports is one of `ok`.

The Recommendation phrases the four value-range constraints as SPARQL expressions
that must RETURN TRUE, so a pair SPARQL cannot compare is a violation rather than a
pass. `cmpTerms` reports such a pair as `some .incomparable`, which is never in any
`ok` list below, so this definition inherits that reading. A pair `cmpTerms`
declines to classify is `none`, which is also not in `ok`, so the specification
calls it a violation; the evaluator refuses instead. -/
def CmpIs (ok : List Cmp) (a b : Term) : Prop := ∃ k, cmpTerms a b = some k ∧ k ∈ ok

theorem CmpIs.of_eq {ok : List Cmp} {a b : Term} {k : Cmp} (h : cmpTerms a b = some k)
    (hm : k ∈ ok) : CmpIs ok a b := ⟨k, h, hm⟩

theorem CmpIs.not_of_eq {ok : List Cmp} {a b : Term} {k : Cmp} (h : cmpTerms a b = some k)
    (hm : k ∉ ok) : ¬ CmpIs ok a b := by
  rintro ⟨k', hk', hm'⟩
  rw [h] at hk'
  injection hk' with e
  subst e
  exact hm hm'

/-- Something holds of the string a term denotes. False for a blank node, which has
no string representation, and false for a spelling whose characters are not the
denoted string's, where the evaluator refuses instead. -/
def StrProp (t : Term) (Q : List Char → Prop) : Prop := ∃ cs, strRep t = .chars cs ∧ Q cs

/-- The string a term denotes has this many characters. False for a blank node,
which SHACL says violates both length constraints, and false for a spelling whose
characters are not the denoted string's, where the evaluator refuses. -/
def StrLen (t : Term) (P : Nat → Prop) : Prop := StrProp t (fun cs => P cs.length)

/-! ## What it is for a pattern to match

A recursive definition rather than an inductive relation, so that inverting it is
unfolding rather than a case analysis on indices. `ItemsMatch fold items s r` says
the items consume a prefix of `s` and leave `r`. -/

def ItemsMatch (fold : Bool) : List Item → List Char → List Char → Prop
  | [], s, r => r = s
  | it :: rest, s, r =>
      match it.quant with
      | .one =>
          ∃ c s', s = c :: s' ∧ itemAdmits fold it c = true ∧ ItemsMatch fold rest s' r
      | .star =>
          ∃ pre s', s = pre ++ s' ∧ (∀ c ∈ pre, itemAdmits fold it c = true) ∧
            ItemsMatch fold rest s' r

/-- SPARQL `REGEX` is a SEARCH: an unanchored pattern matches when some substring
matches. `^` pins the start of that substring to the start of the string and `$`
pins its end to the end. -/
def RegexMatch (re : Regex) (s : List Char) : Prop :=
  ∃ pre suf r, s = pre ++ suf ∧ (re.anchorStart = true → pre = []) ∧
    ItemsMatch re.fold re.items suf r ∧ (re.anchorEnd = true → r = [])

theorem StrLen.of_chars {t : Term} {cs : List Char} {P : Nat → Prop}
    (h : strRep t = .chars cs) (hp : P cs.length) : StrLen t P := ⟨cs, h, hp⟩

theorem StrLen.not_of_chars {t : Term} {cs : List Char} {P : Nat → Prop}
    (h : strRep t = .chars cs) (hp : ¬ P cs.length) : ¬ StrLen t P := by
  rintro ⟨cs', hc, hp'⟩
  rw [h] at hc
  injection hc with e
  subst e
  exact hp hp'

/-- A blank node has no string representation at all, so no length constraint holds
of it. This is the clause the Recommendation states separately for `sh:minLength`
and `sh:maxLength`, and it is why a blank node violates BOTH of them at once. -/
theorem StrLen.not_of_blank {t : Term} {P : Nat → Prop} (h : strRep t = .noString) :
    ¬ StrLen t P := by
  rintro ⟨cs, hc, -⟩
  rw [h] at hc
  exact absurd hc (by simp)

/-- **Conformance.** `Conf G s f` says focus node `f` conforms to shape `s` in
graph `G`.

The two counting clauses are the point of interest. `minCount` says there EXIST
that many distinct value nodes; `maxCount` says NO list of distinct value nodes is
longer than the bound. Both are statements about the set of value nodes with no
enumeration of it anywhere, which is what keeps this specification independent of
the evaluator that has to build one. -/
def Conf (G : Graph) : Shape → Term → Prop
  | .top, _ => True
  | .bot, _ => False
  | .klass c, f => IsInstance G c f
  | .datatype d, f => ∃ l, asLiteral f = some l ∧ l.dt = d ∧ lexOK l = some true
  | .nodeKind k, f => ∃ κ, kindOf f = some κ ∧ k.admits κ = true
  | .hasValue v, f => f = v
  | .inSet vs, f => f ∈ vs
  | .minInclusive c, f => CmpIs [.lt, .eq] c f
  | .maxInclusive c, f => CmpIs [.gt, .eq] c f
  | .minExclusive c, f => CmpIs [.lt] c f
  | .maxExclusive c, f => CmpIs [.gt] c f
  | .minLength n, f => StrLen f (fun len => n ≤ len)
  | .maxLength n, f => StrLen f (fun len => len ≤ n)
  | .languageIn tags, f =>
      ∃ t, langOf f = some t ∧ ∃ r ∈ tags, langMatches r t = true
  | .pattern re, f => StrProp f (fun cs => RegexMatch re cs)
  | .equals pa q, f =>
      ∀ v, IsValueOrSelf G pa f v ↔ (⟨f, q, v⟩ : Triple) ∈ G
  | .disjoint pa q, f =>
      ∀ v, IsValueOrSelf G pa f v → (⟨f, q, v⟩ : Triple) ∉ G
  | .lessThan pa q, f =>
      ∀ v w, IsValueOrSelf G pa f v → (⟨f, q, w⟩ : Triple) ∈ G → CmpIs [.lt] v w
  | .lessThanOrEq pa q, f =>
      ∀ v w, IsValueOrSelf G pa f v → (⟨f, q, w⟩ : Triple) ∈ G → CmpIs [.lt, .eq] v w
  | .uniqueLang pa, f =>
      ∀ v w, IsValueOrSelf G pa f v → IsValueOrSelf G pa f w → v ≠ w →
        langOf v = none ∨ langOf v ≠ langOf w
  | .qualifiedMin pa q n, f =>
      ∃ l : List Term, l.Nodup ∧ (∀ v ∈ l, IsValue G pa f v ∧ Conf G q v) ∧ n ≤ l.length
  | .qualifiedMax pa q n, f =>
      ∀ l : List Term, l.Nodup → (∀ v ∈ l, IsValue G pa f v ∧ Conf G q v) → l.length ≤ n
  | .closed allowed, f => ∀ p o, (⟨f, p, o⟩ : Triple) ∈ G → p ∈ allowed
  | .report _ a, f => Conf G a f
  | .both a b, f => Conf G a f ∧ Conf G b f
  | .andC a b, f => Conf G a f ∧ Conf G b f
  | .orC a b, f => Conf G a f ∨ Conf G b f
  | .notC a, f => ¬ Conf G a f
  | .nodeC a, f => Conf G a f
  | .named _ a, f => Conf G a f
  | .forAll pa a, f => ∀ v, IsValue G pa f v → Conf G a v
  | .minCount pa n, f =>
      ∃ l : List Term, l.Nodup ∧ (∀ v ∈ l, IsValue G pa f v) ∧ n ≤ l.length
  | .maxCount pa n, f =>
      ∀ l : List Term, l.Nodup → (∀ v ∈ l, IsValue G pa f v) → l.length ≤ n
  | .hasValueOn pa v, f => IsValue G pa f v

/-! ## Targets

A target declaration selects focus nodes. These are `Prop`s for the same reason
`Conf` is: the executable computes a list and the agreement is proved. -/

/-- The focus nodes a target declaration selects. -/
inductive Target where
  | node (n : Term)
  | klass (c : Term)
  | subjectsOf (p : Term)
  | objectsOf (p : Term)
deriving DecidableEq, Repr

def IsFocus (G : Graph) : Target → Term → Prop
  | .node n, x => x = n
  | .klass c, x => IsInstance G c x
  | .subjectsOf p, x => ∃ o, (⟨x, p, o⟩ : Triple) ∈ G
  | .objectsOf p, x => ∃ s, (⟨s, p, x⟩ : Triple) ∈ G

end Shacl
