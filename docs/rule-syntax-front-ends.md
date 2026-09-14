# Rules you wrote, in SWRL or RIF Core

`lean/OOCert/Horn.lean` proves one soundness theorem good for every rule table at once, and
`reason --rules` evaluates a table and writes a certificate. Between them they were said to cover
the logic-programming family: Datalog, the Rule Interchange Format, the Semantic Web Rule Language.

They did not. The only rule syntax anything here could read was `rules.tsv`, the tab-separated
encoding the Lean parser happens to use, which is an internal format and not a language anybody
writes in. A user holding a SWRL ontology or a RIF Core document could use none of it. `rules-import`
is the way in.

```bash
open-ontologies rules-import --from swrl --out rules.tsv                 # the LOADED graph
open-ontologies rules-import --from swrl --file rules.owl --out rules.tsv
open-ontologies rules-import --from rif  --file rules.xml --out rules.tsv
open-ontologies rules-import --from rif  --file rules.xml               # table returned inline
```

MCP: `onto_rules_import` with `from`, `file`, `out`, `allow_partial`.

## What is supported, exactly

Nothing here claims to support SWRL or RIF Core. Each front end supports a FRAGMENT, and the
fragment is printed in every response under `supported_fragment`.

### SWRL

Rules in the RDF encoding, which is the form a SWRL rule takes inside an OWL ontology: `swrl:Imp`
with `swrl:body` and `swrl:head` as `rdf:List` atom lists. Three atom forms are read, and they are
the three that ARE triple patterns.

| SWRL atom | triple pattern |
|---|---|
| `swrl:ClassAtom` with `swrl:classPredicate` C, `swrl:argument1` a | `a rdf:type C` |
| `swrl:IndividualPropertyAtom` with `swrl:propertyPredicate` P, `argument1` a, `argument2` b | `a P b` |
| `swrl:DatavaluedPropertyAtom` with `swrl:propertyPredicate` P, `argument1` a, `argument2` v | `a P v` |

An argument typed `rdf:type swrl:Variable` becomes a variable; anything else is a constant in its
N-Triples spelling. A conjunctive head of *n* atoms becomes *n* rules, which is the standard split
of a conjunctive consequent, and the count is reported as `conjunctive_heads_split`.

### RIF Core

The **XML syntax only**. The presentation syntax is a different grammar and is refused by name
rather than half-read.

| RIF construct | triple pattern |
|---|---|
| `Frame` with object o and slot (p, v) | `o p v` |
| `Member` with instance i, class c | `i rdf:type c` |
| `Subclass` with sub a, super b | `a rdfs:subClassOf b` |
| `Atom` with op p, args (a, b) | `a p b` |
| `Atom` with op p, args (a) | `a rdf:type p` |

`Forall` wrapping an `Implies` is a rule; a bare `Atom`, `Frame`, `Member` or `Subclass` is a ground
fact, which becomes a rule with an empty body. `And` in the condition is a conjunction; `And` in the
conclusion, and a multi-slot `Frame` in the conclusion, become several rules. `Exists` is accepted
in the condition, where dropping the quantifier is equivalent, and refused in the conclusion, where
it is not.

`Const type="&rif;iri"` is an IRI; any other type is a typed literal, with `rdf:PlainLiteral` split
on its trailing `@lang`. Entity references are not expanded: a document written against a DOCTYPE
declaring `&rif;` must be serialised with them expanded, and one that is not is an error rather than
a guess, because reading `&rif;iri` as six literal characters would turn every IRI constant into a
local one.

**`Atom` of arity 1 and 2 is a CONVENTION, not part of RIF.** RIF predicates have their own
extensions; reading a unary predicate as an RDF class and a binary one as an RDF property is the
usual mapping and it is the one taken here. `Frame`, `Member` and `Subclass` need no convention:
they are the RIF constructs the RIF–RDF combination already defines as triples.

### Datalog

Not offered under that name. Datalog has no single standard concrete syntax, and a Datalog program
over triples IS a `rules.tsv` table, which `reason --rules` already takes. Claiming a Datalog front
end would be exactly the "covered in architecture" move this work exists to undo.

## What is refused, and why a refusal is loud

| refused | why a Horn table over triple patterns cannot hold it |
|---|---|
| `swrl:BuiltinAtom` (`swrlb:` arithmetic, string, date predicates) | a predicate over the data domain, computed rather than matched. The table's atoms match triples that are in the graph |
| `swrl:SameIndividualAtom` | equality of individuals in the domain, not a triple. `owl:sameAs` would be a different claim: the checker has no congruence, so nothing downstream substitutes equals for equals |
| `swrl:DifferentIndividualsAtom` | a negative fact; a Horn rule is positive atoms implying one positive atom |
| `swrl:DataRangeAtom` | a test on the VALUE a literal denotes. The checker compares RDF terms and does no datatype reasoning |
| a `classPredicate`/`propertyPredicate` that is a blank node | an anonymous class expression. A triple pattern holds a name, not a class expression |
| a `classPredicate`/`propertyPredicate` that is a variable | SWRL requires an IRI there |
| an empty `swrl:head` | an integrity constraint: the conclusion is falsity, and there is no head atom to derive |
| an atom list that does not reach `rdf:nil` | read short it is a rule with FEWER conditions, which fires MORE often than the one written |
| `rif:Equal`, in the condition or the conclusion | a rule table has no equality. In the conclusion, deriving one would require every later step to substitute equals for equals |
| `rif:External` term or predicate | computed by a function outside the rule set; nothing here computes |
| `rif:Expr` | a function application. RIF Core is function-free, and a triple position holds a name or a variable |
| a `rif:local` constant | scoped to the document and denoting nothing outside it. Giving it an IRI would be minting a name the document does not have |
| a `rif:List` term | a triple position holds one term |
| `Or`, `Neg`, `INeg`, `Naf` | outside Core, which is Horn |
| `Exists` in the conclusion | needs a Skolem constant, which would be a name the rule does not contain |
| `Atom` of arity 0, or 3 and above | arity 3+ would have to be reified, which is a modelling decision the importer will not take on the author's behalf |
| a `rif:Import` directive | the imported document is not fetched, so the rule set it defines is larger than the rules read |
| the RIF presentation syntax | a different grammar. A half-written parser would mis-read rules rather than refuse them |

**A refusal fails the whole import by default, and no table is written.** The reason is the failure
this project attacks. A rule set that quietly lost half its rules still evaluates to a fixpoint, and
the certificate over what is left still checks green: a perfectly sound proof, about a rule set
nobody wrote. `--allow-partial` / `allow_partial: true` imports the rest anyway, and then the
response carries `certifies_a_weaker_rule_set: true`, a per-construct census under
`constructs_not_supported`, and every lost rule by name under `refused`. That is the same vocabulary
the DL model-certificate block uses for the constructs it does not model.

Two more things are checked per rule, and both refuse rather than guess. A head variable that does
not occur in the body is refused, because the engine would have to invent a term to bind it to. A
constant not in N-Triples spelling is refused, because it can never equal a term the store holds and
the rule would silently never fire. Both are enforced by rendering each imported rule to its
`rules.tsv` line and reading it back with the parser `reason --rules` will use, so what the checker
verifies and what the importer built are the same rule.

Variables are named by their local name when that identifies them. Two variable IRIs in one rule
with the same local name would become ONE variable in the table, joining two positions the author
kept apart, so a collision drops the whole rule to full IRIs instead.

## The verdict, which is why this is safe to build

Every rule a front end produces is a rule you wrote. Nothing discharges it against the RDF
semantics, so a certificate over such a table earns `entailed_under_supplied_rules` and names
`OOCert.horn_certificate_sound`: true in every model of the asserted graph THAT ALSO SATISFIES THOSE
RULES. `tests/fixtures/rules/family_swrl.ttl` contains the rule that makes the point, in SWRL: every
supplier is compliant. It is a valid SWRL rule, it is assumed and never checked, and a certificate
over a table containing it checks green for ever.

`oo-horn` awards `entailed` only to a table that renders identically to the built-in one, names
included. Every imported rule is named `swrl/…` or `rif/…`, and no built-in rule is, so a table out
of this importer can never be that table. That is structural rather than observed:
`no_front_end_can_name_a_rule_the_way_a_built_in_is_named` checks the naming against the committed
built-in table with no Lean present, and
`a_swrl_rule_never_earns_the_absolute_verdict` / `a_rif_rule_never_earns_the_absolute_verdict` take a
real rules file in each syntax all the way to the checker and assert the verdict it returns.

The importer itself states no verdict, for the reason `run_horn` gives: a second place that
pronounces is a second place the two verdicts can be confused. What it reports is which of the two a
table of its making is ELIGIBLE for, which is a fact about provenance and not a judgement on a
certificate.

## What this does not do

- No `owl:imports` chasing, and no fetching of `rif:Import`. What is read is the document in front
  of it.
- No datatype reasoning. `"01"^^xsd:integer` and `"1"^^xsd:integer` are different terms to the
  checker even though they denote the same value, so a data-valued atom derives less than its SWRL
  reading would. Deriving less is the sound direction, and it is stated rather than discovered.
- No RIF presentation syntax.
- SWRL variables must be declared `rdf:type swrl:Variable`. One that is not is read as an
  individual, which makes a rule that fires on nothing; a rule that ends up with no variables at all
  is flagged under `notes` for exactly that reason.
- Nothing is materialised into the store, here or in `reason --rules`. The certificate is the
  output.
