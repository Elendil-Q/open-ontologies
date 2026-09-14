# Derivation certificates and the Lean checker

Every inference the forward-chaining reasoner makes can be written out with the rule that
produced it and the premises the rule read, and a checker in `lean/` verifies that record against a
formal semantics. The checker's soundness is a machine-checked theorem, so a certificate it accepts
contains only triples entailed by the asserted graph, whatever the Rust engine did to find them.

This page is the how-to. The design and its limits are in
[decision 0002](decisions/0002-an-inference-carries-a-certificate.md).

## Produce a certificate

```bash
# CLI: any of rdfs, owl-rl, owl-rl-ext. The tableaux path (owl-dl) refuses the flag.
open-ontologies load ontology.ttl
open-ontologies reason --profile owl-rl-ext --certificate /tmp/cert

# Batch, when the store is in-memory per process:
printf 'load ontology.ttl\nreason --profile owl-rl-ext --certificate /tmp/cert\n' \
  | open-ontologies --no-connect --data-dir /tmp/store batch -
```

Over MCP, `onto_reason` takes `certificate_dir`. The response gains a `certificate` object:

```json
{
  "inferred_count": 268,
  "certificate": {
    "dir": "/tmp/cert",
    "format": "oo-cert/1",
    "asserted": 1128,
    "derivations": 268,
    "by_rule": {"rdfs2": 41, "rdfs9": 190, "scm-eqc1": 3, "...": "..."},
    "check_with": "cd lean && lake exe oo-cert <dir>/asserted.tsv <dir>/derivations.tsv"
  }
}
```

`derivations` always equals `inferred_count`: one line per inferred triple, recorded the first time
it is derived.

## Check it

The checker needs a Lean 4 toolchain. [elan](https://github.com/leanprover/elan) installs the
version `lean/lean-toolchain` pins; nothing else is downloaded, the project has no dependencies.

```bash
cd lean
lake build                      # builds the checker AND checks the proofs
lake exe oo-cert /tmp/cert/asserted.tsv /tmp/cert/derivations.tsv
```

Exit codes: `0` every step checks; `1` a step was rejected, and the JSON on stdout names the first
one with its rule, conclusion and premises; `2` a file could not be read or parsed.

```json
{"ok":true,"asserted":1128,"derivations":268,"theorem":"OOCert.certificate_sound"}
```

## The files

Tab-separated. Terms are in N-Triples spelling, exactly as the engine's interner holds
them, so a term is spelled identically wherever it appears and tabs and newlines cannot occur
inside one.

- `asserted.tsv`: one triple per line, `s TAB p TAB o`. Every triple the run started from.
- `derivations.tsv`: one step per line, `rule TAB s TAB p TAB o` for the conclusion, then the
  premises as further triples, in the order documented per rule in `lean/OOCert/Rules.lean`.
- `refutation.tsv`, only when the run found a contradiction it can certify: the line `oo-refute/1`,
  then the derivation steps that reached the clash in the same spelling as `derivations.tsv`, then
  one `refute TAB rule` line with the clash rule's premises. See the refutation section below.

## What is proved

`OOCert.certificate_sound` in `lean/OOCert/Soundness.lean`:

> if `checkCert G steps = true` then for every step, `G ⊨ step.conclusion`

where `G ⊨ t` is truth in every model of `G` under the semantics in `lean/OOCert/Semantics.lean`:
the RDF-based reading of the twenty rules' vocabulary, with each semantic condition the *if*
direction of the W3C condition or a consequence of it, never more. Weaker conditions admit more
interpretations, so the result carries over to the OWL 2 RDF-Based Semantics and to the Direct
Semantics read through triples.

The axioms the theorem depends on are pinned in the source by `#guard_msgs`:
`propext`, `Classical.choice`, `Quot.sound`. A `sorry`, or a `native_decide`, fails `lake build`.

## Why the theorem is not vacuous

A soundness theorem about an unsatisfiable semantics proves nothing: if no interpretation met the
conditions, every triple would be entailed and the checker could accept anything. `lean/OOCert/Witness.lean`
closes that by construction, and its own axiom lists are pinned the same way.

| theorem | says |
|---|---|
| `saturated_is_a_model` | every graph has a model, so the conditions are satisfiable and no graph is inconsistent here |
| `not_everything_is_entailed` | some triple is not entailed, so `Entails` is not the trivial relation |
| `the_old_svf_derivation_is_not_entailed` | `C ⊑ ∃p.D` with `x p y` and `y ∈ D` does **not** entail `x ∈ C` |
| `the_sound_half_survives` | the same premises **do** entail `x ∈ ∃p.D`, so the fix did not overshoot |

The third is the one worth reading. It is a machine-checked refutation of the derivation this engine
used to make: a model of the premises in which `x` is not a `C`. So the removed rule was unsound in
fact, not merely unjustified by the rule set the checker implements. The witness is the Herbrand
interpretation of the premises plus the single consequence the semantics does force.

## What is not proved

- Completeness. The checker rejects anything it cannot re-derive by pattern, including valid
  inferences in an order it does not expect. A rejection is a false alarm at worst, never a false
  pass.
- The parser and the file format (`lean/OOCert/Parse.lean`, `lean/Main.lean`). A parse error
  rejects.
- Anything outside the forward-chaining family: the SHACL validator (the pyshacl differential in
  `tools/shacl_differential.py` is its gate), the SHIQ tableaux reasoner, the RDF parsers.
- Datatype semantics. Two spellings of one literal value are two terms. No rule compares literals
  by value, so nothing is lost, but do not read `Entails` as datatype-aware.

## What it caught on day one

An adversarial audit of the whole layer on 13 September 2026 found nine more defects, seven of them
predating the certificate work: a false clean from unscoped prefix declarations, an ignored
`sh:deactivated`, a truncation that silently disabled any constraint mentioning a typed literal, a
blank-node shape acting as a wildcard, a reasoner that was not a fixpoint, four rules that could
emit an unserialisable triple, and a CI job that could not pass. All are fixed and pinned; the
CHANGELOG lists them.

`cls-svf1` in the `owl-rl-ext` profile derived `x rdf:type C` from `C rdfs:subClassOf ∃p.D`,
`x p y` and `y rdf:type D`. That is the converse of the axiom. It also treated `x p D`, with `D` the
filler class IRI itself, as a witness. Neither has a sound rule, so neither could be given one in
the checker, and both are gone (`tests/reason_rl_ext_soundness_test.rs`). The old derivation is
kept in `tests/lean_certificate_test.rs` as a forged certificate the checker must reject.

## In CI

The `lean` job builds `lean/` (which is the proof check), then runs
`tests/lean_certificate_test.rs` with `OO_REQUIRE_FIXTURES=1`. Every RDF file the repository
tracks, enumerated from `git ls-files`, is loaded, reasoned under `owl-rl-ext` with a certificate,
and the certificate checked: 122 files and 37,133 derivations at the time of writing. Files over
4 MB and files that do not parse are listed with the reason, never dropped silently. The same test
appends three forgeries and requires each to be rejected.

The corpus used to be five hand-named directories, three of which hold no RDF, so 46% of the
repository's RDF was never walked and was excluded without being named. Widening it is what
surfaced the literal-subject defect in `prp-symp`, `prp-inv1`, `prp-inv2` and `eq-sym`, which lived
in `benchmark/`.

## Refutations: certifying that a graph has NO model

A derivation certificate says a triple follows. A *refutation* says the graph contradicts itself, and
it needs a second format because there is no triple to conclude. `lean/OOCert/Refute.lean` holds it,
`oo-refute` checks it, and `OOCert.refutation_sound` is proved about it.

The reasoner now writes one. `reason --certificate DIR` looks for a contradiction in the closure it
reached and, when it finds one the checker can judge, writes `DIR/refutation.tsv` beside the other
two files.

```bash
open-ontologies reason --profile owl-rl --certificate /tmp/cert
cd lean
lake exe oo-refute check /tmp/cert/asserted.tsv /tmp/cert/refutation.tsv
lake exe oo-refute guard /tmp/cert/asserted.tsv /tmp/cert/derivations.tsv /tmp/cert/refutation.tsv
```

`check` exits 0 when the refutation is valid, which is a good exit code reporting bad news. `guard`
runs both checkers and REFUSES the derivation certificate when the refutation succeeds, because over
a refuted graph every triple is entailed under the disjointness reading and an ordinary certificate
carries no information (`OOCert.a_certificate_adds_nothing_when_the_graph_is_refuted`). `oo-cert`
will still accept that certificate and will still be telling the truth: its verdict quantifies over
a model class that ignores disjointness, and that class is never empty.

The response gains an `inconsistency` object:

```json
{
  "inconsistency": {
    "found": true,
    "verdict": "clash_found_by_this_engine",
    "checked_by_lean": false,
    "by_rule": {"cax-dw": 1},
    "refutation": {
      "written": true,
      "rule": "cax-dw",
      "prefix": 2,
      "verdict": "refutation_written_not_yet_checked",
      "check_with": "cd lean && lake exe oo-refute check /tmp/cert/asserted.tsv /tmp/cert/refutation.tsv"
    }
  }
}
```

**Read the two verdicts apart.** `clash_found_by_this_engine` is this engine saying so, with nothing
behind it. `unsatisfiable_under_disjointness` is what `oo-refute` prints when it has ACCEPTED a
refutation, and the engine never states it.
`tests/lean_refutation_producer_test.rs::the_engine_never_states_the_checkers_verdict` fails if any
string in the response is ever that verdict, on the pattern the Horn layer's laundering guard set.

### Which rules conclude `false`, and which of them can be certified

Seventeen rules of the OWL 2 RL profile conclude `false` rather than a triple. None of them is in the
forward-chaining table, and none could be: a certificate step's conclusion is a triple. They are
looked for once, after the fixpoint.

| rule | detected | certifiable |
|---|---|---|
| `cax-dw` (`c1 owl:disjointWith c2`, `x a c1`, `x a c2`) | yes | **yes** |
| `cls-com` (`owl:complementOf`) | yes | no |
| `cls-nothing2` (`x a owl:Nothing`) | yes | no |
| `cls-maxc1` (`owl:maxCardinality 0`) | yes | no |
| `eq-diff1` (`owl:sameAs` and `owl:differentFrom`) | yes | no |
| `prp-irp` (`owl:IrreflexiveProperty`) | yes | no |
| `prp-asyp` (`owl:AsymmetricProperty`) | yes | no |
| `prp-pdw` (`owl:propertyDisjointWith`) | yes | no |
| `prp-npa1`, `prp-npa2` (negative property assertions) | yes | no |
| `cax-adc`, `prp-adp`, `eq-diff2`, `eq-diff3` | no, they read an RDF list | no |
| `cls-maxqc1`, `cls-maxqc2` | no, qualified cardinality is not implemented | no |
| `dt-not-type` | no, an ill-typed literal needs a datatype value space | no |

Only `cax-dw` is certifiable, and the reason belongs to the checker rather than to the engine.
`OOCert.RefuteConditions` carries exactly one semantic field, for `cax-dw`, and `oo-refute` refuses a
refutation naming any other clash rule with exit 2 rather than guessing at it. So the producer writes
a refutation for that rule alone. For the other nine it detects, the response says a clash was found
and `"refutation": {"written": false}` with the reason. Every rule the engine does not look for is
listed in `rules_not_detected` with its own reason, so a run with no clash is never a consistency
result: most of the table was not tried.

`lean/OOCert/Refute.lean` says sixteen rules conclude `false`. Counted against the W3C tables it is
seventeen; the difference is `dt-not-type`, which that file excludes elsewhere on the stated ground
that the Lean semantics has no datatype value space. Nothing computes with the number.

### The limit, which is real

`cax-dw` needs an INDIVIDUAL in two disjoint classes. A TBox that is unsatisfiable with no individual
asserted cannot be seen this way at all. `:Lion rdfs:subClassOf :Carnivore, :Herbivore` with those
two disjoint makes `:Lion` unsatisfiable, and until something is asserted to BE a `:Lion` the
rule-based route has nothing to fire on. That is a boundary of forward chaining, not a defect in the
producer.

The SHIQ tableau (`--profile owl-dl`, `src/tableaux.rs`) does see it, and reports
`unsatisfiable_classes`. **Its answer carries no certificate**, which its own report already states
(`"not_covered": "unsatisfiability and inconsistency carry no certificate"`). No refutation is
emitted from it, and the obstruction is precise rather than a matter of effort:

- `oo-refute/1` can express exactly one contradiction, `cax-dw`, whose three premises must each be
  asserted or concluded by a step of the 29-rule forward-chaining prefix. A tableau clash reached
  through `∃`/`∀` expansion, node merging or a cardinality bound is not three triples of that shape
  and there is nothing in the format to write it as.
- Where a tableau clash IS a `cax-dw` instance over triples the forward-chaining rules can reach, the
  rule-based producer has already found it, so the tableau adds nothing that can be certified.
- Feeding the tableau's inferred subsumptions back into the store and re-reasoning would let more
  clashes surface, but those subsumptions would then appear in `asserted.tsv` as axioms with nothing
  marking them derived. That is the assumption-laundering failure this layer exists to prevent, so it
  is not done.
- Adding a clash rule to the format means a new field in `OOCert.RefuteConditions`, a new arm in
  `OOCert.checkRefuteStep` and a new soundness case. That is a change to `lean/`, not to the producer.

`tests/lean_refutation_producer_test.rs::the_tbox_only_case_is_invisible_here_and_the_tableau_sees_it`
computes this boundary on one ontology rather than asserting it here.

`onto_defects` asks a different question again, and the three do not substitute for one another.
It checks the ontology against ITSELF with no data present, so `disjoint_with_ancestor` and
`inherited_disjoint` catch the schema that will contradict itself the moment an instance arrives.
This layer needs the instance to be there. The tableau needs neither and certifies nothing.

## User-written rules

The twenty built-in rules were twenty arms in the checker, which does not extend to rules you write.
`lean/OOCert/Horn.lean` makes a rule into data: a body and a head over triple patterns with
variables. A certificate step cites a rule by index into a table you supply and gives a binding, and
one theorem, `OOCert.horn_certificate_sound`, covers every rule table at once.

```bash
cd lean
lake build
lake exe oo-horn rules                                    # the built-in table, as data
lake exe oo-horn check RULES.tsv ASSERTED.tsv HORN.tsv    # check a certificate
```

**The verdict tells you what it is relative to, and you must read it.**

| table | verdict | theorem | means |
|---|---|---|---|
| exactly the built-ins | `entailed` | `OOCert.entails_of_builtin_horn` | true in every model of the asserted graph |
| anything else | `entailed_under_supplied_rules` | `OOCert.horn_certificate_sound` | true in every model that **also satisfies your rules** |

The second is weaker and the difference is not academic. A rule reading "every supplier is
compliant" makes certificates that check green for ever, because the certificate certifies the
inference and never the premises. The report carries a digest of the table that was in force so two
runs can be compared, and `tests/lean_horn_certificate_test.rs` fails if a user-rule run ever
reports the absolute verdict.

Twenty-seven of the engine's rules are Horn rules and appear in the built-in table, the count
`the_built_in_rules_are_emitted_as_data` pins. Four are not: `cls-int1`, `cls-int2`, `cls-uni` and
`cls-oo` each read an RDF list off the graph, so the LIST is a premise and the premise count is data
rather than fixed by the rule. They remain hardcoded arms. A user rule language stops at the same
boundary.

`reason --rules TABLE --certificate DIR` evaluates a supplied table to a fixpoint over the loaded
graph and writes the three files `oo-horn check` reads. Nothing is materialised: a conclusion drawn
under a table nobody has checked holds only in models that satisfy that table, and writing it into
the store beside the assertions would lose exactly that distinction. See
[decision 0003](decisions/0003-a-rule-is-data-and-an-assumption-is-not-a-fact.md).

## Rules you wrote in SWRL or RIF Core

`rules.tsv` is an internal encoding, not a language anybody writes in. `rules-import` reads two
standard rule syntaxes into it.

```bash
open-ontologies load ontology.ttl
open-ontologies rules-import --from swrl --out rules.tsv              # SWRL, out of the loaded graph
open-ontologies rules-import --from swrl --file rules.owl --out rules.tsv
open-ontologies rules-import --from rif  --file rules.xml --out rules.tsv
open-ontologies reason --rules rules.tsv --certificate cert/
cd lean && lake exe oo-horn check ../cert/rules.tsv ../cert/asserted.tsv ../cert/horn.tsv
```

**Only part of each language is a Horn table over triple patterns, and the exact fragment is in
[docs/rule-syntax-front-ends.md](rule-syntax-front-ends.md) and in every response.** A rule outside
it is named, counted and refused; by default one refusal fails the whole import and writes nothing,
because a table that quietly lost a rule still reaches a fixpoint and still produces a certificate
that checks green, which is a sound proof about a rule set nobody wrote. `--allow-partial` imports
the rest and flags the result `certifies_a_weaker_rule_set`.

Every imported rule is a rule you wrote, so it lands on the second row of the table above without
exception: imported rules are named `swrl/…` and `rif/…`, no built-in rule is, and `oo-horn` awards
the absolute verdict only to a table that renders identically to the built-in one.

## Known limitations

Stated rather than discovered later.

- **The rule table is this engine's, not W3C's.** `by_rule` describes what this engine did. It is
  not an OWL 2 RL conformance claim, and the engine does not implement every rule in the profile.
- **`asserted.tsv` is the store, not your file.** Quads are flattened, so a triple present in two
  named graphs appears on two lines. Literals are in the store's post-parse canonical spelling, so
  `"01"^^xsd:integer` is written `"1"^^xsd:integer`. The guarantee is relative to that file.
- **Reasoning twice into one store.** The run now reaches a fixpoint, so a second run adds nothing,
  but if you materialise into a store that already held inferences they appear in `asserted.tsv` as
  assumptions with nothing marking them derived. Use `inference_graph: true` (decision 0001) when
  that distinction matters.
- **No clash found is not consistency.** Seven of the seventeen clash rules are not looked for at
  all and eight of the ten that are cannot be certified, so a clean `reason` run means "none of the
  ten rules tried fired", never "this ontology is consistent". A rejected refutation means the same:
  `oo-refute`'s own report says so in every verdict it prints.
- **One clash is reported per refutation, and only the first certifiable one is written.** A graph
  with twenty disjointness clashes gets one `refutation.tsv`. `clash_count` and `by_rule` carry the
  rest; ten are listed in full under `clashes`. Refuting a graph once is enough to invalidate every
  derivation over it, so a second refutation would add nothing.
- **The refutation's derivation prefix is not byte-stable across runs.** Which of several valid
  derivations of a premise the fixpoint recorded first depends on the same hash iteration order that
  already decides the line order of `derivations.tsv`. The contradiction itself IS stable: clashes
  are sorted on their N-Triples spelling before one is chosen.
- **A SHACL report double-counts a node selected by two target declarations of one shape.** Both
  `focus_nodes` and `violation_count` are affected. Collapsing identical results is not the fix:
  SHACL emits one result per SPARQL solution, pyshacl does too, and deduplicating breaks an exact
  agreement with it. The fix is to union a shape's focus nodes across its declarations, which is a
  change to the evaluation loop and is not done.
