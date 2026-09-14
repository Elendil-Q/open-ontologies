# 0003 · A rule is data, and an assumption is not a fact

- **Status**: implemented · `lean/OOCert/Horn.lean` with `horn_certificate_sound` machine-checked ·
  `lean/OOCert/HornBuiltin.lean` discharges the engine's Horn rules against the semantics (27 table rows covering 25 W3C rules, since `scm-eqc1` and `scm-eqp1` each license two conclusions), giving
  `entails_of_builtin_horn` · checker `oo-horn`, gated by `tests/lean_horn_certificate_test.rs` and
  a CI leg · `reason --rules` emits Horn certificates, and `lean/OOCert/Mixed.lean` has landed
- **Written**: 2026-09-14
- **Related**: decision 0002 (an inference carries a certificate); the adversarial-SHACL assurance
  laundering work, which named the failure this decision is built to avoid

## The problem

`checkStep` had one arm per rule and `Soundness.lean` one lemma per arm. That is fine for a fixed
set of twenty and impossible for rules a user writes, and rules a user writes are the entire
logic-programming family: RIF Core, Datalog, SWRL, and any domain rule table a customer has.
Extending the checker rule by rule would mean a Lean edit per customer.

## Decisions

1. **Rules become data.** A `RulePattern` is a body and a head over triple patterns with variables.
   A certificate step cites a rule by index into a supplied table and gives a binding. `checkHornStep`
   verifies the binding instantiates the body into known triples and the head into the claimed
   conclusion. One generic arm replaces the per-rule ones.
2. **One theorem covers every rule table at once.** `horn_certificate_sound` needs no case analysis
   over rules, because there is no per-rule structure left in the checker. Axioms are
   `propext`, `Classical.choice`, `Quot.sound`, identical to the existing theorem. The trust surface
   does not grow.
3. **The built-ins are a rule table like any other.** Most of the engine's rules are Horn rules and are
   written out as data in `HornBuiltin.lean`, each with a one-line lemma deriving it from the
   semantic conditions. `cls-int1` and `cls-uni` are not Horn rules and stay as arms: their premise
   count is the length of an RDF list, which is data rather than fixed by the rule. That is not a gap
   in the generalisation, it is the exact boundary of the Horn family, and a user rule language will
   stop in the same place.
4. **The two verdicts never share a word.** A certificate over the built-ins yields `Entails`:
   true in every model of the asserted graph. A certificate over user rules yields `EntailsR`: true
   in every model that ALSO satisfies those rules. The rules are assumed and never checked, so a rule
   reading "every supplier is compliant" produces certificates that check green for ever. The checker
   prints `entailed` or `entailed_under_supplied_rules`, names a different theorem for each, and
   carries a digest of the table that was in force.
   `a_user_rule_never_earns_the_absolute_verdict` fails if that distinction is ever lost.
   Without it this layer is a machine for turning an assumption into a fact with a proof attached,
   which is the thing this project named and then had to find inside its own Lean layer once already.
5. **The digest identifies, it does not commit.** `String.hash` is not a cryptographic hash. It
   exists so two reports can be compared, not so one can be defended against someone who controls
   the rule file. Anyone needing that should hash the file.

## What this does not claim

The checker says a conclusion follows from the premises by the cited rule. It says nothing about
whether the rule is true, whether the rule set is consistent, or whether the asserted graph is
accurate. Under a user table the guarantee is conditional on assumptions the user wrote, and the
report says so in the verdict rather than in a footnote.

## Since written

Both items listed here as not done have landed. `reason --rules` evaluates a supplied table and
emits a certificate, and `Mixed.lean` lets one certificate carry both built-in arms and Horn steps,
which needed `Soundness.lean` generalised from `Entails G` to `EntailsIn P` across about twenty
cases. The engine's rule count has since grown; the checker covers 29 of the OWL 2 RL profile's 78
rules, 30 counting `cax-dw` in the refutation layer, and four of them stay as hand-written arms
because their premise count is the length of an RDF list.

## The family is now covered in fact and not only in architecture

This decision said the logic-programming family — RIF Core, Datalog, SWRL — was the reason to make
rules data. For a while that was true of the checker and false of the product: the only rule syntax
anything here could read was `rules.tsv`, which is an internal encoding and not a language anybody
writes in, and grep found no mention of SWRL or RIF outside this file. A user holding a rules file
in a standard syntax could use none of it.

`src/rulesyntax.rs` and `rules-import` / `onto_rules_import` close that. SWRL is read out of a
loaded RDF graph through the `swrl:Imp` encoding, reusing the one `rdf:first`/`rdf:rest` reader the
DL parser already had; RIF Core is read out of its normative XML syntax. Datalog is deliberately NOT
offered as a front end, because it has no single standard concrete syntax and a Datalog program over
triples IS a `rules.tsv` table.

Three things follow from decision 4 and are not negotiable in that code:

1. **Both front ends produce USER tables.** Every rule is named `swrl/…` or `rif/…`, no built-in
   rule is, and `oo-horn` awards `entailed` only to a table that renders identically to the
   built-in one. So an imported table structurally cannot earn the absolute verdict.
   `a_swrl_rule_never_earns_the_absolute_verdict` and its RIF twin are the front ends' copies of
   `a_user_rule_never_earns_the_absolute_verdict`, and they run the whole pipeline into `oo-horn`.
2. **A rule that cannot be represented is refused by name and counted.** Both languages exceed a
   Horn table: SWRL has built-in atoms, same- and different-individual atoms and data ranges; RIF
   Core has equality, External, `Expr`, `rif:local` and list terms. By default ONE refusal fails the
   whole import and no table is written, because a rule set that quietly lost half its rules still
   reaches a fixpoint and its certificate still checks green — a sound proof about a rule set nobody
   wrote, which is the laundering failure in its purest form. `allow_partial` is the opt-in and sets
   `certifies_a_weaker_rule_set`, the name the DL model-certificate block already uses for the same
   idea.
3. **The supported fragment is stated, never implied.** `docs/rule-syntax-front-ends.md` and every
   response carry it. "SWRL is supported" would be the false claim this decision exists to prevent
   one level up.

## Still not done

- Nothing in `src/` writes the refutation format, so inconsistency can be checked and not yet
  produced by this engine.
- The RIF presentation syntax is not parsed. It is refused by name; a half-written parser for it
  would mis-read rules rather than refuse them.
