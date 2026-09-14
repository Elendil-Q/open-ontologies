# 0003 · A rule is data, and an assumption is not a fact

- **Status**: implemented · `lean/OOCert/Horn.lean` with `horn_certificate_sound` machine-checked ·
  `lean/OOCert/HornBuiltin.lean` discharges 19 of the engine's rules against the semantics, giving
  `entails_of_builtin_horn` · checker `oo-horn`, gated by `tests/lean_horn_certificate_test.rs` and
  a CI leg · **the Rust reasoner does not yet emit Horn certificates**, and
  `lean/OOCert/Mixed.lean` is deferred (see Not done)
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
3. **The built-ins are a rule table like any other.** 19 of the engine's rules are Horn rules and are
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

## Not done

- The Rust reasoner cannot yet evaluate a supplied rule table or emit a Horn certificate, so today
  the layer checks certificates rather than producing them. That is the next piece.
- `Mixed.lean`, which lets one certificate carry both built-in arms and Horn steps, needs
  `Soundness.lean` generalised from `Entails G` to `EntailsIn P`. The change is mechanical across
  about twenty cases and was deferred rather than rushed. Until it lands, a user-rule certificate
  cannot also cite `cls-int1` or `cls-uni`.
