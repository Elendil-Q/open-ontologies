# 0008 · A binding is data, and evidence admits one reading

- **Status**: implemented · `lean/OOCert/Horn.lean`, where `bindingWellFormed` is a conjunct of
  `checkHornStep`, and `wellFormed_determines_instantiation` is the theorem that says what it
  buys · `horn_certificate_sound`, `horn_certificate_sound_fo` and `SatRuleFO.to_SatRule` are
  unchanged in statement and in axiom footprint · `isabelle/OO_Check.thy` is UNTOUCHED, because
  it was written independently and that independence is the whole value · the refusal can fail
  in Lean
  (`rejects_duplicate_binding_key`, `rejects_binding_that_omits_a_rule_variable` in
  `HornWitness.lean`) and on the real bytes
  (`tests/cross_kernel_differential_test.rs::resolved_d1_*`, `::resolved_d2*`) · the producer is
  proved unable to emit either shape by
  `tests/reason_horn_emit_test.rs::no_emitted_binding_is_one_the_format_now_refuses`
- **Written**: 2026-09-14
- **Related**: decision 0003 (a rule is data, and an assumption is not a fact), whose format this
  amends; decision 0002 (an inference carries a certificate)
- **Not run in CI.** The differential needs Isabelle2025-2 and Poly/ML, which the workflow does not
  install, so `cargo test --test cross_kernel_differential_test` is a LOCAL gate and the 47-to-0
  number is reproduced by running it, not by a green badge. `lean_horn_certificate_test` and
  `reason_horn_emit_test` do run in CI and carry the Lean-side and producer-side halves.

## The problem

The repository carries two verified checkers for one Horn certificate format: the Lean in
`lean/OOCert/Horn.lean` and an independent Isabelle/HOL formalisation in `isabelle/`, written from
the W3C sources with the Lean deliberately unread. Run over 1,718 certificates they agreed on 1,671
and disagreed on 47, always in the same direction, with one root cause:

**Isabelle validates the binding list as a data structure and Lean did not.** Isabelle's
`check_step` requires `distinct (map fst b)` and `binding_covers b r` before it instantiates
anything. Lean's `substOf` was `fun v => (List.lookup v l).getD v`, which turns any binding list
into a total function with a silent default, and it was applied without the list being inspected
at all.

Neither checker was unsound, and saying so is not a softening. Lean's soundness theorem quantifies
over whatever total substitution it built, so every acceptance held in its own theorem; Isabelle's
extra rejections were false alarms, which is the harmless direction. **The defect was in the
FORMAT.** Nothing in `docs/lean-certificates.md` or decision 0003 said what a repeated binding key
meant or what an incomplete binding meant, so two readings of the same bytes were both defensible
and a certificate's validity depended on which verified checker read it.

Two files make it concrete.

`isabelle/fixtures-added/bad_dup_key.tsv` binds `x` twice, first to `<http://ex.org/a>`, which makes
the step check, and then to `<http://ex.org/zzz>`, which does not. Lean returned exit 0 and the
ABSOLUTE verdict `entailed`. Isabelle returned `binding_dup_key`. Which one was right turned on
`List.lookup` being first-wins: a tie-break inside a standard-library function standing in for a
rule about a file format, deciding whether a certificate is valid.

`isabelle/fixtures-differential/unsafehead_cert.tsv` cites the rule `?s <p> ?o -> ?s <q> ?z` over
one ordinary triple of IRIs, binds `s` and `o`, and omits `z`. Lean accepted a conclusion whose
object was the bare term `z`, which is not an IRI, not a blank node, not a literal and not
writable RDF, minted out of a variable's NAME in the rule file. Nobody wrote that term. The fuzzer
then found the same hole through a one-character typo (`?o` became a bare `?`, read by both parsers
as a variable whose name is the empty string), which is what settles the objection that the first
case was contrived.

## The decision

**A binding list is DATA before it is a substitution, and a malformed binding is refused rather than
repaired.** `checkHornStep` now requires, of the binding and the rule it cites:

1. **Distinct keys.** A repeated key is refused.
2. **Coverage.** Every variable the cited rule mentions, in the body AND in the head, has a binding.

Both refusals are strictness with no soundness content, and that is the point. What they buy is a
sentence a soundness theorem cannot say: the certificate means ONE thing.
`wellFormed_determines_instantiation` states it and the kernel checks it. Once the binding is well
formed for the cited rule, every total substitution that extends it instantiates that rule the same
way, so a checker carrying the binding as a partial map and one carrying it as a total function with
a default are reading the same certificate.

### Why refusing, rather than writing the permissive reading into the format

Both questions had a permissive answer available, and both were rejected on the same ground: the
permissive reading costs nothing to give up and buys a second meaning.

On the **repeated key**, the alternative was to make first-wins normative. One sentence would have
made the format determinate, so this is a real option and not a straw man. It is the wrong one.
First-wins is not "the natural implementation", because there is no such thing. Of the four
association-list primitives an implementer is most likely to reach for, two are first-wins
(`List.lookup` in Lean, `map_of` in Isabelle) and two are last-wins (`dict(pairs)` in Python,
`HashMap::from_iter` in Rust, both of which insert in order and let the later value win). A
normative first-wins rule would therefore be broken by half the primitives on that short list, and
broken SILENTLY, by accepting a certificate that means something else. `distinct` has no such
split: every language has it, and getting it wrong is loud. Against that, a duplicate key carries no
information a producer needs, since there is no certificate writable with one that is not writable
without one, so refusing costs exactly nothing.

On the **incomplete binding**, the argument is sharper, because on the question of ENTAILMENT the
permissive reading was right and Isabelle was the incomplete one. `EntailsR` quantifies over every
total substitution, so a step whose body instantiates into known triples under SOME total
substitution really does entail its conclusion. The refusal is therefore a deliberate choice of
well-formedness over completeness, and it is the right one for two reasons. First, the permissive
reading does not merely admit more certificates: it FABRICATES a term out of a variable's name and
puts it in the conclusion, so what the certificate says depends on a rule file's choice of
identifier. Second, and this is what makes the trade free, it loses no certificate anybody meant. A
step whose binding omits a variable can always be rewritten with that variable bound to the term the
conclusion already shows, and the rewritten step is accepted by both kernels.
`the_repair_is_accepted` in `HornWitness.lean` and
`the_refusal_costs_no_certificate_anybody_meant` in the differential are that claim, run.

### What is NOT refused

**A binding for a variable the cited rule never mentions is accepted.** It is never consulted, so it
cannot make a step mean two things, and there is no second reading to remove. Refusing it would be a
tidiness rule dressed as a determinacy one. Both kernels already agreed here
(`probe_extrabind`, exit 0 on both) and they still do.

## What this does not claim

**This decision does not make a conclusion writable RDF.** Binding `z` to the bare term `z` is now
required and still accepted, so a certificate can still conclude a triple no serialiser can write.
What changed is that the term must be WRITTEN by the certificate's author rather than minted by the
checker. Whether the format should additionally require every term to be well-formed N-Triples is a
separate question, it is not answered here, and `the_refusal_costs_no_certificate_anybody_meant`
exists partly so that the boundary is visible rather than assumed away.

It also does not add a theorem to `horn_certificate_sound`. That statement is unchanged, its proof
below the first line is unchanged, and the new conjunct is destructured and discarded. Adding a
check makes `checkHornStep = true` a STRONGER hypothesis, so the theorem cannot have been
weakened to accommodate it. The accounting runs the other way, and it is the accounting that
matters: a checker that refuses more is trivially easier to prove sound, so the evidence that this
one still accepts anything lives in `HornWitness.lean` and in the differential's floor of 20
mutually accepted certificates, not in the soundness theorem.

## What moved, and what deliberately did not

The **Lean moved**. The Isabelle was written from the specifications without reading it, and editing
it to agree would spend the only thing the second kernel is for. Where the two now differ is a new
finding and belongs in a report, not in a patch to whichever side is easier to change.

A property proved inside one formalisation is not a property of the format, and this is the case
that showed it. Isabelle's `coverage_implied` proves that removing its coverage check cannot change
its accept/reject bit. That is true of Isabelle, whose instantiation is partial, so a missing
binding kills the step anyway. It does not transfer: Lean's instantiation is total, so the same
check is load-bearing there and in the opposite direction.

## The numbers

Before, over 1,718 certificates (61 base, 1,291 mutated, 366 fuzzed, fuzz seed `0xd1ffed0001`):

    both accept:      349
    both reject:      857
    both exit 2:      465
    known divergence: 47
    unexplained:      0

After:

    both accept:      349
    both reject:      904
    both exit 2:      465
    divergent:        0
    malformed binding, refused by both (decision 0008): 286

The 47 moved into rejected-by-both and nowhere else: 857 plus 47 is 904, and the accepted and
unparseable counts did not move. The 286 is larger than 47 because most rows carrying a malformed
binding were already rejected by both kernels for some other reason; the gate runs on every row
rather than only on the ones that disagree, because a check that ran only on divergences could be
satisfied by silence.

## Since written

Nothing yet.
