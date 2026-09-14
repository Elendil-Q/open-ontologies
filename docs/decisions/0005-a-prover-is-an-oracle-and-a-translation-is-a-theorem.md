# 0005 · A prover is an oracle, and a translation is a theorem

- **Status**: implemented · `src/tptp.rs`, `fol --out DIR --format tptp|clif`, `onto_fol_export` ·
  correspondence pinned by `tests/fol_translation_correspondence_test.rs` (31 tests) ·
  differential in `tools/fol_differential.py`, run against E 3.2.5 · the translation mirrors
  `OwlLean/Translation.lean` in the sibling `owl-lean` project, whose `OwlLean.adequacy` is
  machine-checked with axioms `propext`, `Classical.choice`, `Quot.sound` · **the Rust-to-Lean
  correspondence is pinned by tests and is NOT proved**
- **Written**: 2026-09-14
- **Related**: decision 0002 (an inference carries a certificate), which this decision is the
  boundary of; `tools/shacl_differential.py`, whose treatment of pyshacl this copies exactly

## The problem

There is a problem on each side of this work, and they pull in opposite directions.

An OWL-to-first-order exporter is easy to write and hard to justify. FOWL
validated its mapping empirically over 168 consistent ChEBI modules. Hets proves its OWL-to-CASL
comorphism on paper, through the institution satisfaction condition. LATIN's `OWL2toFOL.elf` is
type-checked by Twelf, which is no longer maintained, and has its cardinality constructors and
`objectPropertyChain` commented out. So an exporter can emit a plausible file and nobody, including
its author, can say what the file means.

The opposite temptation arrives with the output. Once an ontology is in TPTP, a prover will answer questions
about it, and the answers look like proofs. They are not. Decision 0002 lets this engine say an
inference is *checked*, because `lean/` holds a checker whose soundness is a machine-checked
theorem and the certificate is small enough to re-derive. A superposition refutation is not like
that. Checking one needs a verified first-order calculus with unification, which does not exist in
core Lean. Treating a prover's `SZS status Theorem` as a certificate would undo the distinction
decision 0002 exists to draw, inside the same codebase, one layer up.

## Decisions

1. **The exporter emits the translation a machine-checked theorem is about.** The sibling project
   `owl-lean` proves `OwlLean.adequacy`: for an ontology `O` and an axiom `a`,
   `Entails O a ↔ FOL.Entails (background ++ indAxioms inds ++ O.map trAx) (trAx a)`, no `sorry`,
   no Mathlib, axioms `[propext, Classical.choice, Quot.sound]`. `src/tptp.rs` transcribes `tr`,
   `trAx`, `background` and `indAxioms` function for function. Nothing is normalised, simplified or
   optimised on the way out: `⊤` fillers still emit `$true` conjuncts, because the file has to
   carry the formula the theorem is about rather than one equivalent to it.
2. **The correspondence is pinned by tests and is not proved, and the output says so.**
   Nothing mechanically checks that `Translation::axiom` is `OwlLean.trAx`. What exists is
   `tests/fol_translation_correspondence_test.rs`, whose expected strings are computed BY HAND from
   `OwlLean/Translation.lean` rather than recorded from a run: a golden file captured from the
   emitter would agree with the emitter by construction and would catch nothing. The claim appears
   in the module docs, in the JSON report, and in the header of every emitted file, because a limit
   stated only in a README gets read without one.
3. **What the theorem needs is handled, not assumed.** `tr_bridge` holds only under
   `Fresh n x`, and `OwlLean.Refutations.tr_bridge_needs_freshness` is a machine-checked
   countermodel where the existential `tr` allocates captures its own subject variable. The
   exporter never chooses a counter: every entry goes through `Translation::concept_fresh`, which
   refuses unless `x < c`, and the call sites reproduce `trAx`'s own `tr c 0 2`, `tr c 1 2`,
   `tr c 0 1`. Separately, `background` alone does not force a constant to denote an object, and
   `OwlLean.Refutations.adequacy_needs_ind_axioms` refutes adequacy outright with the empty
   ontology and `⊤(a)`; `indAxioms`, i.e. `thing(a)` for every individual name, is the fix and is
   emitted. Both were real defects found while proving the theorem.
4. **What is not exported is named in the output.** `exports_a_weaker_axiom_set` and
   `constructs_not_exported` carry every construct outside the fragment with its count and the
   reason, the same shape as `certifies_a_weaker_axiom_set` on the description-logic layer. A
   construct rewritten into the fragment before translation, such as `owl:AllDisjointClasses` or
   `owl:equivalentProperty`, is listed under `reduced_to_fragment` rather than passed off as
   native. Annotations are counted separately, because an annotation carries no Direct Semantics
   content and folding 206 `rdfs:label` triples into the drop list would bury the sixteen
   constructs that do weaken the axiom set.
5. **An ATP verdict is an oracle opinion and is labelled as one everywhere it appears.**
   `tools/fol_differential.py` runs the engine's claimed entailments past E or Vampire and reports
   `AGREE`, `CLAIMED_NOT_ENTAILED`, `WEAKER_EXPORT`, `UNDETERMINED`, `ATP_ERROR` or `NOT_ASKED`. A
   disagreement is a bug in one of the two and the tool's job is to say so, not to adjudicate.
   `UNDETERMINED` is never collapsed into agreement: the translated theory is not decidable in
   general and a non-entailment often has only infinite countermodels. The word "proved" appears
   nowhere next to a prover's answer.
6. **A disagreement caused by the fragment is separated from a disagreement caused by a bug, and
   the separation is computed rather than guessed.** OWL TIME derives a class assertion from a
   data-property assertion, and GoodRelations derives a range from a data-property hierarchy;
   neither has a constructor in `OwlLean/Syntax.lean`, so the exported theory genuinely does not
   entail those conclusions and the prover is right to say so. Calling that a bug would send a
   reader hunting a defect that was a stated limitation. Every triple in the certificate is put to
   the exporter as a goal of its own, so the exporter's own judgement decides what is expressible;
   a conclusion is reachable when it is an expressible asserted triple or some derivation of it has
   every premise reachable; and a conclusion with no surviving derivation is reported as
   `WEAKER_EXPORT` with the blocking triple named. The verdict is only as good as that
   expressibility judgement, so the triple is printed rather than summarised.
7. **The differential exports from an unreasoned store, and checks that it did.** `reason`
   materialises into the default graph, so exporting from the same store puts the conclusion into
   the axioms and every conjecture becomes trivially entailed. That was this tool's first shape,
   and a deliberately broken exporter still scored a clean run under it. It now runs the reasoner
   and the exporter against separate stores, loads the certificate's own `asserted.tsv` for the
   export so the two see the same graph down to the blank node labels, and aborts if the triple
   counts differ rather than reporting a differential that cannot fail.
8. **Two serialisers, one translation.** `Form` is computed once; TPTP FOF and CLIF are folds over
   it and contain no OWL-specific logic. The correspondence test reads the CLIF back with an
   S-expression reader and requires the identical `Form`, so a drift in either writer is caught
   rather than argued about.
9. **The CLIF is restricted to the first-order-equivalent fragment, and says so in the file.**
   Common Logic is not plain first-order logic: it has sequence markers, arity-free predicates, and
   a universe in which relations are themselves individuals. ISO/IEC 24707 clause 6.5 is explicit
   that sequence markers make the logic non-compact and therefore not first-order. The adequacy
   theorem is about plain first-order logic, so the emitted text uses no sequence markers, fixed
   arity everywhere, and no quantification into a predicate position. `Form` cannot express any of
   the three; `clif_uses_only_fol_fragment` checks that the writer still does not.

## Why CLIF at all, given TPTP exists

Because they are not competing. TPTP is the execution format and CLIF is the interchange format,
and the toolchain confirms the split: Macleod translates CLIF to TPTP and to LADR and then calls
Vampire, Prover9, Paradox or Mace4 (`src/macleod/Commands.py` has exactly those four; E is not
among them). The consumer that matters here is standards-side, and it is a requirement rather than
a preference. **ISO/IEC 21838-1:2021 clause 4.3 requires that a top-level ontology be available
through an axiomatisation in a language conforming to ISO/IEC 24707**, its note naming CLIF, CGIF
and XCL as the qualifying dialects. Two qualifications travel with that and must not be dropped:
the English clause text was NOT read here, being paywalled, so the "shall be available" modality
comes from the Russian identical adoption of the same standard; and CLIF specifically is not
mandatory, since CGIF or XCL would satisfy clause 4.3 equally. CLIF is named for Basic Formal
Ontology in particular by ISO/IEC 21838-2 clause 4.4.1(a), which WAS read verbatim, and the ISO
maintenance portal ships `21838-2/common-logic/*.cl` alongside a Prover9 rendering and an OWL
approximation. BFO's own documentation states that the OWL version is an approximation to the CLIF
one and that an OWL axiom counts as valid just in case it is provable from the stronger
implementation. An ontology engine that can emit only TPTP cannot speak to that audience in its own
notation.

## CLIF was got wrong three times, and each time by assertion rather than measurement

Every correction below came from reading the standard or running a parser, and each replaced
something this project had simply assumed.

**Vertical bars.** Names were first written as `|...|`. That is Common Lisp's and KIF's convention.
A.2.2.2 sets `namequote = '"'`, and in CLIF the vertical bar is an ordinary name character, so
`|x|` lexes as a bare name containing two pipes and protects nothing. Names are now enclosed names
in double quotes, which A.2.2.4 recommends for IRIs.

**Double-quoted comment strings.** Comments were then written with double quotes, justified by
matching the CLIF files ISO hosts for ISO/IEC 21838-2. That corpus has been withdrawn by its own
maintainers: BFO's release notes of 7 December 2025 say "Comment texts are surrounded by single,
not double quotes". Counted, the ISO-hosted files carry 369 double-quoted `cl:comment` forms and
BFO master carries 356 single-quoted and none double-quoted. Worse, quote style had been bound to
operator spelling, so **no combination of flags could emit conforming CLIF**. The two are now
independent and comment strings are single-quoted in both dialects.

**Sentences wrapped in comments.** Every sentence was emitted as `(cl:comment '...' SENTENCE)`, the
shape BFO uses. Measured, both CLIF parsers that exist return an EMPTY theory from such a file:
py-typedlogic treats the form as discardable and Macleod has no production for it, and both do the
same to BFO's own files. A file that is formally valid and practically empty is the
assurance-laundering shape this project exists to attack, found inside this project's own output.
The default is now a standalone `(cl:comment '...')` phrase followed by a bare sentence, which
py-typedlogic reads back at exactly the sentence count the exporter reports; `--clif-comments
wrapped` keeps the old shape and the docs say what it costs. The text is also named now, because
all 227 COLORE texts are named and an unnamed one is refused by Macleod and misnamed by
py-typedlogic.

## Two dialects, because the ecosystem has two

`cl:text` and `cl:comment` are ISO/IEC 24707's reserved tokens and are what ISO publishes BFO in.
The COLORE repository is written with `cl-text` and `cl-comment`, and the Macleod parser
(`src/macleod/parsing/parser.py`) maps only the hyphen forms, with the colon forms present and
commented out. `--clif-dialect` therefore takes `iso` (the default) or `colore`. It is a spelling
and not a second translation: the correspondence test reads both dialects back to the identical
`Form`. It is **not** true that a file in one spelling fails in the other's tools, which this
record claimed until it was measured: py-typedlogic maps both spellings to identical results with
identical sentence counts. Macleod reads neither, because it cannot lex an IRI in a symbol
position at all.

## The subdialect claim is gated, not asserted

ISO/IEC 24707 first edition A.4.2: "The subdialect of CLIF which does not use numerals or quoted
strings is exactly semantically conformant". Staying inside it makes CLIF entailment and Common
Logic entailment coincide, so the adequacy theorem needs no qualification at the CLIF end. The
scope is stated exactly, in the header and in the docs: no decimal numerals and no quoted strings
IN SENTENCE POSITIONS, with comment annotations as the named exception, since a comment's text is a
quoted string by definition. `clif_stays_in_the_exactly_conformant_subdialect` walks every emitted
sentence and fails on either violation, and both failures have been demonstrated.

Nothing is claimed about the second edition's Annex A.3, which this project has not read, and
nothing anywhere says Common Logic requires infinite universes: abstract Common Logic requires only
non-emptiness, and the infinite-universe requirement is CLIF-specific, sits in the withdrawn first
edition, and sits awkwardly beside A.4.2 in that same edition.

## The quoting trap points opposite ways

TPTP takes single-quoted atoms for IRIs and CLIF takes double-quoted enclosed names, for the same
IRIs, for opposite reasons. In TPTP a double-quoted string is a *distinct object*, pairwise unequal
to every other; using it for IRIs would silently assert that all individuals are pairwise distinct,
which contradicts OWL's lack of a unique name assumption and would make every `owl:sameAs` export
unsound while still parsing and still proving things. In CLIF a single-quoted string is an
*interpreted name* that denotes itself, which is why A.2.2.4 recommends enclosed names for IRIs and
why using single quotes there would leave the exactly-conformant subdialect. Both traps are real
and they point opposite ways, so both are written down rather than left to a reader's intuition.

## What this does not claim

- **No ATP result is certified, in either direction.** `AGREE` means a second implementation
  reached the same conclusion. It is evidence, like pyshacl's agreement, and it is not a proof.
- **The Rust is not verified against the Lean.** Decision 0002's checker earns its verdict from a
  theorem. This layer earns its verdict from a test suite, and the difference is stated rather than
  blurred.
- **The front end is unclaimed on both sides.** `owl-lean`'s README lists OWL-file-to-abstract-syntax
  as not started: IRI resolution, the imports closure, the OWL 2 datatype map and facets, punning,
  blank node scoping. The reader in `src/tptp.rs` is that front end, and it is the part of this work
  that no theorem touches. Everything it cannot read, it names.
- **`hinds` is satisfied by construction, not weakened.** The theorem's hypothesis is
  `∀ a : S.Ind, a ∈ inds`, and the export's signature is the individual vocabulary occurring in the
  axioms and the goal, so the hypothesis holds for the signature the export defines. `owl-lean`
  lists weakening it to the occurring vocabulary as open; the exporter sits on the side of the gap
  where it is satisfied.

## Still not done

- The reader covers the common constructs and names the rest; it is not an OWL 2 conformance front
  end and does not claim to be.
- Cardinalities above 25 are dropped and named rather than expanded, because `minCard n` emits
  `n(n-1)/2` distinctness literals.
- Nothing runs the differential in CI. It needs a prover on `PATH`, skips loudly without one, and
  turns that skip into a failure under `FOL_DIFF_REQUIRE_ATP=1`; wiring a CI leg that installs E is
  not done. Nor is a CI leg that runs a CLIF parser over the export, which is what caught the
  empty-file defect.
- Nobody here has read ISO/IEC 24707:2018 or either part of ISO/IEC 21838. All three are priced at
  CHF 0, 70 pages for 24707, but downloading them needs a free ISO account, which is an owner
  action and not one to take on someone's behalf. The old ITTF free-standards site closed in 2025;
  the catalogue pages are reachable at `committee.iso.org` when `www.iso.org` returns 403. Until
  that is done, every clause cited here is scoped to the edition and the text actually read.
