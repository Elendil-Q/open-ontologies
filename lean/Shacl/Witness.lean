import Shacl.Report

/-!
# Witnesses: the specification says something, and it does not say everything

`eval_conforms_iff` and `validate_spec` are worth nothing on their own. If `Conf`
held of every focus node, "the evaluator reports nothing exactly when the node
conforms" would be a promise that the evaluator never reports anything, and the
theorem would still be true. If `Conf` held of none, the mirror image. This file
closes both by construction, the way `lean/OOCert/Witness.lean` does for the
derivation checker.

| theorem | says |
|---|---|
| `alice_conforms` | some node conforms to a real shape, proved from the specification by hand |
| `bob_does_not_conform` | some node does not, so `Conf` is not the trivial relation |
| `the_report_is_empty_when_everything_conforms` | `validate` can return nothing |
| `the_report_names_the_failing_node` | and it can return something, naming the right node and component |
| `duplicate_triples_are_counted_once` | `sh:maxCount` counts the SET of value nodes |
| `two_distinct_values_break_maxCount_one` | and it really does count them |
| `the_evaluator_refuses_rather_than_guessing` | the third answer is reachable, not decoration |

The two counting theorems are the ones worth reading. SHACL counts distinct value
nodes, so a triple asserted twice must not make a `sh:maxCount 1` fail. An engine
that counts SPARQL solutions rather than value nodes gets that wrong, and the
repository's own SHACL validator is documented as counting the other way
(`docs/lean-certificates.md`, "A SHACL report double-counts a node selected by two
target declarations"). Here it is settled in the specification and proved.
-/
namespace Shacl

/-! ## A small graph -/

def exAlice : Term := "<http://ex.org/alice>"
def exBob : Term := "<http://ex.org/bob>"
def exPerson : Term := "<http://ex.org/Person>"
def exAgent : Term := "<http://ex.org/Agent>"
def exName : Term := "<http://ex.org/name>"
def exKnows : Term := "<http://ex.org/knows>"
def exShape : Term := "<http://ex.org/AgentShape>"
def litAlice : Term := "\"Alice\""
def litBob : Term := "\"Bob\""

/-- Alice is a Person, Person is a subclass of Agent, Alice has a name, and Bob
knows Alice. Bob has no type and no name. -/
def gEx : Graph :=
  [ ⟨exAlice, V.type, exPerson⟩,
    ⟨exPerson, V.subClassOf, exAgent⟩,
    ⟨exAlice, exName, litAlice⟩,
    ⟨exBob, exKnows, exAlice⟩ ]

/-- An Agent with at least one name, every name a string. Written the way the
compiler writes it: the property shape's constraints wrapped in `named` so results
carry its IRI, the count constraint and the value-node constraint conjoined
transparently. -/
def sAgent : Shape :=
  .named exShape
    (.both (.klass exAgent)
      (.both (.minCount (.pred exName) 1)
        (.forAll (.pred exName) (.datatype V.xsdString))))

/-! ## Conformance holds somewhere, proved from the specification by hand

These three go through the definition of `Conf` and never touch `eval`. If the only
evidence that the specification says anything came from running the evaluator, a
reader would be entitled to suspect the two agree because they are the same
mistake. -/

theorem alice_is_an_agent : IsInstance gEx exAgent exAlice :=
  ⟨exPerson, by simp [gEx], .step (by simp [gEx]) (.refl _)⟩

theorem alice_has_a_name : Conf gEx (.minCount (.pred exName) 1) exAlice := by
  refine ⟨[litAlice], by simp, ?_, by simp⟩
  intro v hv
  rw [List.mem_singleton] at hv
  subst hv
  show (⟨exAlice, exName, litAlice⟩ : Triple) ∈ gEx
  simp [gEx]

theorem alices_names_are_strings :
    Conf gEx (.forAll (.pred exName) (.datatype V.xsdString)) exAlice := by
  intro v hv
  have hv' : (⟨exAlice, exName, v⟩ : Triple) ∈ gEx := hv
  simp only [gEx, List.mem_cons, List.not_mem_nil, or_false, Triple.mk.injEq] at hv'
  rcases hv' with ⟨-, h, -⟩ | ⟨h, -, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · subst h
    exact ⟨⟨"Alice", V.xsdString, none⟩, by decide, rfl, by decide⟩
  · exact absurd h (by decide)

/-- **Conformance is not the empty relation.** -/
theorem alice_conforms : Conf gEx sAgent exAlice :=
  ⟨alice_is_an_agent, alice_has_a_name, alices_names_are_strings⟩

/-! ## And it fails somewhere -/

theorem bob_has_no_type (t : Term) : (⟨exBob, V.type, t⟩ : Triple) ∉ gEx := by
  intro h
  simp only [gEx, List.mem_cons, List.not_mem_nil, or_false, Triple.mk.injEq] at h
  rcases h with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨-, h, -⟩ <;> exact absurd h (by decide)

/-- **Conformance is not the total relation.** Bob has no `rdf:type` at all, so he
is an instance of nothing, so he is not an Agent. -/
theorem bob_does_not_conform : ¬ Conf gEx sAgent exBob := by
  rintro ⟨⟨t, ht, -⟩, -, -⟩
  exact bob_has_no_type t ht

/-! ## The report, end to end

`validate` is what a validator actually runs. These two runs are settled by kernel
computation (`rfl`), so they are executable facts rather than claims about the
code. -/

def declAgent : ShapeDecl :=
  { id := exShape, targets := [.node exAlice], shape := sAgent }

def declBoth : ShapeDecl :=
  { id := exShape, targets := [.node exAlice, .node exBob], shape := sAgent }

/-- Targeting only Alice, the report is empty. -/
theorem the_report_is_empty_when_everything_conforms :
    validate gEx [declAgent] = .ok [] := by rfl

/-- Targeting Bob as well, the report names Bob, blames `sh:class`, and blames
`sh:minCount`: two results, with the property shape's IRI as `sh:sourceShape` and
the right constraint components. Written out in full so that a change to any field
of a result breaks this proof rather than passing quietly. -/
theorem the_report_names_the_failing_node :
    validate gEx [declBoth] = .ok
      [ { focus := exBob, path := none, value := some exBob, source := exShape,
          component := C.klass, blamed := .klass exAgent, blamedNode := exBob },
        { focus := exBob, path := some (.pred exName), value := none, source := exShape,
          component := C.minCount, blamed := .minCount (.pred exName) 1,
          blamedNode := exBob } ] := by rfl

/-- The two are not independent: because the report above is non-empty,
`validate_spec` says some targeted node fails, and because the one before it is
empty, `validate_spec` says every targeted node conforms. Both directions of the
theorem are therefore exercised on real data. -/
theorem the_specification_agrees_with_both_runs :
    (∀ d ∈ [declAgent], ∀ f, Targeted gEx d f → Conf gEx d.shape f) ∧
      ¬ (∀ d ∈ [declBoth], ∀ f, Targeted gEx d f → Conf gEx d.shape f) := by
  refine ⟨(validate_spec the_report_is_empty_when_everything_conforms).1.mp rfl, ?_⟩
  intro hall
  have hnil := (validate_spec the_report_names_the_failing_node).1.mpr hall
  exact absurd hnil (by simp)

/-! ## Counting is about the set of value nodes -/

def gDup : Graph := [⟨exAlice, exName, litAlice⟩, ⟨exAlice, exName, litAlice⟩]
def gTwo : Graph := [⟨exAlice, exName, litAlice⟩, ⟨exAlice, exName, litBob⟩]

/-- One value asserted twice is one value node, so `sh:maxCount 1` holds. Proved
from the specification, which quantifies over duplicate-free lists of value nodes
and so cannot be fooled by a repeated triple. -/
theorem duplicate_triples_are_counted_once :
    Conf gDup (.maxCount (.pred exName) 1) exAlice := by
  intro l hnd hmem
  have hsub : l ⊆ [litAlice] := by
    intro v hv
    have hv' : (⟨exAlice, exName, v⟩ : Triple) ∈ gDup := hmem v hv
    simp only [gDup, List.mem_cons, List.not_mem_nil, or_false, Triple.mk.injEq] at hv'
    rcases hv' with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> (subst h; simp)
  simpa using List.Nodup.length_le_of_subset hnd hsub

/-- Two distinct values are two value nodes, so the same constraint fails. Without
this the theorem above would be consistent with a specification that counts
nothing. -/
theorem two_distinct_values_break_maxCount_one :
    ¬ Conf gTwo (.maxCount (.pred exName) 1) exAlice := by
  intro h
  have hle := h [litAlice, litBob] (by decide) ?_
  · exact absurd hle (by decide)
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · show (⟨exAlice, exName, litAlice⟩ : Triple) ∈ gTwo; simp [gTwo]
    · rw [List.mem_singleton] at hv
      subst hv
      show (⟨exAlice, exName, litBob⟩ : Triple) ∈ gTwo; simp [gTwo]

/-! ## The third answer is reachable

A refusal that never fires is decoration. This one fires on the first `xsd:date`
literal it meets, and `tests/shacl_core_verified_test.rs` counts how often that
happens across the W3C suite. -/

def xsdDate : Term := "<http://www.w3.org/2001/XMLSchema#date>"
def litDate : Term := "\"2026-09-14\"^^<http://www.w3.org/2001/XMLSchema#date>"

/-- The literal has the right datatype IRI, so the constraint turns on whether it is
a well-formed `xsd:date`, and `lexOK` does not know. The evaluator says so by name
instead of choosing an answer. -/
theorem the_evaluator_refuses_rather_than_guessing :
    eval [] (.datatype xsdDate) exShape litDate
      = .error (.unknownLexicalSpace xsdDate "2026-09-14") := by rfl

/-- The specification, meanwhile, treats an unjudgeable literal as non-conforming.
So the two possible behaviours at this point were "report a violation" and "report a
refusal", and the evaluator takes the weaker one. Neither is a false pass, which is
the property that matters. -/
theorem the_refused_literal_does_not_conform :
    ¬ Conf [] (.datatype xsdDate) litDate := by
  rintro ⟨l, hl, -, hok⟩
  have : l = ⟨"2026-09-14", xsdDate, none⟩ := by
    have : asLiteral litDate = some ⟨"2026-09-14", xsdDate, none⟩ := by decide
    rw [this] at hl
    exact (Option.some.inj hl).symm
  subst this
  exact absurd hok (by decide)

/-! ## Axioms, pinned -/

/-- info: 'Shacl.alice_conforms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alice_conforms

/-- info: 'Shacl.bob_does_not_conform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bob_does_not_conform

/-- info: 'Shacl.the_report_names_the_failing_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms the_report_names_the_failing_node

/-- info: 'Shacl.duplicate_triples_are_counted_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms duplicate_triples_are_counted_once

/-- info: 'Shacl.two_distinct_values_break_maxCount_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_distinct_values_break_maxCount_one

/-- info: 'Shacl.the_evaluator_refuses_rather_than_guessing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms the_evaluator_refuses_rather_than_guessing

end Shacl
