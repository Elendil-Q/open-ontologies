import OOCert.Semantics

/-!
# Witnesses: the semantics has models, and it does not prove everything

`certificate_sound` says an accepted certificate contains only entailed triples. That claim is worth
nothing on its own, and this file closes the two ways it could be hollow by construction rather than
by argument.

1. **If no interpretation satisfied `Conditions`**, `Entails G t` would hold for every `t` and the
   soundness theorem would be vacuously true. `saturated_is_a_model` exhibits a model of an
   arbitrary graph, so the conditions are satisfiable and no graph is inconsistent here. That is the
   expected shape rather than a surprise: the fragment has no negation, so nothing can contradict
   anything.

2. **If `Entails` held of everything anyway**, soundness would still say nothing.
   `not_everything_is_entailed` exhibits a triple that is not entailed.

The third theorem is the one worth having. `the_old_svf_derivation_is_not_entailed` proves that the
derivation the reasoner used to make, `x rdf:type C` from `C rdfs:subClassOf (some p D)` together
with `x p y` and `y rdf:type D`, is **not** a consequence: there is a model of the premises in which
`x` is not a `C`. So that behaviour was unsound in fact, not merely unjustified by the rule set this
checker implements, and `tests/reason_rl_ext_soundness_test.rs` pins a real defect.
`the_sound_half_survives` proves the fix did not overshoot: what the reasoner still derives on the
same input is entailed.

The witness is the Herbrand interpretation of a finite graph: the domain is the set of terms, every
term denotes itself, and a property's extension is the set of pairs the list carries. Every side
condition is `decide`-checked over concrete term strings, so these are executable facts.
-/
namespace OOCert

/-! ## The semantics is satisfiable -/

/-- The interpretation in which every property relates everything. -/
def saturated : Interp where
  D := Unit
  ι := fun _ => ()
  iext := fun _ _ _ => True

/-- Every graph has a model, so `Entails` is never the "anything follows" of an inconsistent
premise set. -/
theorem saturated_is_a_model (G : List Triple) : Model saturated G where
  conds :=
    { sc_sub := fun _ _ _ _ _ => trivial
      sc_trans := fun _ _ _ _ _ => trivial
      sp_sub := fun _ _ _ _ _ _ => trivial
      sp_trans := fun _ _ _ _ _ => trivial
      dom := fun _ _ _ _ _ _ => trivial
      rng := fun _ _ _ _ _ _ => trivial
      trp := fun _ _ _ _ _ _ _ => trivial
      symp := fun _ _ _ _ _ => trivial
      inv := fun _ _ _ _ _ => Iff.intro (fun _ => trivial) (fun _ => trivial)
      same := fun a b _ => by cases a; cases b; rfl
      eqc := fun _ _ _ => ⟨trivial, trivial⟩
      eqp := fun _ _ _ => ⟨trivial, trivial⟩
      svf := fun _ _ _ _ _ _ _ _ _ => trivial
      avf := fun _ _ _ _ _ _ _ _ _ => trivial
      hv := fun _ _ _ _ _ _ => Iff.intro (fun _ => trivial) (fun _ => trivial) }
  facts := fun _ _ => trivial
  int := fun _ _ _ _ _ _ _ => trivial
  uni := fun _ _ _ _ _ _ _ _ _ => trivial

/-! ## Herbrand interpretations -/

/-- Terms denote themselves; a property relates exactly the pairs the graph lists. -/
def herbrand (H : List Triple) : Interp where
  D := Term
  ι := id
  iext := fun p x y => (⟨x, p, y⟩ : Triple) ∈ H

@[simp] theorem herbrand_ι (H : List Triple) (t : Term) : (herbrand H).ι t = t := rfl

@[simp] theorem herbrand_iext (H : List Triple) (p x y : Term) :
    (herbrand H).iext p x y ↔ (⟨x, p, y⟩ : Triple) ∈ H := Iff.rfl

@[simp] theorem herbrand_sat (H : List Triple) (t : Triple) :
    (herbrand H).sat t ↔ t ∈ H := Iff.rfl

@[simp] theorem herbrand_cext (H : List Triple) (c x : Term) :
    (herbrand H).cext c x ↔ (⟨x, V.type, c⟩ : Triple) ∈ H := Iff.rfl

@[simp] theorem herbrand_sc (H : List Triple) (a b : Term) :
    (herbrand H).sc a b ↔ (⟨a, V.subClassOf, b⟩ : Triple) ∈ H := Iff.rfl

@[simp] theorem herbrand_sp (H : List Triple) (a b : Term) :
    (herbrand H).sp a b ↔ (⟨a, V.subPropertyOf, b⟩ : Triple) ∈ H := Iff.rfl

/-- No triple of `H` uses predicate `p`, so nothing is in `p`'s extension. `H` and `p` are explicit:
left implicit, unification instantiates `p` with the unreduced `(herbrand H).ι V.foo`, and the side
condition stops being a decidable proposition. -/
theorem not_mem_pred (H : List Triple) (p : Term) (h : ∀ t ∈ H, t.p ≠ p) (s o : Term) :
    (⟨s, p, o⟩ : Triple) ∉ H := fun hm => h _ hm rfl

/-- Nothing in `H` is typed `c`, so `c`'s class extension is empty. -/
theorem not_typed (H : List Triple) (c : Term) (h : ∀ t ∈ H, ¬(t.p = V.type ∧ t.o = c)) (x : Term) :
    (⟨x, V.type, c⟩ : Triple) ∉ H := fun hm => h _ hm ⟨rfl, rfl⟩

/-- The Herbrand interpretation of the empty graph: every condition holds vacuously and no triple
is satisfied. -/
theorem empty_herbrand_is_a_model : Model (herbrand []) [] where
  conds :=
    { sc_sub := fun a b hab => absurd hab (not_mem_pred [] V.subClassOf (by simp) a b)
      sc_trans := fun a b _ hab => absurd hab (not_mem_pred [] V.subClassOf (by simp) a b)
      sp_sub := fun a b hab => absurd hab (not_mem_pred [] V.subPropertyOf (by simp) a b)
      sp_trans := fun a b _ hab => absurd hab (not_mem_pred [] V.subPropertyOf (by simp) a b)
      dom := fun p c hpc => absurd hpc (not_mem_pred [] V.domain (by simp) p c)
      rng := fun p c hpc => absurd hpc (not_mem_pred [] V.range (by simp) p c)
      trp := fun p hp => absurd hp (not_typed [] V.transitiveProperty (by simp) p)
      symp := fun p hp => absurd hp (not_typed [] V.symmetricProperty (by simp) p)
      inv := fun p q hpq => absurd hpq (not_mem_pred [] V.inverseOf (by simp) p q)
      same := fun a b hab => absurd hab (not_mem_pred [] V.sameAs (by simp) a b)
      eqc := fun a b hab => absurd hab (not_mem_pred [] V.equivalentClass (by simp) a b)
      eqp := fun a b hab => absurd hab (not_mem_pred [] V.equivalentProperty (by simp) a b)
      svf := fun r p _ hop => absurd hop (not_mem_pred [] V.onProperty (by simp) r p)
      avf := fun r p _ hop => absurd hop (not_mem_pred [] V.onProperty (by simp) r p)
      hv := fun r p _ hop => absurd hop (not_mem_pred [] V.onProperty (by simp) r p) }
  facts := by intro t ht; simp at ht
  int := by intro c l _ hc; exact absurd hc (not_mem_pred [] V.intersectionOf (by simp) c l)
  uni := by intro c l _ hc; exact absurd hc (not_mem_pred [] V.unionOf (by simp) c l)

/-- Entailment is not trivial. -/
theorem not_everything_is_entailed :
    ¬ Entails [] ⟨"<http://ex.org/a>", "<http://ex.org/b>", "<http://ex.org/c>"⟩ := by
  intro h
  have hs := h (herbrand []) empty_herbrand_is_a_model
  simp at hs

/-! ## The derivation the old `cls-svf1` made, refuted

`svfPremises` is the ontology from `tests/reason_rl_ext_soundness_test.rs`:
`C rdfs:subClassOf R`, `R owl:onProperty p`, `R owl:someValuesFrom D`, `x p y`, `y rdf:type D`.
The reasoner used to conclude `x rdf:type C` from it.

`svfWitness` adds the one triple the semantics does force, `x rdf:type R`, and nothing else. Its
Herbrand interpretation models the premises and refutes the conclusion.
-/

def tC : Term := "<http://ex.org/C>"
def tR : Term := "<http://ex.org/R>"
def tD : Term := "<http://ex.org/D>"
def tp : Term := "<http://ex.org/p>"
def tx : Term := "<http://ex.org/x>"
def ty : Term := "<http://ex.org/y>"

def svfPremises : List Triple :=
  [ ⟨tC, V.subClassOf, tR⟩,
    ⟨tR, V.onProperty, tp⟩,
    ⟨tR, V.someValuesFrom, tD⟩,
    ⟨tx, tp, ty⟩,
    ⟨ty, V.type, tD⟩ ]

/-- The premises plus the one consequence the `svf` condition forces, `x ∈ (some p D)`. Nothing
puts `x` in `C`, which is the whole point. -/
def svfWitness : List Triple := ⟨tx, V.type, tR⟩ :: svfPremises

/-! The three side conditions the witness graph has to satisfy, each a closed statement over a
six-triple list and therefore settled by `decide` rather than by a tactic script. Stating them this
way keeps the model proof free of membership case analysis, which is where the string literals
would otherwise have to be compared by hand. -/

/-- Nothing is an instance of a class that has a superclass: the only `rdfs:subClassOf` triple has
subject `C`, and nothing is typed `C`. This is what makes `sc_sub` hold vacuously. -/
private theorem no_typed_subclass :
    ∀ t ∈ svfWitness, ∀ u ∈ svfWitness, ¬(t.p = V.subClassOf ∧ u.p = V.type ∧ u.o = t.s) := by
  decide

/-- No two `rdfs:subClassOf` triples compose, so `sc_trans` holds vacuously. -/
private theorem no_sc_chain :
    ∀ t ∈ svfWitness, ∀ u ∈ svfWitness, ¬(t.p = V.subClassOf ∧ u.p = V.subClassOf ∧ u.s = t.o) := by
  decide

/-- The one existential witness the graph does contain is already recorded: whenever the graph has
`r owl:onProperty p`, `r owl:someValuesFrom c`, `x p y` and `y rdf:type c`, it also has
`x rdf:type r`. This is the `svf` condition, and it is the only condition the witness graph
satisfies non-vacuously. -/
private theorem svf_closed :
    ∀ t ∈ svfWitness, ∀ u ∈ svfWitness, ∀ v ∈ svfWitness, ∀ w ∈ svfWitness,
      (t.p = V.onProperty ∧ u.p = V.someValuesFrom ∧ u.s = t.s ∧
       v.p = t.o ∧ w.p = V.type ∧ w.o = u.o ∧ w.s = v.o) →
      (⟨v.s, V.type, t.s⟩ : Triple) ∈ svfWitness := by
  decide

theorem svf_witness_is_a_model : Model (herbrand svfWitness) svfPremises where
  conds :=
    { sc_sub := fun a b hab x hx =>
        absurd ⟨rfl, rfl, rfl⟩ (no_typed_subclass ⟨a, V.subClassOf, b⟩ hab ⟨x, V.type, a⟩ hx)
      sc_trans := fun a b c hab hbc =>
        absurd ⟨rfl, rfl, rfl⟩
          (no_sc_chain ⟨a, V.subClassOf, b⟩ hab ⟨b, V.subClassOf, c⟩ hbc)
      sp_sub := fun a b hab => absurd hab (not_mem_pred svfWitness V.subPropertyOf (by decide) a b)
      sp_trans := fun a b _ hab =>
        absurd hab (not_mem_pred svfWitness V.subPropertyOf (by decide) a b)
      dom := fun p c hpc => absurd hpc (not_mem_pred svfWitness V.domain (by decide) p c)
      rng := fun p c hpc => absurd hpc (not_mem_pred svfWitness V.range (by decide) p c)
      trp := fun p hp => absurd hp (not_typed svfWitness V.transitiveProperty (by decide) p)
      symp := fun p hp => absurd hp (not_typed svfWitness V.symmetricProperty (by decide) p)
      inv := fun p q hpq => absurd hpq (not_mem_pred svfWitness V.inverseOf (by decide) p q)
      same := fun a b hab => absurd hab (not_mem_pred svfWitness V.sameAs (by decide) a b)
      eqc := fun a b hab => absurd hab (not_mem_pred svfWitness V.equivalentClass (by decide) a b)
      eqp := fun a b hab =>
        absurd hab (not_mem_pred svfWitness V.equivalentProperty (by decide) a b)
      svf := fun r p c hop hsv x y hxy hy =>
        svf_closed ⟨r, V.onProperty, p⟩ hop ⟨r, V.someValuesFrom, c⟩ hsv
          ⟨x, p, y⟩ hxy ⟨y, V.type, c⟩ hy ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      avf := fun r _ c _ hav =>
        absurd hav (not_mem_pred svfWitness V.allValuesFrom (by decide) r c)
      hv := fun r _ v _ hhv => absurd hhv (not_mem_pred svfWitness V.hasValue (by decide) r v) }
  facts := fun t ht => List.mem_cons_of_mem _ ht
  int := by intro c l _ hc; exact absurd hc (not_mem_pred svfPremises V.intersectionOf (by decide) c l)
  uni := by intro c l _ hc; exact absurd hc (not_mem_pred svfPremises V.unionOf (by decide) c l)

/-- **The old rule was unsound.** `C ⊑ ∃p.D` together with `x p y` and `y ∈ D` does not entail
`x ∈ C`. The reasoner derived exactly this until 13 September 2026. -/
theorem the_old_svf_derivation_is_not_entailed :
    ¬ Entails svfPremises ⟨tx, V.type, tC⟩ := fun h =>
  absurd (h (herbrand svfWitness) svf_witness_is_a_model)
    (not_typed svfWitness tC (by decide) tx)

/-- The fix did not overshoot into deriving nothing: what the reasoner still concludes on the same
input, `x ∈ (some p D)`, is entailed. Proved for an arbitrary model, not just the witness. -/
theorem the_sound_half_survives : Entails svfPremises ⟨tx, V.type, tR⟩ := by
  intro I M
  have hop := M.facts ⟨tR, V.onProperty, tp⟩ (by simp [svfPremises])
  have hsv := M.facts ⟨tR, V.someValuesFrom, tD⟩ (by simp [svfPremises])
  have hxy := M.facts ⟨tx, tp, ty⟩ (by simp [svfPremises])
  have hy := M.facts ⟨ty, V.type, tD⟩ (by simp [svfPremises])
  exact M.conds.svf _ _ _ hop hsv _ _ hxy hy

/-! Axioms, pinned. A `sorry` here would quietly restore the vacuity objection this file exists to
close, which is exactly the kind of silent hole the project refuses elsewhere. These lists are
shorter than the one `certificate_sound` carries: the witnesses need no choice, and the two
statements about the removed rule are proved from `propext` alone. -/
/-- info: 'OOCert.saturated_is_a_model' does not depend on any axioms -/
#guard_msgs in
#print axioms saturated_is_a_model

/-- info: 'OOCert.not_everything_is_entailed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_everything_is_entailed

/-- info: 'OOCert.the_old_svf_derivation_is_not_entailed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms the_old_svf_derivation_is_not_entailed

/-- info: 'OOCert.the_sound_half_survives' depends on axioms: [propext] -/
#guard_msgs in
#print axioms the_sound_half_survives

end OOCert
