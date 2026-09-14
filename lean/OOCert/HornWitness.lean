import OOCert.Horn

/-!
# What the Horn layer is worth

`horn_certificate_sound` is worthless on its own for the same two reasons
`Witness.lean` lists: if nothing satisfied a rule set the theorem would be
vacuous, and if `EntailsR` held of everything it would say nothing. Both are
closed here by construction. A third section shows the gate can fail, and a
fourth shows that eighteen of the twenty hardcoded rules are instances of the
generic theorem, so the generalisation subsumes the existing checker rather
than sitting beside it.
-/
namespace OOCert

/-! ## The rule layer is not vacuous -/

/-- The saturated interpretation satisfies every rule whatsoever, so for any
graph and any rule set the model class `EntailsR` quantifies over is non-empty
and `EntailsR` is not the "anything follows" of an inconsistent premise set. -/
theorem saturated_sat_rule (r : RulePattern) : SatRule saturated r := fun _ _ => trivial

theorem entailsR_not_vacuous (G : List Triple) (R : List RulePattern) :
    ∃ I : Interp, Model I G ∧ ∀ r ∈ R, SatRule I r :=
  ⟨saturated, saturated_is_a_model G, fun r _ => saturated_sat_rule r⟩

/-! ## A worked user rule -/

def uA : Term := "<u:a>"
def uB : Term := "<u:b>"
def uC : Term := "<u:c>"
def uP : Term := "<u:p>"
def uGp : Term := "<u:gp>"

/-- `p(x,y) and p(y,z) -> gp(x,z)`. Nothing about it is built in; it is data. -/
def gpRule : RulePattern :=
  { name := "grandparent"
    body := [⟨.var "x", .const uP, .var "y"⟩, ⟨.var "y", .const uP, .var "z"⟩]
    head := ⟨.var "x", .const uGp, .var "z"⟩ }

def demoR : List RulePattern := [gpRule]
def demoG : List Triple := [⟨uA, uP, uB⟩, ⟨uB, uP, uC⟩]

def demoStep : HornStep :=
  { rule := 0
    binds := [("x", uA), ("y", uB), ("z", uC)]
    premises := [⟨uA, uP, uB⟩, ⟨uB, uP, uC⟩]
    conclusion := ⟨uA, uGp, uC⟩ }

theorem demo_step_accepted :
    checkHornStep demoR (fun t => decide (t ∈ demoG)) demoStep = true := by decide

/-- The payoff, for a rule the checker has never heard of. -/
theorem demo_conclusion_entailed : EntailsR demoG demoR ⟨uA, uGp, uC⟩ :=
  checkHornStep_sound (G := demoG) (R := demoR) (k := fun t => decide (t ∈ demoG))
    (fun _ ht => EntailsR.of_mem (of_decide_eq_true ht)) demo_step_accepted

/-! ## The gate can fail

Six ways to be wrong, each rejected. Without these the acceptance above would
be evidence of nothing. -/

def badConclusion : HornStep := { demoStep with conclusion := ⟨uA, uGp, uB⟩ }
def badOrder : HornStep := { demoStep with premises := [⟨uB, uP, uC⟩, ⟨uA, uP, uB⟩] }
def badIndex : HornStep := { demoStep with rule := 7 }
/-- The substitution is applied consistently and the premises are the instantiated
body, but the second premise is not in the graph. -/
def badUnknown : HornStep :=
  { rule := 0
    binds := [("x", uA), ("y", uB), ("z", uA)]
    premises := [⟨uA, uP, uB⟩, ⟨uB, uP, uA⟩]
    conclusion := ⟨uA, uGp, uA⟩ }

theorem rejects_wrong_conclusion :
    checkHornStep demoR (fun t => decide (t ∈ demoG)) badConclusion = false := by decide
theorem rejects_scrambled_premise_order :
    checkHornStep demoR (fun t => decide (t ∈ demoG)) badOrder = false := by decide
theorem rejects_unknown_rule_index :
    checkHornStep demoR (fun t => decide (t ∈ demoG)) badIndex = false := by decide
theorem rejects_unknown_premise :
    checkHornStep demoR (fun t => decide (t ∈ demoG)) badUnknown = false := by decide

/-! ### The two shapes decision 0008 refuses

Both would have been ACCEPTED before it, and neither acceptance was unsound.
That is the point: these are refusals about what a certificate MEANS, not about
what it proves, so the evidence they can fail has to be written down here rather
than inferred from a soundness theorem that never mentions them. -/

/-- `x` is bound twice: first to the value that makes the step check, then to
one that does not. Whether this checked used to depend on `List.lookup` being
first-wins: a tie-break inside a standard-library function deciding whether a
certificate is valid. -/
def dupKey : HornStep :=
  { demoStep with binds := [("x", uA), ("y", uB), ("z", uC), ("x", uB)] }

/-- `z` is dropped. `substOf`'s default used to send it to the term `"z"`, which
is not an IRI, not a blank node and not a literal, and the conclusion below
carries exactly that fabricated term. -/
def uncovered : HornStep :=
  { rule := 0
    binds := [("x", uA), ("y", uB)]
    premises := [⟨uA, uP, uB⟩, ⟨uB, uP, "z"⟩]
    conclusion := ⟨uA, uGp, "z"⟩ }

theorem rejects_duplicate_binding_key :
    checkHornStep demoR (fun t => decide (t ∈ demoG)) dupKey = false := by decide
theorem rejects_binding_that_omits_a_rule_variable :
    checkHornStep demoR (fun t => decide (t ∈ demoG)) uncovered = false := by decide

/-- A binding for a variable the rule never mentions is NOT refused. The rule is
that the binding must DETERMINE the step, not that it must be minimal, and an
unconsulted pair cannot make a certificate mean two things. -/
def extraBind : HornStep :=
  { demoStep with binds := [("x", uA), ("y", uB), ("z", uC), ("nowhere", uP)] }

theorem accepts_a_binding_for_a_variable_the_rule_never_mentions :
    checkHornStep demoR (fun t => decide (t ∈ demoG)) extraBind = true := by decide

/-- And the refusal costs no certificate anyone meant. Binding `z` to the term
the conclusion already shows turns `uncovered` into a step BOTH kernels accept:
what decision 0008 requires is that the term be WRITTEN, not that it be
writable RDF. The second question is a separate one and this gate does not
answer it. -/
def uncoveredRepaired : HornStep :=
  { uncovered with binds := [("x", uA), ("y", uB), ("z", "z")] }

theorem the_repair_is_accepted :
    checkHornStep demoR (fun t => decide (t ∈ ⟨uB, uP, "z"⟩ :: demoG)) uncoveredRepaired
      = true := by decide

/-! ### The hypothesis of `wellFormed_determines_instantiation` is load-bearing

That theorem says a well-formed binding leaves nothing for a checker's choice of
representation to decide. It would be worth nothing if the conclusion held
anyway, so here is the counterexample: ONE binding list that is not well formed,
TWO total substitutions that both extend it, and two different conclusions. The
difference is exactly what the two kernels used to disagree about. -/

def partialBind : List (Var × Term) := [("x", uA), ("y", uB)]

/-- A second way to make `partialBind` total. It is no worse a choice than
`substOf`'s: both invent a value for `z`, and neither has any claim on the
other. -/
def otherExt : Subst := fun v => (List.lookup v partialBind).getD uC

theorem partialBind_is_not_wellFormed :
    bindingWellFormed gpRule partialBind = false := by decide

theorem otherExt_extends_partialBind :
    ∀ v t, List.lookup v partialBind = some t → otherExt v = t := by
  intro v t h
  simp [otherExt, h]

theorem substOf_extends_partialBind :
    ∀ v t, List.lookup v partialBind = some t → substOf partialBind v = t := by
  intro v t h
  simp [substOf, h]

/-- Two extensions of one binding list, two conclusions. `wellFormed_determines_
instantiation` rules this out, and only because its hypothesis is not free. -/
theorem two_extensions_of_an_uncovered_binding_disagree :
    AtomPat.inst otherExt gpRule.head ≠ AtomPat.inst (substOf partialBind) gpRule.head := by
  decide

/-! ## The rule layer does not derive everything

`demoH` is `demoG` closed under the grandparent rule. Its Herbrand
interpretation models `demoG`, satisfies the rule, and refutes `a gp b`. -/

def demoH : List Triple := ⟨uA, uGp, uC⟩ :: demoG

/-- The closure check, as a decidable statement over a three-triple list. -/
private theorem demoH_gp_closed :
    ∀ t ∈ demoH, ∀ u ∈ demoH, (t.p = uP ∧ u.p = uP ∧ u.s = t.o) →
      (⟨t.s, uGp, u.o⟩ : Triple) ∈ demoH := by decide

theorem demoH_sat_rule : SatRule (herbrand demoH) gpRule := by
  intro sigma hb
  have h1 := hb ⟨.var "x", .const uP, .var "y"⟩ (by simp [gpRule])
  have h2 := hb ⟨.var "y", .const uP, .var "z"⟩ (by simp [gpRule])
  exact demoH_gp_closed ⟨sigma "x", uP, sigma "y"⟩ h1 ⟨sigma "y", uP, sigma "z"⟩ h2
    ⟨rfl, rfl, rfl⟩

theorem demoH_is_a_model : Model (herbrand demoH) demoG where
  conds :=
    { sc_sub := fun a b hab => absurd hab (not_mem_pred demoH V.subClassOf (by decide) a b)
      sc_trans := fun a b _ hab => absurd hab (not_mem_pred demoH V.subClassOf (by decide) a b)
      sp_sub := fun a b hab => absurd hab (not_mem_pred demoH V.subPropertyOf (by decide) a b)
      sp_trans := fun a b _ hab =>
        absurd hab (not_mem_pred demoH V.subPropertyOf (by decide) a b)
      dom := fun p c hpc => absurd hpc (not_mem_pred demoH V.domain (by decide) p c)
      rng := fun p c hpc => absurd hpc (not_mem_pred demoH V.range (by decide) p c)
      trp := fun p hp => absurd hp (not_typed demoH V.transitiveProperty (by decide) p)
      symp := fun p hp => absurd hp (not_typed demoH V.symmetricProperty (by decide) p)
      inv := fun p q hpq => absurd hpq (not_mem_pred demoH V.inverseOf (by decide) p q)
      same := fun a b hab => absurd hab (not_mem_pred demoH V.sameAs (by decide) a b)
      eqc := fun a b hab => absurd hab (not_mem_pred demoH V.equivalentClass (by decide) a b)
      eqp := fun a b hab =>
        absurd hab (not_mem_pred demoH V.equivalentProperty (by decide) a b)
      svf := fun r p _ hop => absurd hop (not_mem_pred demoH V.onProperty (by decide) r p)
      avf := fun r p _ hop => absurd hop (not_mem_pred demoH V.onProperty (by decide) r p)
      hv := fun r p _ hop => absurd hop (not_mem_pred demoH V.onProperty (by decide) r p)
      svf_sc := fun c1 _ _ y1 _ hsv =>
        absurd hsv (not_mem_pred demoH V.someValuesFrom (by decide) c1 y1)
      svf_sp := fun c1 _ _ _ y hsv =>
        absurd hsv (not_mem_pred demoH V.someValuesFrom (by decide) c1 y)
      avf_sc := fun c1 _ _ y1 _ hav =>
        absurd hav (not_mem_pred demoH V.allValuesFrom (by decide) c1 y1)
      avf_sp := fun c1 _ _ _ y hav =>
        absurd hav (not_mem_pred demoH V.allValuesFrom (by decide) c1 y)
      dom_sc := fun p c1 _ hd => absurd hd (not_mem_pred demoH V.domain (by decide) p c1)
      dom_sp := fun _ p2 c hd => absurd hd (not_mem_pred demoH V.domain (by decide) p2 c)
      rng_sc := fun p c1 _ hr => absurd hr (not_mem_pred demoH V.range (by decide) p c1)
      rng_sp := fun _ p2 c hr => absurd hr (not_mem_pred demoH V.range (by decide) p2 c) }
  facts := fun t ht => List.mem_cons_of_mem _ ht
  int := by
    intro c l _ hc
    exact absurd hc (not_mem_pred demoG V.intersectionOf (by decide) c l)
  int2 := by
    intro c l _ hc
    exact absurd hc (not_mem_pred demoG V.intersectionOf (by decide) c l)
  uni := by
    intro c l _ hc
    exact absurd hc (not_mem_pred demoG V.unionOf (by decide) c l)
  oneOf := by
    intro c l _ hc
    exact absurd hc (not_mem_pred demoG V.oneOf (by decide) c l)

/-- Adding a user rule does not collapse entailment: `a gp b` is still not a
consequence, so the Horn layer derives less than everything. -/
theorem demo_not_everything_entailed : ¬ EntailsR demoG demoR ⟨uA, uGp, uB⟩ := by
  intro h
  have hrules : ∀ r ∈ demoR, SatRule (herbrand demoH) r := by
    intro r hr
    have : r = gpRule := List.mem_singleton.mp hr
    subst this
    exact demoH_sat_rule
  have hs := h (herbrand demoH) ⟨demoH_is_a_model, hrules⟩
  exact absurd hs (by decide : (⟨uA, uGp, uB⟩ : Triple) ∉ demoH)

/-- info: 'OOCert.entailsR_not_vacuous' does not depend on any axioms -/
#guard_msgs in
#print axioms entailsR_not_vacuous

/-- info: 'OOCert.demo_conclusion_entailed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms demo_conclusion_entailed

/-- info: 'OOCert.demo_not_everything_entailed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms demo_not_everything_entailed

end OOCert
