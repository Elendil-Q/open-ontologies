import OOCert.Soundness
import OOCert.Witness
import OOCert.Horn
import OOCert.HornBuiltin
import OOCert.HornWitness

/-!
# One certificate, both rule families

A certificate used to be either all built-in arms (`Rules.lean`, proved by
`certificate_sound`) or all citations of a user-supplied Horn rule (`Horn.lean`,
proved by `horn_certificate_sound`). A user who wrote one rule of their own could
not also cite `cls-int1` or `cls-uni`, and those two are never going to become
Horn rules: their premise count is the length of an RDF list, which is data
rather than something the rule fixes. `HornBuiltin.lean` says so at its top and
means it.

`MStep` is the union of the two step kinds and `mixed_certificate_sound` covers
both in one induction. The twenty arms are reused unchanged. The only thing that
had to give was the entailment relation in `Soundness.lean`, which is now
parametric in the class of interpretations the certificate is relative to
(`EntailsIn P`). A model of `G` that also satisfies `R` is in particular a model
of `G`, so every one of the per-rule cases applies at `P := ModelR G R` without
being touched.

## Which guarantee a mixed certificate earns

Two, and they are not the same one.

`mixed_certificate_sound` gives `EntailsR G R`: true in every model of the
asserted graph that also satisfies the supplied rules. The rules are an
assumption the certificate carries and nothing here checks them. A rule reading
"every supplier is compliant" makes certificates that check green for ever.

`mixed_certificate_sound_of_discharged` gives the absolute `Entails G`, and it
asks for the one thing that makes the difference: a proof, for every rule in the
table, that the semantic conditions already imply it.
`mixed_certificate_sound_builtin` is that theorem applied to the nineteen
built-in rules, which `Builtin.asHorn_sound` discharges, and
`mixed_certificate_sound_no_rules` is the empty table, which has nothing to
discharge.

The difference is not academic, and the witness section below proves that rather
than asserting it. `mix_conclusion_entailed` and `mix_not_absolutely_entailed`
are about the same triple of the same accepted certificate: it follows under the
supplied rule, and without that rule it does not follow, because there is a model
of the asserted graph that refutes it. Printing the absolute verdict for that run
would be a false statement about a machine-checked fact.

`absolute_verdict_is_earned` is the last theorem in the file and the reason the
report functions are here rather than in a binary. It says that whenever the
verdict function prints the absolute word, the absolute theorem applies to that
run. The verdict cannot launder an assumption into a fact, and that is a proof
rather than a review comment. See
`docs/decisions/0003-a-rule-is-data-and-an-assumption-is-not-a-fact.md`.
-/
namespace OOCert

/-! ## The checker -/

/-- A step of a mixed certificate: a built-in rule with its hardcoded arm, or a
citation of a rule from the supplied table. -/
inductive MStep
  | builtin : Step → MStep
  | horn : HornStep → MStep
deriving Repr

def MStep.conclusion : MStep → Triple
  | .builtin st => st.conclusion
  | .horn st => st.conclusion

/-- Check one step of either kind.

The built-in arm is handed `inG` and `derived` separately rather than their
disjunction, and that is not tidiness. `cls-int1` and `cls-uni` read their RDF
list off the ASSERTED graph, because `Model` reads it off the asserted graph, so
`checkStep` tests the constructor triple and every chain triple with `inG`
alone. Passing `fun t => inG t || derived t` for both jobs would let a
certificate build a list out of its own earlier conclusions.
`rejects_a_list_that_was_not_asserted` below pins that, with `derived` answering
true to every triple in the language. -/
def checkMStep (inG derived : Triple → Bool) (R : List RulePattern) : MStep → Bool
  | .builtin st => checkStep inG derived st
  | .horn st => checkHornStep R (fun t => inG t || derived t) st

/-- Steps in order, each seeing only the conclusions of the ones before it. The
discipline `checkAll` and `checkHornAll` already use, and in particular no step
may cite itself. -/
def checkAllM (inG : Triple → Bool) (R : List RulePattern) :
    List MStep → Std.HashSet Triple → Bool
  | [], _ => true
  | st :: rest, derived =>
      checkMStep inG (fun t => derived.contains t) R st &&
      checkAllM inG R rest (derived.insert st.conclusion)

/-- The mixed checker. `G` is the asserted graph, `R` the rule table the
certificate is relative to, `steps` the certificate. -/
def checkCertM (G : List Triple) (R : List RulePattern) (steps : List MStep) : Bool :=
  let gset := Std.HashSet.ofList G
  checkAllM (fun t => gset.contains t) R steps ∅

/-! ## Soundness -/

/-- One step, either kind. The built-in case is `checkStep_sound` instantiated at
`P := ModelR G R`, which is the whole content of the generalisation; the Horn
case is `checkHornStep_sound` with the two sources of a known premise spliced
back together. -/
theorem checkMStep_sound {G : List Triple} {R : List RulePattern}
    {inG derived : Triple → Bool} {st : MStep}
    (hG : ∀ t, inG t = true → t ∈ G)
    (hD : ∀ t, derived t = true → EntailsR G R t)
    (h : checkMStep inG derived R st = true) : EntailsR G R st.conclusion := by
  cases st with
  | builtin b =>
    exact checkStep_sound (P := ModelR G R) (fun _ hI => hI.1) hG hD h
  | horn hs =>
    refine checkHornStep_sound ?_ h
    intro t ht
    simp only [Bool.or_eq_true] at ht
    rcases ht with hx | hx
    · exact EntailsR.of_mem (hG t hx)
    · exact hD t hx

theorem checkAllM_sound {G : List Triple} {R : List RulePattern} {inG : Triple → Bool}
    (hG : ∀ t, inG t = true → t ∈ G) :
    ∀ (steps : List MStep) (derived : Std.HashSet Triple),
      (∀ t, derived.contains t = true → EntailsR G R t) →
      checkAllM inG R steps derived = true →
      ∀ st ∈ steps, EntailsR G R st.conclusion := by
  intro steps
  induction steps with
  | nil => intro _ _ _ st hst; simp at hst
  | cons st rest ih =>
    intro derived hD h st' hst'
    simp only [checkAllM, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hst : EntailsR G R st.conclusion := checkMStep_sound hG hD h1
    have hD' : ∀ t, (derived.insert st.conclusion).contains t = true → EntailsR G R t := by
      intro t ht
      rw [Std.HashSet.contains_insert] at ht
      simp only [Bool.or_eq_true, beq_iff_eq] at ht
      rcases ht with rfl | ht
      · exact hst
      · exact hD t ht
    rcases List.mem_cons.mp hst' with rfl | hmem
    · exact hst
    · exact ih _ hD' h2 st' hmem

/-- **The theorem for a mixed certificate.** One induction, both step kinds. The
guarantee is RELATIVE to `R`: every conclusion is true in every model of `G` that
also satisfies the supplied rules. It says nothing about whether those rules are
true, and nothing about whether the rule set is consistent. -/
theorem mixed_certificate_sound (G : List Triple) (R : List RulePattern) (steps : List MStep)
    (h : checkCertM G R steps = true) : ∀ st ∈ steps, EntailsR G R st.conclusion := by
  unfold checkCertM at h
  refine checkAllM_sound (G := G) (R := R)
    (inG := fun t => (Std.HashSet.ofList G).contains t) ?_ steps ∅ ?_ h
  · intro t ht
    rw [Std.HashSet.contains_ofList] at ht
    simpa using ht
  · intro t ht
    simp at ht

/-- The absolute guarantee, and the price of it: a proof for EVERY rule in the
table that the semantic conditions already imply it. Nothing else upgrades a
relative verdict to an absolute one. -/
theorem mixed_certificate_sound_of_discharged (G : List Triple) (R : List RulePattern)
    (hR : ∀ r ∈ R, ∀ I : Interp, Conditions I → SatRule I r)
    (steps : List MStep) (h : checkCertM G R steps = true) :
    ∀ st ∈ steps, Entails G st.conclusion := by
  intro st hst I M
  exact mixed_certificate_sound G R steps h st hst I ⟨M, fun r hr => hR r hr I M.conds⟩

/-- The empty table has nothing to discharge, so a mixed certificate over it is
the old built-in certificate and the old warrant comes back unchanged. Nothing
was lost in the generalisation. -/
theorem mixed_certificate_sound_no_rules (G : List Triple) (steps : List MStep)
    (h : checkCertM G [] steps = true) : ∀ st ∈ steps, Entails G st.conclusion :=
  mixed_certificate_sound_of_discharged G [] (by intro r hr; simp at hr) steps h

/-- The built-in table, discharged by `Builtin.asHorn_sound`. A certificate may
mix the nineteen built-in rules cited as data with the two hardcoded arms
`cls-int1` and `cls-uni` and still earn the absolute verdict. -/
theorem mixed_certificate_sound_builtin (G : List Triple) (steps : List MStep)
    (h : checkCertM G Builtin.asHorn steps = true) :
    ∀ st ∈ steps, Entails G st.conclusion :=
  mixed_certificate_sound_of_discharged G Builtin.asHorn
    (fun r hr I C => Builtin.asHorn_sound I C r hr) steps h

/-! ## A worked mixed certificate

Two steps that could not have shared a certificate before this file existed. The
first is `cls-int1`, a hardcoded arm, because its premise count is the length of
an RDF list. The second cites a rule the checker has never heard of, and its only
premise is the first step's conclusion.

The rule is decision 0003's own example, "every supplier is compliant", because
the point of the section is what such a rule does and does not buy. -/

def mAcme : Term := "<u:acme>"
def mVendor : Term := "<u:Vendor>"
def mApproved : Term := "<u:Approved>"
def mSupplier : Term := "<u:Supplier>"
def mStatus : Term := "<u:status>"
def mCompliant : Term := "<u:Compliant>"
def mL0 : Term := "_:l0"
def mL1 : Term := "_:l1"

/-- `Supplier ≡ Vendor ⊓ Approved` as an RDF list, and an acme that is both. -/
def mixG : List Triple :=
  [ ⟨mSupplier, V.intersectionOf, mL0⟩,
    ⟨mL0, V.first, mVendor⟩, ⟨mL0, V.rest, mL1⟩,
    ⟨mL1, V.first, mApproved⟩, ⟨mL1, V.rest, V.nil⟩,
    ⟨mAcme, V.type, mVendor⟩, ⟨mAcme, V.type, mApproved⟩ ]

/-- The assumption. Nothing in this file or any other proves it, and that is the
whole subject of decision 0003. -/
def complianceRule : RulePattern :=
  { name := "every-supplier-is-compliant"
    body := [⟨.var "s", .const V.type, .const mSupplier⟩]
    head := ⟨.var "s", .const mStatus, .const mCompliant⟩ }

def mixR : List RulePattern := [complianceRule]

def mixIntStep : Step :=
  { rule := .clsInt1
    premises :=
      [⟨mSupplier, V.intersectionOf, mL0⟩,
       ⟨mL0, V.first, mVendor⟩, ⟨mL0, V.rest, mL1⟩,
       ⟨mL1, V.first, mApproved⟩, ⟨mL1, V.rest, V.nil⟩,
       ⟨mAcme, V.type, mVendor⟩, ⟨mAcme, V.type, mApproved⟩]
    conclusion := ⟨mAcme, V.type, mSupplier⟩ }

def mixHornStep : HornStep :=
  { rule := 0
    binds := [("s", mAcme)]
    premises := [⟨mAcme, V.type, mSupplier⟩]
    conclusion := ⟨mAcme, mStatus, mCompliant⟩ }

def mixSteps : List MStep := [.builtin mixIntStep, .horn mixHornStep]

/-! The two facts are stated per step rather than through `checkCertM`, because
`checkCertM` carries its derived set in a `Std.HashSet` and `Triple`'s hash runs
through `String.hash`, which is opaque to the kernel. `decide` therefore cannot
evaluate it, and `native_decide` is not available here: it would add
`Lean.ofReduceBool` to the trust surface. `checkCertM` itself is exercised at
run time, by `tests/lean_mixed_certificate_test.rs`. -/

def mixInG : Triple → Bool := fun t => decide (t ∈ mixG)
/-- What the second step may treat as derived: the first step's conclusion, and
nothing else. -/
def mixAfterFirst : Triple → Bool := fun t => decide (t = (⟨mAcme, V.type, mSupplier⟩ : Triple))

theorem mix_builtin_step_accepted :
    checkMStep mixInG (fun _ => false) mixR (.builtin mixIntStep) = true := by decide

theorem mix_horn_step_accepted :
    checkMStep mixInG mixAfterFirst mixR (.horn mixHornStep) = true := by decide

theorem mix_type_entailed : EntailsR mixG mixR ⟨mAcme, V.type, mSupplier⟩ :=
  checkMStep_sound (G := mixG) (R := mixR)
    (fun _ ht => of_decide_eq_true ht)
    (fun _ ht => by simp at ht)
    mix_builtin_step_accepted

/-- The payoff. A conclusion reached through a hardcoded arm and a user rule in
one certificate. -/
theorem mix_conclusion_entailed : EntailsR mixG mixR ⟨mAcme, mStatus, mCompliant⟩ :=
  checkMStep_sound (G := mixG) (R := mixR)
    (fun _ ht => of_decide_eq_true ht)
    (fun t ht => by
      have he : t = (⟨mAcme, V.type, mSupplier⟩ : Triple) := of_decide_eq_true ht
      subst he
      exact mix_type_entailed)
    mix_horn_step_accepted

/-! ## The gate can fail

Six ways to be wrong, two of them about the built-in step and four about the
step citing a rule, each rejected on its own. Without these the acceptance above
would be evidence of nothing. -/

def mixForgedIntConclusion : Step := { mixIntStep with conclusion := ⟨mAcme, V.type, mVendor⟩ }

/-- A shorter list, so that being merely `Approved` would suffice. The chain
triples are not in `mixG`. -/
def mixForgedIntChain : Step :=
  { rule := .clsInt1
    premises :=
      [⟨mSupplier, V.intersectionOf, mL0⟩,
       ⟨mL0, V.first, mApproved⟩, ⟨mL0, V.rest, V.nil⟩,
       ⟨mAcme, V.type, mApproved⟩]
    conclusion := ⟨mAcme, V.type, mSupplier⟩ }

def mixForgedHornConclusion : HornStep :=
  { mixHornStep with conclusion := ⟨mAcme, mStatus, mSupplier⟩ }
def mixForgedHornIndex : HornStep := { mixHornStep with rule := 1 }
def mixForgedHornBinding : HornStep := { mixHornStep with binds := [("s", mVendor)] }

theorem rejects_a_forged_builtin_conclusion :
    checkMStep mixInG mixAfterFirst mixR (.builtin mixForgedIntConclusion) = false := by decide

/-- `derived` answers true to every triple there is, and the step is still
rejected, because a list must be asserted. -/
theorem rejects_a_list_that_was_not_asserted :
    checkMStep mixInG (fun _ => true) mixR (.builtin mixForgedIntChain) = false := by decide

theorem rejects_a_forged_horn_conclusion :
    checkMStep mixInG mixAfterFirst mixR (.horn mixForgedHornConclusion) = false := by decide

theorem rejects_an_unknown_rule_index :
    checkMStep mixInG mixAfterFirst mixR (.horn mixForgedHornIndex) = false := by decide

theorem rejects_a_binding_that_does_not_instantiate_the_body :
    checkMStep mixInG mixAfterFirst mixR (.horn mixForgedHornBinding) = false := by decide

/-- Order is part of the contract across the two kinds as well as within one:
the Horn step's only premise is the built-in step's conclusion, so before that
step has run it is neither asserted nor derived. -/
theorem rejects_a_horn_step_before_the_builtin_step_it_needs :
    checkMStep mixInG (fun _ => false) mixR (.horn mixHornStep) = false := by decide

/-! ## What the relative guarantee is worth, and what it is not

Three facts about the certificate just accepted. The model class it quantifies
over is not empty, so the guarantee is not the vacuous one of an inconsistent
premise set. It does not hold of everything, so it is not the trivial relation.
And the conclusion it licenses is NOT a consequence of the asserted graph alone,
which is the machine-checked form of the thing decision 0003 refuses to let a
report blur. -/

/-- `saturated` models any graph and satisfies any rule, so the model class is
non-empty for this graph and this table. -/
theorem mix_rules_are_satisfiable : ∃ I : Interp, Model I mixG ∧ ∀ r ∈ mixR, SatRule I r :=
  entailsR_not_vacuous mixG mixR

/-- Inversion for `Chain`, which `Semantics.lean` declares without one because
nothing needed it until a witness graph carried a list. It belongs beside the
inductive and would be welcome there. -/
private theorem chain_uncons {G : List Triple} {l : Term} {ms : List Term} (h : Chain G l ms) :
    (l = V.nil ∧ ms = []) ∨
    ∃ m l' ms', ms = m :: ms' ∧ (⟨l, V.first, m⟩ : Triple) ∈ G ∧
      (⟨l, V.rest, l'⟩ : Triple) ∈ G ∧ Chain G l' ms' := by
  cases h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons h1 h2 hr => exact Or.inr ⟨_, _, _, rfl, h1, h2, hr⟩

/-! The list `mixG` carries is read off it by these five decidable facts, which
say that each node has exactly one `rdf:first` and one `rdf:rest`, that nothing
hangs off `rdf:nil`, and that `Supplier` is the only intersection. -/

private theorem mix_l0_first : ∀ t ∈ mixG, t.s = mL0 → t.p = V.first → t.o = mVendor := by decide
private theorem mix_l0_rest : ∀ t ∈ mixG, t.s = mL0 → t.p = V.rest → t.o = mL1 := by decide
private theorem mix_l1_first : ∀ t ∈ mixG, t.s = mL1 → t.p = V.first → t.o = mApproved := by decide
private theorem mix_l1_rest : ∀ t ∈ mixG, t.s = mL1 → t.p = V.rest → t.o = V.nil := by decide
private theorem mix_no_nil_subject : ∀ t ∈ mixG, t.s ≠ V.nil := by decide
private theorem mix_only_int : ∀ t ∈ mixG, t.p = V.intersectionOf →
    t.s = mSupplier ∧ t.o = mL0 := by decide

private theorem mix_chain_nil : ∀ ms, Chain mixG V.nil ms → ms = [] := by
  intro ms h
  rcases chain_uncons h with ⟨_, rfl⟩ | ⟨_, _, _, _, h1, _, _⟩
  · rfl
  · exact absurd rfl (mix_no_nil_subject _ h1)

private theorem mix_chain_l1 : ∀ ms, Chain mixG mL1 ms → ms = [mApproved] := by
  intro ms h
  rcases chain_uncons h with ⟨hn, _⟩ | ⟨m, l', ms', rfl, h1, h2, hr⟩
  · exact absurd hn (by decide)
  · have hm : m = mApproved := mix_l1_first _ h1 rfl rfl
    have hl : l' = V.nil := mix_l1_rest _ h2 rfl rfl
    subst hm; subst hl
    rw [mix_chain_nil _ hr]

private theorem mix_chain_l0 : ∀ ms, Chain mixG mL0 ms → ms = [mVendor, mApproved] := by
  intro ms h
  rcases chain_uncons h with ⟨hn, _⟩ | ⟨m, l', ms', rfl, h1, h2, hr⟩
  · exact absurd hn (by decide)
  · have hm : m = mVendor := mix_l0_first _ h1 rfl rfl
    have hl : l' = mL1 := mix_l0_rest _ h2 rfl rfl
    subst hm; subst hl
    rw [mix_chain_l1 _ hr]

/-- `mixG` plus the one triple the semantics does force, `acme rdf:type Supplier`,
and nothing else. In particular no `u:status`. -/
def mixH : List Triple := ⟨mAcme, V.type, mSupplier⟩ :: mixG

private theorem mixH_int_closed : ∀ t ∈ mixH, ∀ u ∈ mixH,
    (t.p = V.type ∧ t.o = mVendor ∧ u.p = V.type ∧ u.o = mApproved ∧ u.s = t.s) →
      (⟨t.s, V.type, mSupplier⟩ : Triple) ∈ mixH := by decide

theorem mixH_is_a_model : Model (herbrand mixH) mixG where
  conds :=
    { sc_sub := fun a b hab => absurd hab (not_mem_pred mixH V.subClassOf (by decide) a b)
      sc_trans := fun a b _ hab => absurd hab (not_mem_pred mixH V.subClassOf (by decide) a b)
      sp_sub := fun a b hab => absurd hab (not_mem_pred mixH V.subPropertyOf (by decide) a b)
      sp_trans := fun a b _ hab =>
        absurd hab (not_mem_pred mixH V.subPropertyOf (by decide) a b)
      dom := fun p c hpc => absurd hpc (not_mem_pred mixH V.domain (by decide) p c)
      rng := fun p c hpc => absurd hpc (not_mem_pred mixH V.range (by decide) p c)
      trp := fun p hp => absurd hp (not_typed mixH V.transitiveProperty (by decide) p)
      symp := fun p hp => absurd hp (not_typed mixH V.symmetricProperty (by decide) p)
      inv := fun p q hpq => absurd hpq (not_mem_pred mixH V.inverseOf (by decide) p q)
      same := fun a b hab => absurd hab (not_mem_pred mixH V.sameAs (by decide) a b)
      eqc := fun a b hab => absurd hab (not_mem_pred mixH V.equivalentClass (by decide) a b)
      eqp := fun a b hab =>
        absurd hab (not_mem_pred mixH V.equivalentProperty (by decide) a b)
      svf := fun r p _ hop => absurd hop (not_mem_pred mixH V.onProperty (by decide) r p)
      avf := fun r p _ hop => absurd hop (not_mem_pred mixH V.onProperty (by decide) r p)
      hv := fun r p _ hop => absurd hop (not_mem_pred mixH V.onProperty (by decide) r p) }
  facts := fun t ht => List.mem_cons_of_mem _ ht
  int := by
    intro c l ms hc hchain x hx
    obtain ⟨rfl, rfl⟩ := mix_only_int _ hc rfl
    have hms := mix_chain_l0 ms hchain
    subst hms
    exact mixH_int_closed _ (hx mVendor (by simp)) _ (hx mApproved (by simp))
      ⟨rfl, rfl, rfl, rfl, rfl⟩
  uni := by
    intro c l _ hc
    exact absurd hc (not_mem_pred mixG V.unionOf (by decide) c l)

/-- **The distinction, machine-checked.** The certificate above was accepted and
its conclusion is entailed under the supplied rule. It is NOT entailed by the
asserted graph: `mixH` is a model of that graph in which acme has no status at
all. A run over this table may therefore report `entailed_under_supplied_rules`
and may never report `entailed`. -/
theorem mix_not_absolutely_entailed : ¬ Entails mixG ⟨mAcme, mStatus, mCompliant⟩ := fun h =>
  absurd (h (herbrand mixH) mixH_is_a_model)
    (by decide : (⟨mAcme, mStatus, mCompliant⟩ : Triple) ∉ mixH)

/-- `mixG` closed under the supplied rule as well. -/
def mixH2 : List Triple := ⟨mAcme, mStatus, mCompliant⟩ :: mixH

private theorem mixH2_int_closed : ∀ t ∈ mixH2, ∀ u ∈ mixH2,
    (t.p = V.type ∧ t.o = mVendor ∧ u.p = V.type ∧ u.o = mApproved ∧ u.s = t.s) →
      (⟨t.s, V.type, mSupplier⟩ : Triple) ∈ mixH2 := by decide

private theorem mixH2_rule_closed : ∀ t ∈ mixH2, t.p = V.type → t.o = mSupplier →
    (⟨t.s, mStatus, mCompliant⟩ : Triple) ∈ mixH2 := by decide

theorem mixH2_is_a_model : Model (herbrand mixH2) mixG where
  conds :=
    { sc_sub := fun a b hab => absurd hab (not_mem_pred mixH2 V.subClassOf (by decide) a b)
      sc_trans := fun a b _ hab => absurd hab (not_mem_pred mixH2 V.subClassOf (by decide) a b)
      sp_sub := fun a b hab => absurd hab (not_mem_pred mixH2 V.subPropertyOf (by decide) a b)
      sp_trans := fun a b _ hab =>
        absurd hab (not_mem_pred mixH2 V.subPropertyOf (by decide) a b)
      dom := fun p c hpc => absurd hpc (not_mem_pred mixH2 V.domain (by decide) p c)
      rng := fun p c hpc => absurd hpc (not_mem_pred mixH2 V.range (by decide) p c)
      trp := fun p hp => absurd hp (not_typed mixH2 V.transitiveProperty (by decide) p)
      symp := fun p hp => absurd hp (not_typed mixH2 V.symmetricProperty (by decide) p)
      inv := fun p q hpq => absurd hpq (not_mem_pred mixH2 V.inverseOf (by decide) p q)
      same := fun a b hab => absurd hab (not_mem_pred mixH2 V.sameAs (by decide) a b)
      eqc := fun a b hab => absurd hab (not_mem_pred mixH2 V.equivalentClass (by decide) a b)
      eqp := fun a b hab =>
        absurd hab (not_mem_pred mixH2 V.equivalentProperty (by decide) a b)
      svf := fun r p _ hop => absurd hop (not_mem_pred mixH2 V.onProperty (by decide) r p)
      avf := fun r p _ hop => absurd hop (not_mem_pred mixH2 V.onProperty (by decide) r p)
      hv := fun r p _ hop => absurd hop (not_mem_pred mixH2 V.onProperty (by decide) r p) }
  facts := fun t ht => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)
  int := by
    intro c l ms hc hchain x hx
    obtain ⟨rfl, rfl⟩ := mix_only_int _ hc rfl
    have hms := mix_chain_l0 ms hchain
    subst hms
    exact mixH2_int_closed _ (hx mVendor (by simp)) _ (hx mApproved (by simp))
      ⟨rfl, rfl, rfl, rfl, rfl⟩
  uni := by
    intro c l _ hc
    exact absurd hc (not_mem_pred mixG V.unionOf (by decide) c l)

theorem mixH2_sat_rule : SatRule (herbrand mixH2) complianceRule := by
  intro sigma hb
  have h1 : (⟨sigma "s", V.type, mSupplier⟩ : Triple) ∈ mixH2 :=
    hb ⟨.var "s", .const V.type, .const mSupplier⟩ (by simp [complianceRule])
  exact mixH2_rule_closed ⟨sigma "s", V.type, mSupplier⟩ h1 rfl rfl

/-- Adding the rule does not collapse entailment into "everything follows".
`Vendor` is not a `Supplier`, so nothing makes it compliant. -/
theorem mix_relative_is_not_everything :
    ¬ EntailsR mixG mixR ⟨mVendor, mStatus, mCompliant⟩ := by
  intro h
  have hrules : ∀ r ∈ mixR, SatRule (herbrand mixH2) r := by
    intro r hr
    have hre : r = complianceRule := List.mem_singleton.mp hr
    subst hre
    exact mixH2_sat_rule
  exact absurd (h (herbrand mixH2) ⟨mixH2_is_a_model, hrules⟩)
    (by decide : (⟨mVendor, mStatus, mCompliant⟩ : Triple) ∉ mixH2)

/-! ## The report, and why it cannot launder

A run has to say which of the two guarantees it earned, and decision 0003 puts
that in the verdict rather than in a footnote. These three functions are the
report surface. They are not plumbing that a reviewer has to trust:
`absolute_verdict_is_earned` proves that the absolute word is printed only for a
table the absolute theorem covers. -/

/-- Structural equality of rules. `RulePattern` does not derive `DecidableEq`,
and `Horn.lean` is not this file's to change, so it is written out. Comparing
the rules themselves rather than their rendered form is what makes
`sameTable_eq` provable, and `sameTable_eq` is what makes the verdict theorem
possible. -/
def sameRule (a b : RulePattern) : Bool :=
  a.name == b.name && a.body == b.body && a.head == b.head

def sameTable : List RulePattern → List RulePattern → Bool
  | [], [] => true
  | a :: as, b :: bs => sameRule a b && sameTable as bs
  | _, _ => false

theorem sameRule_eq {a b : RulePattern} (h : sameRule a b = true) : a = b := by
  unfold sameRule at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  cases a; cases b
  simp_all

theorem sameTable_eq : ∀ {A B : List RulePattern}, sameTable A B = true → A = B
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [sameTable] at h
  | _ :: _, [], h => by simp [sameTable] at h
  | _ :: _, _ :: _, h => by
      simp only [sameTable, Bool.and_eq_true] at h
      rw [sameRule_eq h.1, sameTable_eq h.2]

/-- Which of the three theorems a run over this table earned. -/
inductive Warrant
  | noRules | builtin | supplied
deriving DecidableEq, Repr

def warrantOf : List RulePattern → Warrant
  | [] => .noRules
  | r :: rs => if sameTable (r :: rs) Builtin.asHorn then .builtin else .supplied

theorem warrantOf_noRules : ∀ {R : List RulePattern}, warrantOf R = .noRules → R = []
  | [], _ => rfl
  | _ :: _, h => by
      simp only [warrantOf] at h
      split at h <;> exact absurd h (by decide)

theorem warrantOf_builtin : ∀ {R : List RulePattern},
    warrantOf R = .builtin → R = Builtin.asHorn
  | [], h => by simp only [warrantOf] at h; exact absurd h (by decide)
  | _ :: _, h => by
      simp only [warrantOf] at h
      split at h
      · rename_i hs; exact sameTable_eq hs
      · exact absurd h (by decide)

/-- The two verdicts never share a word. -/
def Warrant.verdict : Warrant → String
  | .noRules | .builtin => "entailed"
  | .supplied => "entailed_under_supplied_rules"

def Warrant.theoremName : Warrant → String
  | .noRules => "OOCert.mixed_certificate_sound_no_rules"
  | .builtin => "OOCert.mixed_certificate_sound_builtin"
  | .supplied => "OOCert.mixed_certificate_sound"

/-- What the run is conditional on, in the report itself. -/
def Warrant.means : Warrant → String
  | .noRules =>
      "every conclusion is true in every model of the asserted graph; this certificate cited \
       no rule table, so there is nothing it is conditional on"
  | .builtin =>
      "every conclusion is true in every model of the asserted graph"
  | .supplied =>
      "every conclusion is true in every model of the asserted graph THAT ALSO SATISFIES the \
       supplied rules; the rules themselves are assumed, not checked"

/-- **The verdict cannot launder an assumption into a fact.** Whenever the report
prints the absolute word for an accepted certificate, the absolute theorem
applies to that run. The relative case is the one this rules out, and
`mix_not_absolutely_entailed` shows it is a case that really arises. -/
theorem absolute_verdict_is_earned (G : List Triple) (R : List RulePattern) (steps : List MStep)
    (hv : (warrantOf R).verdict = "entailed")
    (h : checkCertM G R steps = true) : ∀ st ∈ steps, Entails G st.conclusion := by
  cases hw : warrantOf R with
  | noRules =>
    rw [warrantOf_noRules hw] at h
    exact mixed_certificate_sound_no_rules G steps h
  | builtin =>
    rw [warrantOf_builtin hw] at h
    exact mixed_certificate_sound_builtin G steps h
  | supplied =>
    rw [hw] at hv
    exact absurd hv (by decide)

/-- The table the worked certificate cites is not the built-in one, so it earns
the relative verdict. Read with `mix_not_absolutely_entailed`, that is the whole
of decision 0003 in two lines. -/
theorem mix_earns_only_the_relative_verdict :
    (warrantOf mixR).verdict = "entailed_under_supplied_rules" := by decide

/-! ## Axioms, pinned

As `Soundness.lean`, `Horn.lean` and `Witness.lean` pin theirs. A `sorry`, or a
`native_decide` anywhere under these, fails the build here. -/

/-- info: 'OOCert.mixed_certificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixed_certificate_sound

/-- info: 'OOCert.mixed_certificate_sound_builtin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixed_certificate_sound_builtin

/-- info: 'OOCert.absolute_verdict_is_earned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms absolute_verdict_is_earned

/-- info: 'OOCert.mix_conclusion_entailed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mix_conclusion_entailed

/-- info: 'OOCert.mix_not_absolutely_entailed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mix_not_absolutely_entailed

/-- info: 'OOCert.mix_relative_is_not_everything' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mix_relative_is_not_everything

end OOCert
