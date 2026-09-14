import OOCert.Horn

/-!
# The hardcoded arms, as data

The question this file settles: is the generic Horn theorem a SECOND rule
family bolted on beside the twenty arms, or does it SUBSUME them?

Nineteen of the engine's rules are Horn rules over triple patterns, written out below
as values of `RulePattern`. For each, one lemma says the semantic conditions in
`Semantics.lean` imply the term-level rule. Every one of those lemmas is a
single `exact` against the matching field of `Conditions`, because there is no
premise-list destructuring left to do: the checker did it.

`entails_of_horn` is then the payoff. A certificate that cites only rules with
such a lemma yields the ORIGINAL `Entails G t`, the same warrant
`certificate_sound` gives, with no per-rule arm in the checker and no per-rule
lemma about premise lists.

## The two that are not Horn rules, and why

`cls-int1` and `cls-uni` read an RDF list off the graph. Their premise count is
not fixed by the rule: it is the length of the list, which is data. A
`RulePattern` has a finite body, so expressing `cls-int1` needs either one rule
per list length, which is infinitely many rules, or an atom that matches a
chain, which is outside Horn logic over triple patterns. They stay hardcoded.
That is not a defect of the generalisation; it is the exact boundary of the
Horn family, and it is where a user-written rule language will also stop.
-/
namespace OOCert
namespace Builtin

def rdfs2 : RulePattern :=
  { name := "rdfs2"
    body := [⟨.var "s", .var "p", .var "o"⟩, ⟨.var "p", .const V.domain, .var "c"⟩]
    head := ⟨.var "s", .const V.type, .var "c"⟩ }

def rdfs3 : RulePattern :=
  { name := "rdfs3"
    body := [⟨.var "s", .var "p", .var "o"⟩, ⟨.var "p", .const V.range, .var "c"⟩]
    head := ⟨.var "o", .const V.type, .var "c"⟩ }

def rdfs5 : RulePattern :=
  { name := "rdfs5"
    body := [⟨.var "a", .const V.subPropertyOf, .var "b"⟩,
             ⟨.var "b", .const V.subPropertyOf, .var "c"⟩]
    head := ⟨.var "a", .const V.subPropertyOf, .var "c"⟩ }

def rdfs7 : RulePattern :=
  { name := "rdfs7"
    body := [⟨.var "s", .var "p", .var "o"⟩,
             ⟨.var "p", .const V.subPropertyOf, .var "q"⟩]
    head := ⟨.var "s", .var "q", .var "o"⟩ }

def rdfs9 : RulePattern :=
  { name := "rdfs9"
    body := [⟨.var "x", .const V.type, .var "a"⟩,
             ⟨.var "a", .const V.subClassOf, .var "b"⟩]
    head := ⟨.var "x", .const V.type, .var "b"⟩ }

def rdfs11 : RulePattern :=
  { name := "rdfs11"
    body := [⟨.var "a", .const V.subClassOf, .var "b"⟩,
             ⟨.var "b", .const V.subClassOf, .var "c"⟩]
    head := ⟨.var "a", .const V.subClassOf, .var "c"⟩ }

def prpTrp : RulePattern :=
  { name := "prp-trp"
    body := [⟨.var "p", .const V.type, .const V.transitiveProperty⟩,
             ⟨.var "x", .var "p", .var "y"⟩,
             ⟨.var "y", .var "p", .var "z"⟩]
    head := ⟨.var "x", .var "p", .var "z"⟩ }

def prpSymp : RulePattern :=
  { name := "prp-symp"
    body := [⟨.var "p", .const V.type, .const V.symmetricProperty⟩,
             ⟨.var "x", .var "p", .var "y"⟩]
    head := ⟨.var "y", .var "p", .var "x"⟩ }

def prpInv1 : RulePattern :=
  { name := "prp-inv1"
    body := [⟨.var "p", .const V.inverseOf, .var "q"⟩, ⟨.var "x", .var "p", .var "y"⟩]
    head := ⟨.var "y", .var "q", .var "x"⟩ }

def prpInv2 : RulePattern :=
  { name := "prp-inv2"
    body := [⟨.var "p", .const V.inverseOf, .var "q"⟩, ⟨.var "x", .var "q", .var "y"⟩]
    head := ⟨.var "y", .var "p", .var "x"⟩ }

def eqSym : RulePattern :=
  { name := "eq-sym"
    body := [⟨.var "a", .const V.sameAs, .var "b"⟩]
    head := ⟨.var "b", .const V.sameAs, .var "a"⟩ }

def scmEqc1 : RulePattern :=
  { name := "scm-eqc1"
    body := [⟨.var "a", .const V.equivalentClass, .var "b"⟩]
    head := ⟨.var "a", .const V.subClassOf, .var "b"⟩ }

/-- The second conclusion of W3C `scm-eqc1`, which licenses two. It is emitted
under that rule's own id, because `scm-eqc2` names a different W3C rule
concluding in the opposite direction. -/
def scmEqc1b : RulePattern :=
  { name := "scm-eqc1"
    body := [⟨.var "a", .const V.equivalentClass, .var "b"⟩]
    head := ⟨.var "b", .const V.subClassOf, .var "a"⟩ }

def scmEqp1 : RulePattern :=
  { name := "scm-eqp1"
    body := [⟨.var "a", .const V.equivalentProperty, .var "b"⟩]
    head := ⟨.var "a", .const V.subPropertyOf, .var "b"⟩ }

/-- The second conclusion of W3C `scm-eqp1`. See `scmEqc1b`. -/
def scmEqp1b : RulePattern :=
  { name := "scm-eqp1"
    body := [⟨.var "a", .const V.equivalentProperty, .var "b"⟩]
    head := ⟨.var "b", .const V.subPropertyOf, .var "a"⟩ }

def clsSvf1 : RulePattern :=
  { name := "cls-svf1"
    body := [⟨.var "r", .const V.onProperty, .var "p"⟩,
             ⟨.var "r", .const V.someValuesFrom, .var "c"⟩,
             ⟨.var "x", .var "p", .var "y"⟩,
             ⟨.var "y", .const V.type, .var "c"⟩]
    head := ⟨.var "x", .const V.type, .var "r"⟩ }

def clsAvf : RulePattern :=
  { name := "cls-avf"
    body := [⟨.var "r", .const V.onProperty, .var "p"⟩,
             ⟨.var "r", .const V.allValuesFrom, .var "c"⟩,
             ⟨.var "x", .const V.type, .var "r"⟩,
             ⟨.var "x", .var "p", .var "y"⟩]
    head := ⟨.var "y", .const V.type, .var "c"⟩ }

def clsHv1 : RulePattern :=
  { name := "cls-hv1"
    body := [⟨.var "r", .const V.onProperty, .var "p"⟩,
             ⟨.var "r", .const V.hasValue, .var "v"⟩,
             ⟨.var "x", .const V.type, .var "r"⟩]
    head := ⟨.var "x", .var "p", .var "v"⟩ }

def clsHv2 : RulePattern :=
  { name := "cls-hv2"
    body := [⟨.var "r", .const V.onProperty, .var "p"⟩,
             ⟨.var "r", .const V.hasValue, .var "v"⟩,
             ⟨.var "x", .var "p", .var "v"⟩]
    head := ⟨.var "x", .const V.type, .var "r"⟩ }

/-! ## Each is a consequence of the semantic conditions

One `exact` each. Compare `Soundness.lean`, where the same eighteen facts cost
a `rcases` over the premise list, a `simp only` to strip the decidability
wrapper, an `obtain` over the conjunction, and then the `exact`. -/

theorem rdfs2_sound {I : Interp} (C : Conditions I) : SatRule I rdfs2 := fun s hb =>
  C.dom _ _ (hb ⟨.var "p", .const V.domain, .var "c"⟩ (by simp [rdfs2])) _ _
    (hb ⟨.var "s", .var "p", .var "o"⟩ (by simp [rdfs2]))

theorem rdfs3_sound {I : Interp} (C : Conditions I) : SatRule I rdfs3 := fun s hb =>
  C.rng _ _ (hb ⟨.var "p", .const V.range, .var "c"⟩ (by simp [rdfs3])) _ _
    (hb ⟨.var "s", .var "p", .var "o"⟩ (by simp [rdfs3]))

theorem rdfs5_sound {I : Interp} (C : Conditions I) : SatRule I rdfs5 := fun s hb =>
  C.sp_trans _ _ _ (hb ⟨.var "a", .const V.subPropertyOf, .var "b"⟩ (by simp [rdfs5]))
    (hb ⟨.var "b", .const V.subPropertyOf, .var "c"⟩ (by simp [rdfs5]))

theorem rdfs7_sound {I : Interp} (C : Conditions I) : SatRule I rdfs7 := fun s hb =>
  C.sp_sub _ _ (hb ⟨.var "p", .const V.subPropertyOf, .var "q"⟩ (by simp [rdfs7])) _ _
    (hb ⟨.var "s", .var "p", .var "o"⟩ (by simp [rdfs7]))

theorem rdfs9_sound {I : Interp} (C : Conditions I) : SatRule I rdfs9 := fun s hb =>
  C.sc_sub _ _ (hb ⟨.var "a", .const V.subClassOf, .var "b"⟩ (by simp [rdfs9])) _
    (hb ⟨.var "x", .const V.type, .var "a"⟩ (by simp [rdfs9]))

theorem rdfs11_sound {I : Interp} (C : Conditions I) : SatRule I rdfs11 := fun s hb =>
  C.sc_trans _ _ _ (hb ⟨.var "a", .const V.subClassOf, .var "b"⟩ (by simp [rdfs11]))
    (hb ⟨.var "b", .const V.subClassOf, .var "c"⟩ (by simp [rdfs11]))

theorem prpTrp_sound {I : Interp} (C : Conditions I) : SatRule I prpTrp := fun s hb =>
  C.trp _ (hb ⟨.var "p", .const V.type, .const V.transitiveProperty⟩ (by simp [prpTrp])) _ _ _
    (hb ⟨.var "x", .var "p", .var "y"⟩ (by simp [prpTrp]))
    (hb ⟨.var "y", .var "p", .var "z"⟩ (by simp [prpTrp]))

theorem prpSymp_sound {I : Interp} (C : Conditions I) : SatRule I prpSymp := fun s hb =>
  C.symp _ (hb ⟨.var "p", .const V.type, .const V.symmetricProperty⟩ (by simp [prpSymp])) _ _
    (hb ⟨.var "x", .var "p", .var "y"⟩ (by simp [prpSymp]))

theorem prpInv1_sound {I : Interp} (C : Conditions I) : SatRule I prpInv1 := fun s hb =>
  (C.inv _ _ (hb ⟨.var "p", .const V.inverseOf, .var "q"⟩ (by simp [prpInv1])) _ _).mp
    (hb ⟨.var "x", .var "p", .var "y"⟩ (by simp [prpInv1]))

theorem prpInv2_sound {I : Interp} (C : Conditions I) : SatRule I prpInv2 := fun s hb =>
  (C.inv _ _ (hb ⟨.var "p", .const V.inverseOf, .var "q"⟩ (by simp [prpInv2])) _ _).mpr
    (hb ⟨.var "x", .var "q", .var "y"⟩ (by simp [prpInv2]))

theorem eqSym_sound {I : Interp} (C : Conditions I) : SatRule I eqSym := by
  intro s hb
  have h1 : I.iext (I.ι V.sameAs) (I.ι (s "a")) (I.ι (s "b")) :=
    hb ⟨.var "a", .const V.sameAs, .var "b"⟩ (by simp [eqSym])
  have e : I.ι (s "a") = I.ι (s "b") := C.same _ _ h1
  show I.iext (I.ι V.sameAs) (I.ι (s "b")) (I.ι (s "a"))
  rw [← e]
  rw [← e] at h1
  exact h1

theorem scmEqc1_sound {I : Interp} (C : Conditions I) : SatRule I scmEqc1 := fun s hb =>
  (C.eqc _ _ (hb ⟨.var "a", .const V.equivalentClass, .var "b"⟩ (by simp [scmEqc1]))).1

theorem scmEqc1b_sound {I : Interp} (C : Conditions I) : SatRule I scmEqc1b := fun s hb =>
  (C.eqc _ _ (hb ⟨.var "a", .const V.equivalentClass, .var "b"⟩ (by simp [scmEqc1b]))).2

theorem scmEqp1_sound {I : Interp} (C : Conditions I) : SatRule I scmEqp1 := fun s hb =>
  (C.eqp _ _ (hb ⟨.var "a", .const V.equivalentProperty, .var "b"⟩ (by simp [scmEqp1]))).1

theorem scmEqp1b_sound {I : Interp} (C : Conditions I) : SatRule I scmEqp1b := fun s hb =>
  (C.eqp _ _ (hb ⟨.var "a", .const V.equivalentProperty, .var "b"⟩ (by simp [scmEqp1b]))).2

theorem clsSvf1_sound {I : Interp} (C : Conditions I) : SatRule I clsSvf1 := fun s hb =>
  C.svf _ _ _ (hb ⟨.var "r", .const V.onProperty, .var "p"⟩ (by simp [clsSvf1]))
    (hb ⟨.var "r", .const V.someValuesFrom, .var "c"⟩ (by simp [clsSvf1])) _ _
    (hb ⟨.var "x", .var "p", .var "y"⟩ (by simp [clsSvf1]))
    (hb ⟨.var "y", .const V.type, .var "c"⟩ (by simp [clsSvf1]))

theorem clsAvf_sound {I : Interp} (C : Conditions I) : SatRule I clsAvf := fun s hb =>
  C.avf _ _ _ (hb ⟨.var "r", .const V.onProperty, .var "p"⟩ (by simp [clsAvf]))
    (hb ⟨.var "r", .const V.allValuesFrom, .var "c"⟩ (by simp [clsAvf])) _ _
    (hb ⟨.var "x", .const V.type, .var "r"⟩ (by simp [clsAvf]))
    (hb ⟨.var "x", .var "p", .var "y"⟩ (by simp [clsAvf]))

theorem clsHv1_sound {I : Interp} (C : Conditions I) : SatRule I clsHv1 := fun s hb =>
  (C.hv _ _ _ (hb ⟨.var "r", .const V.onProperty, .var "p"⟩ (by simp [clsHv1]))
    (hb ⟨.var "r", .const V.hasValue, .var "v"⟩ (by simp [clsHv1])) _).mp
    (hb ⟨.var "x", .const V.type, .var "r"⟩ (by simp [clsHv1]))

theorem clsHv2_sound {I : Interp} (C : Conditions I) : SatRule I clsHv2 := fun s hb =>
  (C.hv _ _ _ (hb ⟨.var "r", .const V.onProperty, .var "p"⟩ (by simp [clsHv2]))
    (hb ⟨.var "r", .const V.hasValue, .var "v"⟩ (by simp [clsHv2])) _).mpr
    (hb ⟨.var "x", .var "p", .var "v"⟩ (by simp [clsHv2]))

/-- The built-in rules that are Horn rules, as a rule set. Nineteen of the
engine's rules qualify; `cls-int1` and `cls-uni` do not, for the reason given
at the top of this file. -/
def asHorn : List RulePattern :=
  [rdfs2, rdfs3, rdfs5, rdfs7, rdfs9, rdfs11,
   prpTrp, prpSymp, prpInv1, prpInv2, eqSym,
   scmEqc1, scmEqc1b, scmEqp1, scmEqp1b, clsSvf1, clsAvf, clsHv1, clsHv2]

theorem asHorn_sound (I : Interp) (C : Conditions I) : ∀ r ∈ asHorn, SatRule I r := by
  intro r hr
  simp only [asHorn, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact rdfs2_sound C
  · exact rdfs3_sound C
  · exact rdfs5_sound C
  · exact rdfs7_sound C
  · exact rdfs9_sound C
  · exact rdfs11_sound C
  · exact prpTrp_sound C
  · exact prpSymp_sound C
  · exact prpInv1_sound C
  · exact prpInv2_sound C
  · exact eqSym_sound C
  · exact scmEqc1_sound C
  · exact scmEqc1b_sound C
  · exact scmEqp1_sound C
  · exact scmEqp1b_sound C
  · exact clsSvf1_sound C
  · exact clsAvf_sound C
  · exact clsHv1_sound C
  · exact clsHv2_sound C

end Builtin

/-- If every rule in `R` follows from the semantic conditions, a Horn
certificate over `R` delivers the plain `Entails G t` of `Semantics.lean`: the
same warrant `certificate_sound` gives, with the rules moved out of the checker
and into data. -/
theorem entails_of_horn (G : List Triple) (R : List RulePattern)
    (hR : ∀ r ∈ R, ∀ I : Interp, Conditions I → SatRule I r)
    (steps : List HornStep) (h : checkHornCert G R steps = true) :
    ∀ st ∈ steps, Entails G st.conclusion := by
  intro st hst I M
  exact horn_certificate_sound G R steps h st hst I ⟨M, fun r hr => hR r hr I M.conds⟩

/-- Specialised to the built-ins. A certificate written against this rule set is
checked by code that knows nothing about RDFS or OWL, and still yields the
original entailment. -/
theorem entails_of_builtin_horn (G : List Triple) (steps : List HornStep)
    (h : checkHornCert G Builtin.asHorn steps = true) :
    ∀ st ∈ steps, Entails G st.conclusion :=
  entails_of_horn G Builtin.asHorn (fun r hr I C => Builtin.asHorn_sound I C r hr) steps h

/-- info: 'OOCert.entails_of_builtin_horn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entails_of_builtin_horn

end OOCert
