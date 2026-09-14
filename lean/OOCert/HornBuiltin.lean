import OOCert.Horn

/-!
# The hardcoded arms, as data

The question this file settles: is the generic Horn theorem a SECOND rule
family bolted on beside the per-rule arms, or does it SUBSUME them?

Twenty-five of the engine's twenty-nine rules are Horn rules over triple
patterns, written out below as values of `RulePattern`. Two of them license two
conclusions each, so the table has twenty-seven entries. For each, one lemma
says the semantic conditions in `Semantics.lean` imply the term-level rule.
Every one of those lemmas is a single `exact` against the matching field of
`Conditions`, because there is no premise-list destructuring left to do: the
checker did it.

`entails_of_horn` is then the payoff. A certificate that cites only rules with
such a lemma yields the ORIGINAL `Entails G t`, the same warrant
`certificate_sound` gives, with no per-rule arm in the checker and no per-rule
lemma about premise lists.

## The four that are not Horn rules, and why

`cls-int1`, `cls-int2`, `cls-uni` and `cls-oo` read an RDF list off the graph.
Their premise count is not fixed by the rule: it is the length of the list,
which is data. A `RulePattern` has a finite body, so expressing `cls-int1`
needs either one rule per list length, which is infinitely many rules, or an
atom that matches a chain, which is outside Horn logic over triple patterns.
They stay hardcoded. That is not a defect of the generalisation; it is the
exact boundary of the Horn family, and it is where a user-written rule language
will also stop.

`cls-int2` is the newest of the four and it lands on the same side for the same
reason, even though its premise list is shorter than `cls-int1`'s. What decides
the question is not how many instance premises a rule reads but whether the
LIST is one of them, and `cls-int2` reads the list to know which conclusions it
is allowed to draw. Its condition is therefore a field of `Model`, which sees
the graph, rather than of `Conditions`, which sees only the interpretation.
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

/-! ### The restriction-ordering and domain-and-range rules

Eight more, all of them Horn rules over triple patterns and none of them needing
anything the `RulePattern` language does not already have. The first four order
two restrictions on the same property or with the same filler; the last four
move a declared domain or range along the class and the property hierarchy.

`scmAvf2` concludes `?c2 rdfs:subClassOf ?c1`, the reverse of the other three.
That is the W3C table, not a typo here: a universal restriction is antitone in
its property. The `Conditions` field it appeals to is stated the same way round,
so a head written the natural way would fail to typecheck. -/

def scmSvf1 : RulePattern :=
  { name := "scm-svf1"
    body := [⟨.var "c1", .const V.someValuesFrom, .var "y1"⟩,
             ⟨.var "c1", .const V.onProperty, .var "p"⟩,
             ⟨.var "c2", .const V.someValuesFrom, .var "y2"⟩,
             ⟨.var "c2", .const V.onProperty, .var "p"⟩,
             ⟨.var "y1", .const V.subClassOf, .var "y2"⟩]
    head := ⟨.var "c1", .const V.subClassOf, .var "c2"⟩ }

def scmSvf2 : RulePattern :=
  { name := "scm-svf2"
    body := [⟨.var "c1", .const V.someValuesFrom, .var "y"⟩,
             ⟨.var "c1", .const V.onProperty, .var "p1"⟩,
             ⟨.var "c2", .const V.someValuesFrom, .var "y"⟩,
             ⟨.var "c2", .const V.onProperty, .var "p2"⟩,
             ⟨.var "p1", .const V.subPropertyOf, .var "p2"⟩]
    head := ⟨.var "c1", .const V.subClassOf, .var "c2"⟩ }

def scmAvf1 : RulePattern :=
  { name := "scm-avf1"
    body := [⟨.var "c1", .const V.allValuesFrom, .var "y1"⟩,
             ⟨.var "c1", .const V.onProperty, .var "p"⟩,
             ⟨.var "c2", .const V.allValuesFrom, .var "y2"⟩,
             ⟨.var "c2", .const V.onProperty, .var "p"⟩,
             ⟨.var "y1", .const V.subClassOf, .var "y2"⟩]
    head := ⟨.var "c1", .const V.subClassOf, .var "c2"⟩ }

/-- Head REVERSED, `?c2 rdfs:subClassOf ?c1`. See the note above. -/
def scmAvf2 : RulePattern :=
  { name := "scm-avf2"
    body := [⟨.var "c1", .const V.allValuesFrom, .var "y"⟩,
             ⟨.var "c1", .const V.onProperty, .var "p1"⟩,
             ⟨.var "c2", .const V.allValuesFrom, .var "y"⟩,
             ⟨.var "c2", .const V.onProperty, .var "p2"⟩,
             ⟨.var "p1", .const V.subPropertyOf, .var "p2"⟩]
    head := ⟨.var "c2", .const V.subClassOf, .var "c1"⟩ }

def scmDom1 : RulePattern :=
  { name := "scm-dom1"
    body := [⟨.var "p", .const V.domain, .var "c1"⟩,
             ⟨.var "c1", .const V.subClassOf, .var "c2"⟩]
    head := ⟨.var "p", .const V.domain, .var "c2"⟩ }

def scmDom2 : RulePattern :=
  { name := "scm-dom2"
    body := [⟨.var "p2", .const V.domain, .var "c"⟩,
             ⟨.var "p1", .const V.subPropertyOf, .var "p2"⟩]
    head := ⟨.var "p1", .const V.domain, .var "c"⟩ }

def scmRng1 : RulePattern :=
  { name := "scm-rng1"
    body := [⟨.var "p", .const V.range, .var "c1"⟩,
             ⟨.var "c1", .const V.subClassOf, .var "c2"⟩]
    head := ⟨.var "p", .const V.range, .var "c2"⟩ }

def scmRng2 : RulePattern :=
  { name := "scm-rng2"
    body := [⟨.var "p2", .const V.range, .var "c"⟩,
             ⟨.var "p1", .const V.subPropertyOf, .var "p2"⟩]
    head := ⟨.var "p1", .const V.range, .var "c"⟩ }

/-! ## Each is a consequence of the semantic conditions

One `exact` each. Compare `Soundness.lean`, where the same facts cost
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

theorem scmSvf1_sound {I : Interp} (C : Conditions I) : SatRule I scmSvf1 := fun s hb =>
  C.svf_sc _ _ _ _ _
    (hb ⟨.var "c1", .const V.someValuesFrom, .var "y1"⟩ (by simp [scmSvf1]))
    (hb ⟨.var "c1", .const V.onProperty, .var "p"⟩ (by simp [scmSvf1]))
    (hb ⟨.var "c2", .const V.someValuesFrom, .var "y2"⟩ (by simp [scmSvf1]))
    (hb ⟨.var "c2", .const V.onProperty, .var "p"⟩ (by simp [scmSvf1]))
    (hb ⟨.var "y1", .const V.subClassOf, .var "y2"⟩ (by simp [scmSvf1]))

theorem scmSvf2_sound {I : Interp} (C : Conditions I) : SatRule I scmSvf2 := fun s hb =>
  C.svf_sp _ _ _ _ _
    (hb ⟨.var "c1", .const V.someValuesFrom, .var "y"⟩ (by simp [scmSvf2]))
    (hb ⟨.var "c1", .const V.onProperty, .var "p1"⟩ (by simp [scmSvf2]))
    (hb ⟨.var "c2", .const V.someValuesFrom, .var "y"⟩ (by simp [scmSvf2]))
    (hb ⟨.var "c2", .const V.onProperty, .var "p2"⟩ (by simp [scmSvf2]))
    (hb ⟨.var "p1", .const V.subPropertyOf, .var "p2"⟩ (by simp [scmSvf2]))

theorem scmAvf1_sound {I : Interp} (C : Conditions I) : SatRule I scmAvf1 := fun s hb =>
  C.avf_sc _ _ _ _ _
    (hb ⟨.var "c1", .const V.allValuesFrom, .var "y1"⟩ (by simp [scmAvf1]))
    (hb ⟨.var "c1", .const V.onProperty, .var "p"⟩ (by simp [scmAvf1]))
    (hb ⟨.var "c2", .const V.allValuesFrom, .var "y2"⟩ (by simp [scmAvf1]))
    (hb ⟨.var "c2", .const V.onProperty, .var "p"⟩ (by simp [scmAvf1]))
    (hb ⟨.var "y1", .const V.subClassOf, .var "y2"⟩ (by simp [scmAvf1]))

/-- The head is `?c2 rdfs:subClassOf ?c1` and `avf_sp` concludes `I.sc c2 c1`.
Swap either one and this `exact` stops typechecking, which is the point of
having the direction in two places rather than one. -/
theorem scmAvf2_sound {I : Interp} (C : Conditions I) : SatRule I scmAvf2 := fun s hb =>
  C.avf_sp _ _ _ _ _
    (hb ⟨.var "c1", .const V.allValuesFrom, .var "y"⟩ (by simp [scmAvf2]))
    (hb ⟨.var "c1", .const V.onProperty, .var "p1"⟩ (by simp [scmAvf2]))
    (hb ⟨.var "c2", .const V.allValuesFrom, .var "y"⟩ (by simp [scmAvf2]))
    (hb ⟨.var "c2", .const V.onProperty, .var "p2"⟩ (by simp [scmAvf2]))
    (hb ⟨.var "p1", .const V.subPropertyOf, .var "p2"⟩ (by simp [scmAvf2]))

theorem scmDom1_sound {I : Interp} (C : Conditions I) : SatRule I scmDom1 := fun s hb =>
  C.dom_sc _ _ _ (hb ⟨.var "p", .const V.domain, .var "c1"⟩ (by simp [scmDom1]))
    (hb ⟨.var "c1", .const V.subClassOf, .var "c2"⟩ (by simp [scmDom1]))

theorem scmDom2_sound {I : Interp} (C : Conditions I) : SatRule I scmDom2 := fun s hb =>
  C.dom_sp _ _ _ (hb ⟨.var "p2", .const V.domain, .var "c"⟩ (by simp [scmDom2]))
    (hb ⟨.var "p1", .const V.subPropertyOf, .var "p2"⟩ (by simp [scmDom2]))

theorem scmRng1_sound {I : Interp} (C : Conditions I) : SatRule I scmRng1 := fun s hb =>
  C.rng_sc _ _ _ (hb ⟨.var "p", .const V.range, .var "c1"⟩ (by simp [scmRng1]))
    (hb ⟨.var "c1", .const V.subClassOf, .var "c2"⟩ (by simp [scmRng1]))

theorem scmRng2_sound {I : Interp} (C : Conditions I) : SatRule I scmRng2 := fun s hb =>
  C.rng_sp _ _ _ (hb ⟨.var "p2", .const V.range, .var "c"⟩ (by simp [scmRng2]))
    (hb ⟨.var "p1", .const V.subPropertyOf, .var "p2"⟩ (by simp [scmRng2]))

/-- The built-in rules that are Horn rules, as a rule set. Twenty-seven of the
twenty-nine rule ids the engine emits qualify; `cls-int1`, `cls-int2`, `cls-uni`
and `cls-oo` do not, for the reason given at the top of this file, and
`scm-eqc1` and `scm-eqp1` each contribute two entries because each licenses two
conclusions.

The ORDER is a contract. A certificate cites a rule by its index into this
list, so the nineteen entries that were here before keep the positions they
had, and anything new is appended. -/
def asHorn : List RulePattern :=
  [rdfs2, rdfs3, rdfs5, rdfs7, rdfs9, rdfs11,
   prpTrp, prpSymp, prpInv1, prpInv2, eqSym,
   scmEqc1, scmEqc1b, scmEqp1, scmEqp1b, clsSvf1, clsAvf, clsHv1, clsHv2,
   scmSvf1, scmSvf2, scmAvf1, scmAvf2, scmDom1, scmDom2, scmRng1, scmRng2]

theorem asHorn_sound (I : Interp) (C : Conditions I) : ∀ r ∈ asHorn, SatRule I r := by
  intro r hr
  simp only [asHorn, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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
  · exact scmSvf1_sound C
  · exact scmSvf2_sound C
  · exact scmAvf1_sound C
  · exact scmAvf2_sound C
  · exact scmDom1_sound C
  · exact scmDom2_sound C
  · exact scmRng1_sound C
  · exact scmRng2_sound C

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
