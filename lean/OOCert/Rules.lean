import Std.Data.HashSet
import OOCert.Semantics

/-!
# Rules and the checker

A certificate is a list of steps. Each step names a rule, lists the premises
the engine used, and states the conclusion. `checkStep` re-derives the
conclusion from the premises by pattern alone: it checks that the premises
have the shape the rule requires, that each is asserted or was concluded by an
earlier step, and that the conclusion is the one the rule produces from them.
It does no search. That is what keeps it small and what makes
`certificate_sound` (in `Soundness.lean`) a short proof.

## Premise order is part of the contract

The engine writes premises in the order listed with each rule below, and the
checker matches on that order. A certificate with the right triples in the
wrong order is rejected, which is a false alarm and never a false pass.

| rule       | premises                                                        | conclusion       |
|------------|-----------------------------------------------------------------|------------------|
| rdfs2      | `s p o`, `p rdfs:domain c`                                      | `s rdf:type c`   |
| rdfs3      | `s p o`, `p rdfs:range c`                                       | `o rdf:type c`   |
| rdfs5      | `a sp b`, `b sp c`                                              | `a sp c`         |
| rdfs7      | `s p o`, `p sp q`                                               | `s q o`          |
| rdfs9      | `x rdf:type a`, `a sc b`                                        | `x rdf:type b`   |
| rdfs11     | `a sc b`, `b sc c`                                              | `a sc c`         |
| prp-trp    | `p rdf:type owl:TransitiveProperty`, `x p y`, `y p z`           | `x p z`          |
| prp-symp   | `p rdf:type owl:SymmetricProperty`, `x p y`                     | `y p x`          |
| prp-inv1   | `p owl:inverseOf q`, `x p y`                                    | `y q x`          |
| prp-inv2   | `p owl:inverseOf q`, `x q y`                                    | `y p x`          |
| eq-sym     | `a owl:sameAs b`                                                | `b owl:sameAs a` |
| scm-eqc1   | `a owl:equivalentClass b`                                       | `a sc b` or `b sc a` |
| scm-eqp1   | `a owl:equivalentProperty b`                                    | `a sp b` or `b sp a` |
| cls-svf1   | `r owl:onProperty p`, `r owl:someValuesFrom c`, `x p y`, `y rdf:type c` | `x rdf:type r` |
| cls-avf    | `r owl:onProperty p`, `r owl:allValuesFrom c`, `x rdf:type r`, `x p y` | `y rdf:type c` |
| cls-hv1    | `r owl:onProperty p`, `r owl:hasValue v`, `x rdf:type r`        | `x p v`          |
| cls-hv2    | `r owl:onProperty p`, `r owl:hasValue v`, `x p v`               | `x rdf:type r`   |
| cls-int1   | `c owl:intersectionOf l`, the list chain of `l`, `x rdf:type m` for every member `m` | `x rdf:type c` |
| cls-int2   | `c owl:intersectionOf l`, the list chain of `l`, `x rdf:type c`  | `x rdf:type m` for one member `m` |
| cls-uni    | `c owl:unionOf l`, the list chain of `l`, `x rdf:type m` for one member `m` | `x rdf:type c` |
| cls-oo     | `c owl:oneOf l`, the list chain of `l`                           | `m rdf:type c` for one member `m` |
| scm-svf1   | `c1 svf y1`, `c1 onProperty p`, `c2 svf y2`, `c2 onProperty p`, `y1 sc y2` | `c1 sc c2`  |
| scm-svf2   | `c1 svf y`, `c1 onProperty p1`, `c2 svf y`, `c2 onProperty p2`, `p1 sp p2` | `c1 sc c2`  |
| scm-avf1   | `c1 avf y1`, `c1 onProperty p`, `c2 avf y2`, `c2 onProperty p`, `y1 sc y2` | `c1 sc c2`  |
| scm-avf2   | `c1 avf y`, `c1 onProperty p1`, `c2 avf y`, `c2 onProperty p2`, `p1 sp p2` | **`c2 sc c1`** |
| scm-dom1   | `p rdfs:domain c1`, `c1 sc c2`                                   | `p rdfs:domain c2` |
| scm-dom2   | `p2 rdfs:domain c`, `p1 sp p2`                                   | `p1 rdfs:domain c` |
| scm-rng1   | `p rdfs:range c1`, `c1 sc c2`                                    | `p rdfs:range c2`  |
| scm-rng2   | `p2 rdfs:range c`, `p1 sp p2`                                    | `p1 rdfs:range c`  |

`scm-avf2` is bold because its conclusion is the reverse of the other three
restriction-ordering rules, and a checker that got it the natural way round
would accept an unsound step. The W3C table reads
`T(?c2, rdfs:subClassOf, ?c1)`; see the `avf_sp` condition in
`Semantics.lean` and the refutation in `Witness.lean`.

The list chain is the sequence `l rdf:first m₁`, `l rdf:rest l₂`,
`l₂ rdf:first m₂`, `l₂ rdf:rest l₃`, … down to a node whose `rdf:rest` is
`rdf:nil`. The chain and the constructor triple must be asserted, not derived,
because `Model` reads lists off the asserted graph.

`cls-int2` and `cls-oo` license one conclusion per list member, so a
certificate carries one step per member, each repeating the constructor triple
and the chain. `cls-oo` has no premise beyond those two: an enumeration types
its members on schema alone.

`scm-eqc1` and `scm-eqp1` each license TWO conclusions from one premise, so a
certificate carries two steps under one rule id and the checker accepts either
conclusion. They used to emit the second under the ids `scm-eqc2` and `scm-eqp2`,
which name different W3C rules concluding in the opposite direction. Those names
are now free for the rules that own them.
-/
namespace OOCert

inductive Rule
  | rdfs2 | rdfs3 | rdfs5 | rdfs7 | rdfs9 | rdfs11
  | prpTrp | prpSymp | prpInv1 | prpInv2 | eqSym
  | scmEqc1 | scmEqp1
  | clsSvf1 | clsAvf | clsHv1 | clsHv2 | clsInt1 | clsInt2 | clsUni | clsOo
  | scmSvf1 | scmSvf2 | scmAvf1 | scmAvf2
  | scmDom1 | scmDom2 | scmRng1 | scmRng2
deriving DecidableEq, Repr

def Rule.name : Rule → String
  | .rdfs2 => "rdfs2" | .rdfs3 => "rdfs3" | .rdfs5 => "rdfs5" | .rdfs7 => "rdfs7"
  | .rdfs9 => "rdfs9" | .rdfs11 => "rdfs11"
  | .prpTrp => "prp-trp" | .prpSymp => "prp-symp" | .prpInv1 => "prp-inv1"
  | .prpInv2 => "prp-inv2" | .eqSym => "eq-sym"
  | .scmEqc1 => "scm-eqc1" | .scmEqp1 => "scm-eqp1"
  | .clsSvf1 => "cls-svf1" | .clsAvf => "cls-avf"
  | .clsHv1 => "cls-hv1" | .clsHv2 => "cls-hv2"
  | .clsInt1 => "cls-int1" | .clsInt2 => "cls-int2"
  | .clsUni => "cls-uni" | .clsOo => "cls-oo"
  | .scmSvf1 => "scm-svf1" | .scmSvf2 => "scm-svf2"
  | .scmAvf1 => "scm-avf1" | .scmAvf2 => "scm-avf2"
  | .scmDom1 => "scm-dom1" | .scmDom2 => "scm-dom2"
  | .scmRng1 => "scm-rng1" | .scmRng2 => "scm-rng2"

def Rule.all : List Rule :=
  [.rdfs2, .rdfs3, .rdfs5, .rdfs7, .rdfs9, .rdfs11,
   .prpTrp, .prpSymp, .prpInv1, .prpInv2, .eqSym,
   .scmEqc1, .scmEqp1,
   .clsSvf1, .clsAvf, .clsHv1, .clsHv2, .clsInt1, .clsInt2, .clsUni, .clsOo,
   .scmSvf1, .scmSvf2, .scmAvf1, .scmAvf2,
   .scmDom1, .scmDom2, .scmRng1, .scmRng2]

def Rule.ofName? (s : String) : Option Rule :=
  Rule.all.find? (fun r => r.name == s)

structure Step where
  rule : Rule
  premises : List Triple
  conclusion : Triple
deriving Repr

/-- Consume the list chain for node `l` from the front of `ps`, checking each
chain triple with `inG`. Returns the members and the premises left over. -/
def takeChain (inG : Triple → Bool) : Term → List Triple → Option (List Term × List Triple)
  | l, ps =>
    if l = V.nil then some ([], ps)
    else
      match ps with
      | ⟨l1, f, m⟩ :: ⟨l2, r, l'⟩ :: ps' =>
        if l1 = l ∧ f = V.first ∧ l2 = l ∧ r = V.rest ∧ inG ⟨l1, f, m⟩ ∧ inG ⟨l2, r, l'⟩ then
          match takeChain inG l' ps' with
          | some (ms, q) => some (m :: ms, q)
          | none => none
        else none
      | _ => none

/-- `ps` is exactly `x rdf:type m` for each `m` in `ms`, in order, each known. -/
def allTyped (x : Term) (k : Triple → Bool) : List Term → List Triple → Bool
  | [], [] => true
  | m :: ms, ⟨x', t, m'⟩ :: ps =>
      x' = x ∧ t = V.type ∧ m' = m ∧ k ⟨x', t, m'⟩ ∧ allTyped x k ms ps
  | _, _ => false

/-- Check one step. `inG` answers "asserted"; `derived` answers "concluded by
an earlier step". A premise may be either, except the list constructor and its
chain, which must be asserted. -/
def checkStep (inG derived : Triple → Bool) (st : Step) : Bool :=
  let k : Triple → Bool := fun t => inG t || derived t
  match st.rule, st.premises with
  | .rdfs2, [⟨s, p, o⟩, ⟨p', d, c⟩] =>
      p' = p ∧ d = V.domain ∧ k ⟨s, p, o⟩ ∧ k ⟨p', d, c⟩ ∧
      st.conclusion = ⟨s, V.type, c⟩
  | .rdfs3, [⟨s, p, o⟩, ⟨p', r, c⟩] =>
      p' = p ∧ r = V.range ∧ k ⟨s, p, o⟩ ∧ k ⟨p', r, c⟩ ∧
      st.conclusion = ⟨o, V.type, c⟩
  | .rdfs5, [⟨a, sp1, b⟩, ⟨b', sp2, c⟩] =>
      sp1 = V.subPropertyOf ∧ sp2 = V.subPropertyOf ∧ b' = b ∧
      k ⟨a, sp1, b⟩ ∧ k ⟨b', sp2, c⟩ ∧ st.conclusion = ⟨a, V.subPropertyOf, c⟩
  | .rdfs7, [⟨s, p, o⟩, ⟨p', sp, q⟩] =>
      p' = p ∧ sp = V.subPropertyOf ∧ k ⟨s, p, o⟩ ∧ k ⟨p', sp, q⟩ ∧
      st.conclusion = ⟨s, q, o⟩
  | .rdfs9, [⟨x, t, a⟩, ⟨a', sc, b⟩] =>
      t = V.type ∧ a' = a ∧ sc = V.subClassOf ∧ k ⟨x, t, a⟩ ∧ k ⟨a', sc, b⟩ ∧
      st.conclusion = ⟨x, V.type, b⟩
  | .rdfs11, [⟨a, sc1, b⟩, ⟨b', sc2, c⟩] =>
      sc1 = V.subClassOf ∧ sc2 = V.subClassOf ∧ b' = b ∧
      k ⟨a, sc1, b⟩ ∧ k ⟨b', sc2, c⟩ ∧ st.conclusion = ⟨a, V.subClassOf, c⟩
  | .prpTrp, [⟨p, t, tp⟩, ⟨x, p1, y⟩, ⟨y', p2, z⟩] =>
      t = V.type ∧ tp = V.transitiveProperty ∧ p1 = p ∧ p2 = p ∧ y' = y ∧
      k ⟨p, t, tp⟩ ∧ k ⟨x, p1, y⟩ ∧ k ⟨y', p2, z⟩ ∧ st.conclusion = ⟨x, p, z⟩
  | .prpSymp, [⟨p, t, sy⟩, ⟨x, p1, y⟩] =>
      t = V.type ∧ sy = V.symmetricProperty ∧ p1 = p ∧
      k ⟨p, t, sy⟩ ∧ k ⟨x, p1, y⟩ ∧ st.conclusion = ⟨y, p, x⟩
  | .prpInv1, [⟨p, io, q⟩, ⟨x, p1, y⟩] =>
      io = V.inverseOf ∧ p1 = p ∧ k ⟨p, io, q⟩ ∧ k ⟨x, p1, y⟩ ∧
      st.conclusion = ⟨y, q, x⟩
  | .prpInv2, [⟨p, io, q⟩, ⟨x, q1, y⟩] =>
      io = V.inverseOf ∧ q1 = q ∧ k ⟨p, io, q⟩ ∧ k ⟨x, q1, y⟩ ∧
      st.conclusion = ⟨y, p, x⟩
  | .eqSym, [⟨a, sa, b⟩] =>
      sa = V.sameAs ∧ k ⟨a, sa, b⟩ ∧ st.conclusion = ⟨b, V.sameAs, a⟩
  | .scmEqc1, [⟨a, e, b⟩] =>
      e = V.equivalentClass ∧ k ⟨a, e, b⟩ ∧
      (st.conclusion = ⟨a, V.subClassOf, b⟩ ∨ st.conclusion = ⟨b, V.subClassOf, a⟩)
  | .scmEqp1, [⟨a, e, b⟩] =>
      e = V.equivalentProperty ∧ k ⟨a, e, b⟩ ∧
      (st.conclusion = ⟨a, V.subPropertyOf, b⟩ ∨ st.conclusion = ⟨b, V.subPropertyOf, a⟩)
  | .clsSvf1, [⟨r, op, p⟩, ⟨r', sv, c⟩, ⟨x, p1, y⟩, ⟨y', t, c'⟩] =>
      op = V.onProperty ∧ sv = V.someValuesFrom ∧ r' = r ∧ p1 = p ∧ y' = y ∧
      t = V.type ∧ c' = c ∧
      k ⟨r, op, p⟩ ∧ k ⟨r', sv, c⟩ ∧ k ⟨x, p1, y⟩ ∧ k ⟨y', t, c'⟩ ∧
      st.conclusion = ⟨x, V.type, r⟩
  | .clsAvf, [⟨r, op, p⟩, ⟨r', av, c⟩, ⟨x, t, r''⟩, ⟨x', p1, y⟩] =>
      op = V.onProperty ∧ av = V.allValuesFrom ∧ r' = r ∧ t = V.type ∧ r'' = r ∧
      x' = x ∧ p1 = p ∧
      k ⟨r, op, p⟩ ∧ k ⟨r', av, c⟩ ∧ k ⟨x, t, r''⟩ ∧ k ⟨x', p1, y⟩ ∧
      st.conclusion = ⟨y, V.type, c⟩
  | .clsHv1, [⟨r, op, p⟩, ⟨r', hv, v⟩, ⟨x, t, r''⟩] =>
      op = V.onProperty ∧ hv = V.hasValue ∧ r' = r ∧ t = V.type ∧ r'' = r ∧
      k ⟨r, op, p⟩ ∧ k ⟨r', hv, v⟩ ∧ k ⟨x, t, r''⟩ ∧
      st.conclusion = ⟨x, p, v⟩
  | .clsHv2, [⟨r, op, p⟩, ⟨r', hv, v⟩, ⟨x, p1, v'⟩] =>
      op = V.onProperty ∧ hv = V.hasValue ∧ r' = r ∧ p1 = p ∧ v' = v ∧
      k ⟨r, op, p⟩ ∧ k ⟨r', hv, v⟩ ∧ k ⟨x, p1, v'⟩ ∧
      st.conclusion = ⟨x, V.type, r⟩
  | .clsInt1, ⟨c, io, l⟩ :: ps =>
      decide (io = V.intersectionOf) && inG ⟨c, io, l⟩ &&
      (match takeChain inG l ps with
       | some (ms, q) =>
           allTyped st.conclusion.s k ms q &&
           decide (st.conclusion.p = V.type ∧ st.conclusion.o = c)
       | none => false)
  | .clsInt2, ⟨c, io, l⟩ :: ps =>
      decide (io = V.intersectionOf) && inG ⟨c, io, l⟩ &&
      (match takeChain inG l ps with
       | some (ms, [⟨x, t, c'⟩]) =>
           decide (t = V.type ∧ c' = c ∧ k ⟨x, t, c'⟩ ∧
             st.conclusion.s = x ∧ st.conclusion.p = V.type ∧ st.conclusion.o ∈ ms)
       | _ => false)
  | .clsUni, ⟨c, uo, l⟩ :: ps =>
      decide (uo = V.unionOf) && inG ⟨c, uo, l⟩ &&
      (match takeChain inG l ps with
       | some (ms, [⟨x, t, m⟩]) =>
           decide (t = V.type ∧ m ∈ ms ∧ k ⟨x, t, m⟩ ∧ st.conclusion = ⟨x, V.type, c⟩)
       | _ => false)
  | .clsOo, ⟨c, oo, l⟩ :: ps =>
      decide (oo = V.oneOf) && inG ⟨c, oo, l⟩ &&
      (match takeChain inG l ps with
       | some (ms, []) =>
           decide (st.conclusion.s ∈ ms ∧ st.conclusion.p = V.type ∧ st.conclusion.o = c)
       | _ => false)
  | .scmSvf1, [⟨c1, sv1, y1⟩, ⟨c1a, op1, p⟩, ⟨c2, sv2, y2⟩, ⟨c2a, op2, pa⟩, ⟨y1a, sc, y2a⟩] =>
      sv1 = V.someValuesFrom ∧ op1 = V.onProperty ∧ c1a = c1 ∧
      sv2 = V.someValuesFrom ∧ op2 = V.onProperty ∧ c2a = c2 ∧ pa = p ∧
      sc = V.subClassOf ∧ y1a = y1 ∧ y2a = y2 ∧
      k ⟨c1, sv1, y1⟩ ∧ k ⟨c1a, op1, p⟩ ∧ k ⟨c2, sv2, y2⟩ ∧ k ⟨c2a, op2, pa⟩ ∧
      k ⟨y1a, sc, y2a⟩ ∧
      st.conclusion = ⟨c1, V.subClassOf, c2⟩
  | .scmSvf2, [⟨c1, sv1, y⟩, ⟨c1a, op1, p1⟩, ⟨c2, sv2, ya⟩, ⟨c2a, op2, p2⟩, ⟨p1a, sp, p2a⟩] =>
      sv1 = V.someValuesFrom ∧ op1 = V.onProperty ∧ c1a = c1 ∧
      sv2 = V.someValuesFrom ∧ op2 = V.onProperty ∧ c2a = c2 ∧ ya = y ∧
      sp = V.subPropertyOf ∧ p1a = p1 ∧ p2a = p2 ∧
      k ⟨c1, sv1, y⟩ ∧ k ⟨c1a, op1, p1⟩ ∧ k ⟨c2, sv2, ya⟩ ∧ k ⟨c2a, op2, p2⟩ ∧
      k ⟨p1a, sp, p2a⟩ ∧
      st.conclusion = ⟨c1, V.subClassOf, c2⟩
  | .scmAvf1, [⟨c1, av1, y1⟩, ⟨c1a, op1, p⟩, ⟨c2, av2, y2⟩, ⟨c2a, op2, pa⟩, ⟨y1a, sc, y2a⟩] =>
      av1 = V.allValuesFrom ∧ op1 = V.onProperty ∧ c1a = c1 ∧
      av2 = V.allValuesFrom ∧ op2 = V.onProperty ∧ c2a = c2 ∧ pa = p ∧
      sc = V.subClassOf ∧ y1a = y1 ∧ y2a = y2 ∧
      k ⟨c1, av1, y1⟩ ∧ k ⟨c1a, op1, p⟩ ∧ k ⟨c2, av2, y2⟩ ∧ k ⟨c2a, op2, pa⟩ ∧
      k ⟨y1a, sc, y2a⟩ ∧
      st.conclusion = ⟨c1, V.subClassOf, c2⟩
  -- scm-avf2 concludes `c2 subClassOf c1`. The other three restriction-ordering
  -- arms conclude `c1 subClassOf c2`, and writing this one the same way would
  -- make the checker accept a step no model supports.
  | .scmAvf2, [⟨c1, av1, y⟩, ⟨c1a, op1, p1⟩, ⟨c2, av2, ya⟩, ⟨c2a, op2, p2⟩, ⟨p1a, sp, p2a⟩] =>
      av1 = V.allValuesFrom ∧ op1 = V.onProperty ∧ c1a = c1 ∧
      av2 = V.allValuesFrom ∧ op2 = V.onProperty ∧ c2a = c2 ∧ ya = y ∧
      sp = V.subPropertyOf ∧ p1a = p1 ∧ p2a = p2 ∧
      k ⟨c1, av1, y⟩ ∧ k ⟨c1a, op1, p1⟩ ∧ k ⟨c2, av2, ya⟩ ∧ k ⟨c2a, op2, p2⟩ ∧
      k ⟨p1a, sp, p2a⟩ ∧
      st.conclusion = ⟨c2, V.subClassOf, c1⟩
  | .scmDom1, [⟨p, d, c1⟩, ⟨c1a, sc, c2⟩] =>
      d = V.domain ∧ sc = V.subClassOf ∧ c1a = c1 ∧
      k ⟨p, d, c1⟩ ∧ k ⟨c1a, sc, c2⟩ ∧ st.conclusion = ⟨p, V.domain, c2⟩
  | .scmDom2, [⟨p2, d, c⟩, ⟨p1, sp, p2a⟩] =>
      d = V.domain ∧ sp = V.subPropertyOf ∧ p2a = p2 ∧
      k ⟨p2, d, c⟩ ∧ k ⟨p1, sp, p2a⟩ ∧ st.conclusion = ⟨p1, V.domain, c⟩
  | .scmRng1, [⟨p, r, c1⟩, ⟨c1a, sc, c2⟩] =>
      r = V.range ∧ sc = V.subClassOf ∧ c1a = c1 ∧
      k ⟨p, r, c1⟩ ∧ k ⟨c1a, sc, c2⟩ ∧ st.conclusion = ⟨p, V.range, c2⟩
  | .scmRng2, [⟨p2, r, c⟩, ⟨p1, sp, p2a⟩] =>
      r = V.range ∧ sp = V.subPropertyOf ∧ p2a = p2 ∧
      k ⟨p2, r, c⟩ ∧ k ⟨p1, sp, p2a⟩ ∧ st.conclusion = ⟨p1, V.range, c⟩
  | _, _ => false

/-- Check every step in order, each seeing the conclusions of the ones before. -/
def checkAll (inG : Triple → Bool) : List Step → Std.HashSet Triple → Bool
  | [], _ => true
  | st :: rest, derived =>
      checkStep inG (fun t => derived.contains t) st &&
      checkAll inG rest (derived.insert st.conclusion)

/-- The checker. `G` is the asserted graph, `steps` the certificate. -/
def checkCert (G : List Triple) (steps : List Step) : Bool :=
  let gset := Std.HashSet.ofList G
  checkAll (fun t => gset.contains t) steps ∅

end OOCert
