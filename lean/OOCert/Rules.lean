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
| cls-uni    | `c owl:unionOf l`, the list chain of `l`, `x rdf:type m` for one member `m` | `x rdf:type c` |

The list chain is the sequence `l rdf:first m₁`, `l rdf:rest l₂`,
`l₂ rdf:first m₂`, `l₂ rdf:rest l₃`, … down to a node whose `rdf:rest` is
`rdf:nil`. The chain and the constructor triple must be asserted, not derived,
because `Model` reads lists off the asserted graph.

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
  | clsSvf1 | clsAvf | clsHv1 | clsHv2 | clsInt1 | clsUni
deriving DecidableEq, Repr

def Rule.name : Rule → String
  | .rdfs2 => "rdfs2" | .rdfs3 => "rdfs3" | .rdfs5 => "rdfs5" | .rdfs7 => "rdfs7"
  | .rdfs9 => "rdfs9" | .rdfs11 => "rdfs11"
  | .prpTrp => "prp-trp" | .prpSymp => "prp-symp" | .prpInv1 => "prp-inv1"
  | .prpInv2 => "prp-inv2" | .eqSym => "eq-sym"
  | .scmEqc1 => "scm-eqc1" | .scmEqp1 => "scm-eqp1"
  | .clsSvf1 => "cls-svf1" | .clsAvf => "cls-avf"
  | .clsHv1 => "cls-hv1" | .clsHv2 => "cls-hv2"
  | .clsInt1 => "cls-int1" | .clsUni => "cls-uni"

def Rule.all : List Rule :=
  [.rdfs2, .rdfs3, .rdfs5, .rdfs7, .rdfs9, .rdfs11,
   .prpTrp, .prpSymp, .prpInv1, .prpInv2, .eqSym,
   .scmEqc1, .scmEqp1,
   .clsSvf1, .clsAvf, .clsHv1, .clsHv2, .clsInt1, .clsUni]

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
  | .clsUni, ⟨c, uo, l⟩ :: ps =>
      decide (uo = V.unionOf) && inG ⟨c, uo, l⟩ &&
      (match takeChain inG l ps with
       | some (ms, [⟨x, t, m⟩]) =>
           decide (t = V.type ∧ m ∈ ms ∧ k ⟨x, t, m⟩ ∧ st.conclusion = ⟨x, V.type, c⟩)
       | _ => false)
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
