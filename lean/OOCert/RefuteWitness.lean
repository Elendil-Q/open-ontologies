import OOCert.Refute
import OOCert.W3C

/-!
# Witnesses for the refutation layer

`refutation_sound` says an accepted refutation means `Unsat G`. That claim is
worth nothing on its own, and it can be hollow in a way the derivation checker's
soundness theorem cannot be.

`Unsat G` means "no interpretation satisfies both `Model I G` and
`RefuteConditions I`". If NOTHING ever satisfied both, `Unsat G` would hold of
every graph, the checker could accept anything, and `refutation_sound` would
still be a theorem. `lean/OOCert/Witness.lean` closes the matching hole for the
derivation checker with `saturated_is_a_model`, which exhibits a model of an
arbitrary graph. That route is closed here by construction: disjointness is a
NEGATIVE condition and the saturated interpretation, which puts everything in
every class, violates it. The witness has to be rebuilt, not reused.

| theorem | says |
|---|---|
| `closure_is_a_model` | the OWL-RL closure of ANY graph, read as a Herbrand interpretation, is a model of it |
| `Der_sound` | that closure contains only entailed triples, so it is the closure and not a junk superset |
| `no_violation_means_a_joint_model` | a graph whose closure has no disjointness violation HAS a model respecting disjointness |
| `unsat_means_a_violation` | and the converse: refutability is exactly a violation in the closure |
| `graze_is_refuted` | a concrete graph is refuted, through a derived type rather than an asserted one |
| `feed_is_not_refuted` | a concrete graph that HAS a disjointness axiom is not refutable, so the checker's rejections are not an accident |
| `the_checker_rejects_the_attempt_on_the_consistent_graph` | and the checker really does reject it |
| six `rejects_*` theorems | six ways to forge a refutation, each caught |
| `an_ordinary_certificate_is_worthless_over_the_refuted_graph` | the explosion, stated for the graph above |
| `and_the_old_verdict_does_not_notice` | and `Entails` does not notice, which is the trap |

## The one hypothesis the general theorem carries, named rather than hidden

`closure_is_a_model` needs `∀ a b, Der G ⟨a, owl:sameAs, b⟩ → a = b`. Every other
semantic condition is a closure rule and becomes a constructor of `Der`, but
`Conditions.same` is not a closure rule: it says the denotations of two terms
coincide, and in a Herbrand interpretation a term denotes itself, so two
different spellings cannot be equal. A graph whose closure asserts an identity
between distinct terms therefore needs a quotient of the term domain, which is a
larger construction and is NOT done here. The hypothesis is an explicit argument
of every theorem that needs it, and both concrete graphs discharge it by
containing no `owl:sameAs` at all.
-/
namespace OOCert

/-! ## The closure of a graph, as an inductive predicate

One constructor per condition of `Model`, `Conditions.same` excepted. Read it as
the definition of "the semantics forces this triple": `Der_sound` proves it
derives nothing that is not entailed, and `closure_is_a_model` proves it derives
everything a model must contain.

The pair matters. Without `Der_sound` the predicate could be everything, which
would make `no_violation_means_a_joint_model` vacuous because no graph would
satisfy its hypothesis. Without `closure_is_a_model` it could be nothing, and the
theorem would be about an interpretation that is not a model. -/
inductive Der (G : List Triple) : Triple → Prop
  | base {t : Triple} : t ∈ G → Der G t
  | sc_sub {a b x : Term} :
      Der G ⟨a, V.subClassOf, b⟩ → Der G ⟨x, V.type, a⟩ → Der G ⟨x, V.type, b⟩
  | sc_trans {a b c : Term} :
      Der G ⟨a, V.subClassOf, b⟩ → Der G ⟨b, V.subClassOf, c⟩ → Der G ⟨a, V.subClassOf, c⟩
  | sp_sub {a b x y : Term} :
      Der G ⟨a, V.subPropertyOf, b⟩ → Der G ⟨x, a, y⟩ → Der G ⟨x, b, y⟩
  | sp_trans {a b c : Term} :
      Der G ⟨a, V.subPropertyOf, b⟩ → Der G ⟨b, V.subPropertyOf, c⟩ →
      Der G ⟨a, V.subPropertyOf, c⟩
  | dom {p c x y : Term} : Der G ⟨p, V.domain, c⟩ → Der G ⟨x, p, y⟩ → Der G ⟨x, V.type, c⟩
  | rng {p c x y : Term} : Der G ⟨p, V.range, c⟩ → Der G ⟨x, p, y⟩ → Der G ⟨y, V.type, c⟩
  | trp {p x y z : Term} :
      Der G ⟨p, V.type, V.transitiveProperty⟩ → Der G ⟨x, p, y⟩ → Der G ⟨y, p, z⟩ →
      Der G ⟨x, p, z⟩
  | symp {p x y : Term} :
      Der G ⟨p, V.type, V.symmetricProperty⟩ → Der G ⟨x, p, y⟩ → Der G ⟨y, p, x⟩
  | inv1 {p q x y : Term} : Der G ⟨p, V.inverseOf, q⟩ → Der G ⟨x, p, y⟩ → Der G ⟨y, q, x⟩
  | inv2 {p q x y : Term} : Der G ⟨p, V.inverseOf, q⟩ → Der G ⟨y, q, x⟩ → Der G ⟨x, p, y⟩
  | eqc1 {a b : Term} : Der G ⟨a, V.equivalentClass, b⟩ → Der G ⟨a, V.subClassOf, b⟩
  | eqc2 {a b : Term} : Der G ⟨a, V.equivalentClass, b⟩ → Der G ⟨b, V.subClassOf, a⟩
  | eqp1 {a b : Term} : Der G ⟨a, V.equivalentProperty, b⟩ → Der G ⟨a, V.subPropertyOf, b⟩
  | eqp2 {a b : Term} : Der G ⟨a, V.equivalentProperty, b⟩ → Der G ⟨b, V.subPropertyOf, a⟩
  | svf {r p c x y : Term} :
      Der G ⟨r, V.onProperty, p⟩ → Der G ⟨r, V.someValuesFrom, c⟩ → Der G ⟨x, p, y⟩ →
      Der G ⟨y, V.type, c⟩ → Der G ⟨x, V.type, r⟩
  | avf {r p c x y : Term} :
      Der G ⟨r, V.onProperty, p⟩ → Der G ⟨r, V.allValuesFrom, c⟩ → Der G ⟨x, V.type, r⟩ →
      Der G ⟨x, p, y⟩ → Der G ⟨y, V.type, c⟩
  | hv1 {r p v x : Term} :
      Der G ⟨r, V.onProperty, p⟩ → Der G ⟨r, V.hasValue, v⟩ → Der G ⟨x, V.type, r⟩ →
      Der G ⟨x, p, v⟩
  | hv2 {r p v x : Term} :
      Der G ⟨r, V.onProperty, p⟩ → Der G ⟨r, V.hasValue, v⟩ → Der G ⟨x, p, v⟩ →
      Der G ⟨x, V.type, r⟩
  | svf_sc {c1 c2 p y1 y2 : Term} :
      Der G ⟨c1, V.someValuesFrom, y1⟩ → Der G ⟨c1, V.onProperty, p⟩ →
      Der G ⟨c2, V.someValuesFrom, y2⟩ → Der G ⟨c2, V.onProperty, p⟩ →
      Der G ⟨y1, V.subClassOf, y2⟩ → Der G ⟨c1, V.subClassOf, c2⟩
  | svf_sp {c1 c2 p1 p2 y : Term} :
      Der G ⟨c1, V.someValuesFrom, y⟩ → Der G ⟨c1, V.onProperty, p1⟩ →
      Der G ⟨c2, V.someValuesFrom, y⟩ → Der G ⟨c2, V.onProperty, p2⟩ →
      Der G ⟨p1, V.subPropertyOf, p2⟩ → Der G ⟨c1, V.subClassOf, c2⟩
  | avf_sc {c1 c2 p y1 y2 : Term} :
      Der G ⟨c1, V.allValuesFrom, y1⟩ → Der G ⟨c1, V.onProperty, p⟩ →
      Der G ⟨c2, V.allValuesFrom, y2⟩ → Der G ⟨c2, V.onProperty, p⟩ →
      Der G ⟨y1, V.subClassOf, y2⟩ → Der G ⟨c1, V.subClassOf, c2⟩
  /-- The reversed one. `scm-avf2` concludes `c2 rdfs:subClassOf c1`. -/
  | avf_sp {c1 c2 p1 p2 y : Term} :
      Der G ⟨c1, V.allValuesFrom, y⟩ → Der G ⟨c1, V.onProperty, p1⟩ →
      Der G ⟨c2, V.allValuesFrom, y⟩ → Der G ⟨c2, V.onProperty, p2⟩ →
      Der G ⟨p1, V.subPropertyOf, p2⟩ → Der G ⟨c2, V.subClassOf, c1⟩
  | dom_sc {p c1 c2 : Term} :
      Der G ⟨p, V.domain, c1⟩ → Der G ⟨c1, V.subClassOf, c2⟩ → Der G ⟨p, V.domain, c2⟩
  | dom_sp {p1 p2 c : Term} :
      Der G ⟨p2, V.domain, c⟩ → Der G ⟨p1, V.subPropertyOf, p2⟩ → Der G ⟨p1, V.domain, c⟩
  | rng_sc {p c1 c2 : Term} :
      Der G ⟨p, V.range, c1⟩ → Der G ⟨c1, V.subClassOf, c2⟩ → Der G ⟨p, V.range, c2⟩
  | rng_sp {p1 p2 c : Term} :
      Der G ⟨p2, V.range, c⟩ → Der G ⟨p1, V.subPropertyOf, p2⟩ → Der G ⟨p1, V.range, c⟩
  | int {c l x : Term} {ms : List Term} :
      (⟨c, V.intersectionOf, l⟩ : Triple) ∈ G → Chain G l ms →
      (∀ m ∈ ms, Der G ⟨x, V.type, m⟩) → Der G ⟨x, V.type, c⟩
  | int2 {c l x m : Term} {ms : List Term} :
      (⟨c, V.intersectionOf, l⟩ : Triple) ∈ G → Chain G l ms →
      Der G ⟨x, V.type, c⟩ → m ∈ ms → Der G ⟨x, V.type, m⟩
  | uni {c l x m : Term} {ms : List Term} :
      (⟨c, V.unionOf, l⟩ : Triple) ∈ G → Chain G l ms →
      m ∈ ms → Der G ⟨x, V.type, m⟩ → Der G ⟨x, V.type, c⟩
  | oneOf {c l m : Term} {ms : List Term} :
      (⟨c, V.oneOf, l⟩ : Triple) ∈ G → Chain G l ms → m ∈ ms → Der G ⟨m, V.type, c⟩

/-- **The closure derives only what the semantics forces.** Every case is a
one-line appeal to the matching field of `Model`, which is what it means for the
constructors to mirror the conditions rather than to invent rules. -/
theorem Der_sound {G : List Triple} {I : Interp} (M : Model I G) :
    ∀ {t : Triple}, Der G t → I.sat t := by
  intro t h
  induction h with
  | @base _ hm => exact M.facts _ hm
  | @sc_sub a b x _ _ ih1 ih2 => exact M.conds.sc_sub _ _ ih1 _ ih2
  | @sc_trans a b c _ _ ih1 ih2 => exact M.conds.sc_trans _ _ _ ih1 ih2
  | @sp_sub a b x y _ _ ih1 ih2 => exact M.conds.sp_sub _ _ ih1 _ _ ih2
  | @sp_trans a b c _ _ ih1 ih2 => exact M.conds.sp_trans _ _ _ ih1 ih2
  | @dom p c x y _ _ ih1 ih2 => exact M.conds.dom _ _ ih1 _ _ ih2
  | @rng p c x y _ _ ih1 ih2 => exact M.conds.rng _ _ ih1 _ _ ih2
  | @trp p x y z _ _ _ ih1 ih2 ih3 => exact M.conds.trp _ ih1 _ _ _ ih2 ih3
  | @symp p x y _ _ ih1 ih2 => exact M.conds.symp _ ih1 _ _ ih2
  | @inv1 p q x y _ _ ih1 ih2 => exact (M.conds.inv _ _ ih1 _ _).mp ih2
  | @inv2 p q x y _ _ ih1 ih2 => exact (M.conds.inv _ _ ih1 _ _).mpr ih2
  | @eqc1 a b _ ih => exact (M.conds.eqc _ _ ih).1
  | @eqc2 a b _ ih => exact (M.conds.eqc _ _ ih).2
  | @eqp1 a b _ ih => exact (M.conds.eqp _ _ ih).1
  | @eqp2 a b _ ih => exact (M.conds.eqp _ _ ih).2
  | @svf r p c x y _ _ _ _ ih1 ih2 ih3 ih4 => exact M.conds.svf _ _ _ ih1 ih2 _ _ ih3 ih4
  | @avf r p c x y _ _ _ _ ih1 ih2 ih3 ih4 => exact M.conds.avf _ _ _ ih1 ih2 _ _ ih3 ih4
  | @hv1 r p v x _ _ _ ih1 ih2 ih3 => exact (M.conds.hv _ _ _ ih1 ih2 _).mp ih3
  | @hv2 r p v x _ _ _ ih1 ih2 ih3 => exact (M.conds.hv _ _ _ ih1 ih2 _).mpr ih3
  | @svf_sc c1 c2 p y1 y2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      exact M.conds.svf_sc _ _ _ _ _ ih1 ih2 ih3 ih4 ih5
  | @svf_sp c1 c2 p1 p2 y _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      exact M.conds.svf_sp _ _ _ _ _ ih1 ih2 ih3 ih4 ih5
  | @avf_sc c1 c2 p y1 y2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      exact M.conds.avf_sc _ _ _ _ _ ih1 ih2 ih3 ih4 ih5
  | @avf_sp c1 c2 p1 p2 y _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
      exact M.conds.avf_sp _ _ _ _ _ ih1 ih2 ih3 ih4 ih5
  | @dom_sc p c1 c2 _ _ ih1 ih2 => exact M.conds.dom_sc _ _ _ ih1 ih2
  | @dom_sp p1 p2 c _ _ ih1 ih2 => exact M.conds.dom_sp _ _ _ ih1 ih2
  | @rng_sc p c1 c2 _ _ ih1 ih2 => exact M.conds.rng_sc _ _ _ ih1 ih2
  | @rng_sp p1 p2 c _ _ ih1 ih2 => exact M.conds.rng_sp _ _ _ ih1 ih2
  | @int c l x ms hin hch _ ih => exact M.int _ _ _ hin hch _ ih
  | @int2 c l x m ms hin hch _ hm ih => exact M.int2 _ _ _ hin hch _ ih _ hm
  | @uni c l x m ms hin hch hm _ ih => exact M.uni _ _ _ hin hch _ _ hm ih
  | @oneOf c l m ms hin hch hm => exact M.oneOf _ _ _ hin hch _ hm

/-- The closure is contained in every model, in particular in every finite
Herbrand model, which is how the concrete graphs below settle negatives. -/
theorem Der_entails {G : List Triple} {t : Triple} (h : Der G t) : Entails G t :=
  fun _ M => Der_sound M h

/-- **The closure of any graph is a model of it.** Each field is the matching
constructor, because that is how the constructors were chosen. The one
hypothesis is `Conditions.same`, which is not a closure rule: see the module
docstring. -/
theorem closure_is_a_model (G : List Triple)
    (hsame : ∀ a b : Term, Der G ⟨a, V.sameAs, b⟩ → a = b) :
    Model (herbrandP (Der G)) G where
  conds :=
    { sc_sub := fun _ _ h _ hx => Der.sc_sub h hx
      sc_trans := fun _ _ _ h1 h2 => Der.sc_trans h1 h2
      sp_sub := fun _ _ h _ _ hxy => Der.sp_sub h hxy
      sp_trans := fun _ _ _ h1 h2 => Der.sp_trans h1 h2
      dom := fun _ _ h _ _ hxy => Der.dom h hxy
      rng := fun _ _ h _ _ hxy => Der.rng h hxy
      trp := fun _ h _ _ _ h1 h2 => Der.trp h h1 h2
      symp := fun _ h _ _ h1 => Der.symp h h1
      inv := fun _ _ h _ _ => ⟨fun h1 => Der.inv1 h h1, fun h1 => Der.inv2 h h1⟩
      same := hsame
      eqc := fun _ _ h => ⟨Der.eqc1 h, Der.eqc2 h⟩
      eqp := fun _ _ h => ⟨Der.eqp1 h, Der.eqp2 h⟩
      svf := fun _ _ _ h1 h2 _ _ h3 h4 => Der.svf h1 h2 h3 h4
      avf := fun _ _ _ h1 h2 _ _ h3 h4 => Der.avf h1 h2 h3 h4
      hv := fun _ _ _ h1 h2 _ => ⟨fun h3 => Der.hv1 h1 h2 h3, fun h3 => Der.hv2 h1 h2 h3⟩
      svf_sc := fun _ _ _ _ _ h1 h2 h3 h4 h5 => Der.svf_sc h1 h2 h3 h4 h5
      svf_sp := fun _ _ _ _ _ h1 h2 h3 h4 h5 => Der.svf_sp h1 h2 h3 h4 h5
      avf_sc := fun _ _ _ _ _ h1 h2 h3 h4 h5 => Der.avf_sc h1 h2 h3 h4 h5
      avf_sp := fun _ _ _ _ _ h1 h2 h3 h4 h5 => Der.avf_sp h1 h2 h3 h4 h5
      dom_sc := fun _ _ _ h1 h2 => Der.dom_sc h1 h2
      dom_sp := fun _ _ _ h1 h2 => Der.dom_sp h1 h2
      rng_sc := fun _ _ _ h1 h2 => Der.rng_sc h1 h2
      rng_sp := fun _ _ _ h1 h2 => Der.rng_sp h1 h2 }
  facts := fun _ ht => Der.base ht
  int := fun _ _ _ hin hch _ hall => Der.int hin hch hall
  int2 := fun _ _ _ hin hch _ hx _ hm => Der.int2 hin hch hx hm
  uni := fun _ _ _ hin hch _ _ hm hx => Der.uni hin hch hm hx
  oneOf := fun _ _ _ hin hch _ hm => Der.oneOf hin hch hm

/-- **The replacement for `saturated_is_a_model`.** A graph whose closure has no
disjointness violation has a model that satisfies `Model` AND `RefuteConditions`,
so `refutation_sound` is not a theorem about an empty model class.

Conditional on the `owl:sameAs` hypothesis, which is stated and not buried. -/
theorem no_violation_means_a_joint_model (G : List Triple)
    (hsame : ∀ a b : Term, Der G ⟨a, V.sameAs, b⟩ → a = b)
    (hdw : ∀ c1 c2 x : Term, Der G ⟨c1, RV.disjointWith, c2⟩ → Der G ⟨x, V.type, c1⟩ →
      Der G ⟨x, V.type, c2⟩ → False) :
    ∃ I : Interp, Model I G ∧ RefuteConditions I :=
  joint_model_of_closure (closure_is_a_model G hsame) hdw

/-- The converse, and the more useful direction in practice: if a graph IS
refutable then its closure contains a disjointness violation. So `cax-dw` is not
merely sound for this fragment, it is the only way to be unsatisfiable in it, and
a consumer who finds no violation has a positive result rather than a failure to
find one. Same `owl:sameAs` hypothesis.

Read "unsatisfiable" here as `Unsat`, which is the whole content of the
statement and is narrower than a consumer's word for it. `Unsat` quantifies over
`RefuteConditions`, and `RefuteConditions` reads `owl:disjointWith` and nothing
else, so this theorem says `cax-dw` is the only clash IN THAT MODEL CLASS. It
does not say a graph with no disjointness violation is consistent under OWL 2
RL: sixteen further rules of the profile conclude `false` and none of them has a
condition here, so a graph refutable only by `prp-irp` or `cls-nothing2` passes
this test and is contradictory anyway. The positive result is "no clash of the
one kind this layer can see", and it is worth having for exactly that. -/
theorem unsat_means_a_violation (G : List Triple)
    (hsame : ∀ a b : Term, Der G ⟨a, V.sameAs, b⟩ → a = b) (h : Unsat G) :
    ∃ c1 c2 x : Term, Der G ⟨c1, RV.disjointWith, c2⟩ ∧ Der G ⟨x, V.type, c1⟩ ∧
      Der G ⟨x, V.type, c2⟩ :=
  Classical.byContradiction fun hno =>
    not_unsat_of_joint_model
      (no_violation_means_a_joint_model G hsame
        (fun c1 c2 x h1 h2 h3 => hno ⟨c1, c2, x, h1, h2, h3⟩)) h

/-! ## A fragment in which a plain Herbrand model is easy to exhibit

Both concrete graphs below use only `rdf:type`, `rdfs:subClassOf` and
`owl:disjointWith`. In that fragment every semantic condition except `sc_sub`
and `sc_trans` has a premise no triple can supply, so a list closed under those
two is a model of everything it contains. `Plain` packages the four side
conditions in a form `decide` can settle over a concrete list. -/

/-- The side conditions, all decidable over a concrete list. `scClosed` and
`scTrans` are written over pairs of triples of `H` rather than over arbitrary
terms for exactly that reason. -/
structure Plain (H : List Triple) : Prop where
  vocab : ∀ t ∈ H, t.p = V.type ∨ t.p = V.subClassOf ∨ t.p = RV.disjointWith
  noMeta : ∀ t ∈ H, ¬(t.p = V.type ∧ (t.o = V.transitiveProperty ∨ t.o = V.symmetricProperty))
  scClosed : ∀ t ∈ H, ∀ u ∈ H, t.p = V.subClassOf → u.p = V.type → u.o = t.s →
    (⟨u.s, V.type, t.o⟩ : Triple) ∈ H
  scTrans : ∀ t ∈ H, ∀ u ∈ H, t.p = V.subClassOf → u.p = V.subClassOf → u.s = t.o →
    (⟨t.s, V.subClassOf, u.o⟩ : Triple) ∈ H

namespace Plain

/-- A predicate outside the fragment has an empty extension in `H`. -/
theorem absent {H : List Triple} (hP : Plain H) (p : Term) (h1 : p ≠ V.type)
    (h2 : p ≠ V.subClassOf) (h3 : p ≠ RV.disjointWith) (s o : Term) :
    (⟨s, p, o⟩ : Triple) ∉ H := by
  intro hm
  rcases hP.vocab _ hm with h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h

theorem notTrans {H : List Triple} (hP : Plain H) (p : Term) :
    (⟨p, V.type, V.transitiveProperty⟩ : Triple) ∉ H :=
  fun hm => hP.noMeta _ hm ⟨rfl, Or.inl rfl⟩

theorem notSymm {H : List Triple} (hP : Plain H) (p : Term) :
    (⟨p, V.type, V.symmetricProperty⟩ : Triple) ∉ H :=
  fun hm => hP.noMeta _ hm ⟨rfl, Or.inr rfl⟩

/-- The Herbrand interpretation of a `Plain` list models every graph contained
in it. -/
theorem model {H G : List Triple} (hP : Plain H) (hGH : ∀ t ∈ G, t ∈ H) :
    Model (herbrandL H) G where
  conds :=
    { sc_sub := fun a b hab x hx => hP.scClosed ⟨a, V.subClassOf, b⟩ hab ⟨x, V.type, a⟩ hx rfl rfl rfl
      sc_trans := fun a b c hab hbc =>
        hP.scTrans ⟨a, V.subClassOf, b⟩ hab ⟨b, V.subClassOf, c⟩ hbc rfl rfl rfl
      sp_sub := fun a b hab =>
        absurd hab (hP.absent V.subPropertyOf (by decide) (by decide) (by decide) a b)
      sp_trans := fun a b _ hab =>
        absurd hab (hP.absent V.subPropertyOf (by decide) (by decide) (by decide) a b)
      dom := fun p c h => absurd h (hP.absent V.domain (by decide) (by decide) (by decide) p c)
      rng := fun p c h => absurd h (hP.absent V.range (by decide) (by decide) (by decide) p c)
      trp := fun p h => absurd h (hP.notTrans p)
      symp := fun p h => absurd h (hP.notSymm p)
      inv := fun p q h => absurd h (hP.absent V.inverseOf (by decide) (by decide) (by decide) p q)
      same := fun a b h => absurd h (hP.absent V.sameAs (by decide) (by decide) (by decide) a b)
      eqc := fun a b h =>
        absurd h (hP.absent V.equivalentClass (by decide) (by decide) (by decide) a b)
      eqp := fun a b h =>
        absurd h (hP.absent V.equivalentProperty (by decide) (by decide) (by decide) a b)
      svf := fun r p _ h => absurd h (hP.absent V.onProperty (by decide) (by decide) (by decide) r p)
      avf := fun r p _ h => absurd h (hP.absent V.onProperty (by decide) (by decide) (by decide) r p)
      hv := fun r p _ h => absurd h (hP.absent V.onProperty (by decide) (by decide) (by decide) r p)
      svf_sc := fun c1 _ _ y1 _ h =>
        absurd h (hP.absent V.someValuesFrom (by decide) (by decide) (by decide) c1 y1)
      svf_sp := fun c1 _ _ _ y h =>
        absurd h (hP.absent V.someValuesFrom (by decide) (by decide) (by decide) c1 y)
      avf_sc := fun c1 _ _ y1 _ h =>
        absurd h (hP.absent V.allValuesFrom (by decide) (by decide) (by decide) c1 y1)
      avf_sp := fun c1 _ _ _ y h =>
        absurd h (hP.absent V.allValuesFrom (by decide) (by decide) (by decide) c1 y)
      dom_sc := fun p c1 _ h =>
        absurd h (hP.absent V.domain (by decide) (by decide) (by decide) p c1)
      dom_sp := fun _ p2 c h =>
        absurd h (hP.absent V.domain (by decide) (by decide) (by decide) p2 c)
      rng_sc := fun p c1 _ h =>
        absurd h (hP.absent V.range (by decide) (by decide) (by decide) p c1)
      rng_sp := fun _ p2 c h =>
        absurd h (hP.absent V.range (by decide) (by decide) (by decide) p2 c) }
  facts := fun t ht => hGH t ht
  int := fun c l _ hin =>
    absurd (hGH _ hin) (hP.absent V.intersectionOf (by decide) (by decide) (by decide) c l)
  int2 := fun c l _ hin =>
    absurd (hGH _ hin) (hP.absent V.intersectionOf (by decide) (by decide) (by decide) c l)
  uni := fun c l _ hin =>
    absurd (hGH _ hin) (hP.absent V.unionOf (by decide) (by decide) (by decide) c l)
  oneOf := fun c l _ hin =>
    absurd (hGH _ hin) (hP.absent V.oneOf (by decide) (by decide) (by decide) c l)

/-- The closure of `G` is inside `H`, which is what turns a `decide` over the
list into a fact about the inductive predicate. -/
theorem der_mem {H G : List Triple} (hP : Plain H) (hGH : ∀ t ∈ G, t ∈ H) {t : Triple}
    (h : Der G t) : t ∈ H :=
  Der_sound (hP.model hGH) h

end Plain

/-! ## Two concrete graphs

`graze` is refutable and `feed` is not, and they differ by one triple. Both
carry the same `owl:disjointWith` axiom and the same subclass chain, so the
difference cannot be read off the schema. -/

def rHerbivore : Term := "<http://ex.org/Herbivore>"
def rCarnivore : Term := "<http://ex.org/Carnivore>"
def rLion : Term := "<http://ex.org/Lion>"
def rLeo : Term := "<http://ex.org/leo>"

/-- Herbivore and Carnivore are disjoint, every Lion is a Carnivore, leo is a
Lion, and leo is a Herbivore. Contradictory, and NOT syntactically: the
Carnivore membership has to be derived before the clash is visible. -/
def graze : List Triple :=
  [ ⟨rHerbivore, RV.disjointWith, rCarnivore⟩,
    ⟨rLion, V.subClassOf, rCarnivore⟩,
    ⟨rLeo, V.type, rLion⟩,
    ⟨rLeo, V.type, rHerbivore⟩ ]

/-- The same ontology with the Herbivore assertion removed. Consistent. -/
def feed : List Triple :=
  [ ⟨rHerbivore, RV.disjointWith, rCarnivore⟩,
    ⟨rLion, V.subClassOf, rCarnivore⟩,
    ⟨rLeo, V.type, rLion⟩ ]

/-! ### The refutation of `graze` -/

/-- `rdfs9` premise order is `x rdf:type a`, `a rdfs:subClassOf b`. -/
def grazeStep : Step :=
  { rule := .rdfs9
    premises := [⟨rLeo, V.type, rLion⟩, ⟨rLion, V.subClassOf, rCarnivore⟩]
    conclusion := ⟨rLeo, V.type, rCarnivore⟩ }

/-- `cax-dw` premise order is `c1 owl:disjointWith c2`, `x rdf:type c1`,
`x rdf:type c2`. The third premise is the step above, not an asserted triple. -/
def grazeFinal : RefuteStep :=
  { rule := .caxDw
    premises :=
      [ ⟨rHerbivore, RV.disjointWith, rCarnivore⟩,
        ⟨rLeo, V.type, rHerbivore⟩,
        ⟨rLeo, V.type, rCarnivore⟩ ] }

def grazeRefutation : Refutation := ⟨[grazeStep], grazeFinal⟩

/-- The checker accepts it, by kernel computation rather than by assertion. -/
theorem the_checker_accepts_the_refutation :
    checkRefutation graze grazeRefutation = true := by decide

/-- **A concrete graph is refuted**, with the clash reached through an
inference. -/
theorem graze_is_refuted : Unsat graze :=
  refutation_sound graze grazeRefutation the_checker_accepts_the_refutation

/-! ### Six forgeries, each rejected

A gate that cannot fail is decoration. Each of these is a different way to lie
and each is settled by `decide`, so the rejection is computed and not claimed. -/

/-- The disjointness axiom is invented: `Herbivore owl:disjointWith Lion` is not
in the graph. -/
def forgeUnassertedAxiom : Refutation :=
  ⟨[grazeStep],
   { rule := .caxDw
     premises :=
       [ ⟨rHerbivore, RV.disjointWith, rLion⟩,
         ⟨rLeo, V.type, rHerbivore⟩,
         ⟨rLeo, V.type, rLion⟩ ] }⟩

/-- The first premise is a `rdfs:subClassOf` triple dressed as the axiom. It IS
in the graph, and it still is not a disjointness axiom. -/
def forgeWrongPredicate : Refutation :=
  ⟨[grazeStep],
   { rule := .caxDw
     premises :=
       [ ⟨rLion, V.subClassOf, rCarnivore⟩,
         ⟨rLeo, V.type, rLion⟩,
         ⟨rLeo, V.type, rCarnivore⟩ ] }⟩

/-- The two class memberships are about different individuals, which is the
whole content of `cax-dw` and the easiest thing for a hand-written engine to get
wrong. -/
def forgeTwoIndividuals : Refutation :=
  ⟨[grazeStep],
   { rule := .caxDw
     premises :=
       [ ⟨rHerbivore, RV.disjointWith, rCarnivore⟩,
         ⟨rLeo, V.type, rHerbivore⟩,
         ⟨rLion, V.type, rCarnivore⟩ ] }⟩

/-- The derivation prefix is forged: `rdfs9` does not conclude this. -/
def forgePrefix : Refutation :=
  ⟨[{ grazeStep with conclusion := ⟨rLeo, V.type, rHerbivore⟩ }], grazeFinal⟩

/-- No prefix at all, so the third premise is neither asserted nor derived. This
is the one a careless format would let through, because the triple is true. -/
def forgeMissingPrefix : Refutation := ⟨[], grazeFinal⟩

/-- The right three triples in the wrong order. Premise order is part of the
contract. -/
def forgeWrongOrder : Refutation :=
  ⟨[grazeStep],
   { rule := .caxDw
     premises :=
       [ ⟨rLeo, V.type, rHerbivore⟩,
         ⟨rHerbivore, RV.disjointWith, rCarnivore⟩,
         ⟨rLeo, V.type, rCarnivore⟩ ] }⟩

theorem rejects_an_unasserted_axiom : checkRefutation graze forgeUnassertedAxiom = false := by
  decide
theorem rejects_a_predicate_that_is_not_disjointWith :
    checkRefutation graze forgeWrongPredicate = false := by decide
theorem rejects_two_different_individuals : checkRefutation graze forgeTwoIndividuals = false := by
  decide
theorem rejects_a_forged_derivation_prefix : checkRefutation graze forgePrefix = false := by decide
theorem rejects_a_premise_that_was_never_derived :
    checkRefutation graze forgeMissingPrefix = false := by decide
theorem rejects_premises_in_the_wrong_order : checkRefutation graze forgeWrongOrder = false := by
  decide

/-! ### `feed` is not refutable, and that is proved rather than observed -/

/-- The closure of `feed`, written out. One derived triple: leo is a Carnivore. -/
def feedClosure : List Triple := ⟨rLeo, V.type, rCarnivore⟩ :: feed

theorem feed_closure_is_plain : Plain feedClosure := by
  constructor <;> decide

theorem feed_inside_its_closure : ∀ t ∈ feed, t ∈ feedClosure := by decide

/-- No `owl:sameAs` anywhere in the closure, so the hypothesis of the general
theorem is discharged rather than assumed. -/
theorem feed_has_no_sameAs (a b : Term) (h : Der feed ⟨a, V.sameAs, b⟩) : a = b :=
  absurd (feed_closure_is_plain.der_mem feed_inside_its_closure h)
    (feed_closure_is_plain.absent V.sameAs (by decide) (by decide) (by decide) a b)

/-- No individual is in both halves of the disjointness axiom, checked over the
closure by `decide` rather than by reading the file. -/
private theorem feed_closure_has_no_clash :
    ∀ t ∈ feedClosure, ∀ u ∈ feedClosure, ∀ v ∈ feedClosure,
      ¬(t.p = RV.disjointWith ∧ u.p = V.type ∧ u.o = t.s ∧
        v.p = V.type ∧ v.o = t.o ∧ v.s = u.s) := by decide

/-! `feed_is_not_refuted` below is about `Semantics.lean`'s `Conditions`, not
about the OWL 2 RDF-Based Semantics, and this is where that is recorded. Until
15 September 2026 it was recorded only in `Semantics.lean`'s docstring, with a
reason that turned out to be wrong; this file was byte-identical to the one that
predates `W3C.lean` while that docstring said the caveat sat "at the point of the
assumption".

Two things stop the transfer and they are different in kind.

FIRST, the direction. `Unsat G` is a universal negative over a model class, so a
SMALLER class makes it EASIER to hold and `¬ Unsat` harder. Positive refutations
transfer outward for free, because `W3CModel I IP G → Model I G`; `¬ Unsat` does
not, and would need a `W3CModel` that also satisfies `RefuteConditions`.

SECOND, this particular interpretation is not one. `feed` carries
`Lion rdfs:subClassOf Carnivore` and types nothing as an `rdfs:Class`, so
`W3C.sc_fwd`, Table 5.8 row 1 forward, fails: its conclusion demands
`Lion ∈ IC`. `sc_fwd` mentions no `IP`, so the `IP := fun _ => False` reading
that carries four other non-entailments in this repository over to the conforming
class does not help here. -/

/-- The obstruction, checked rather than asserted. The closure has the
`rdfs:subClassOf` triple that fires `W3C.sc_fwd` and no typing to satisfy the
`IC` conjunct that field concludes, so no choice of `IP` makes
`herbrandL feedClosure` a `W3CModel`.

`V.Class` is taken from `W3C.lean` rather than respelled here, which is why this
file imports it: the IRI is the whole content of the theorem and a second copy of
it would be a second thing to keep in step. -/
theorem feed_closure_misses_the_class_typing :
    ((⟨rLion, V.subClassOf, rCarnivore⟩ : Triple) ∈ feedClosure) ∧
      (⟨rLion, V.type, V.Class⟩ : Triple) ∉ feedClosure := by decide


/-- **A graph with a disjointness axiom that is NOT refutable.** Without this the
refutation layer would be consistent with a checker that accepts everything.

Relative to `Conditions` and to `RefuteConditions`, not to the specification's
model class; the paragraph above says what stops the transfer and
`feed_closure_misses_the_class_typing` pins it. -/
theorem feed_is_not_refuted : ¬ Unsat feed := by
  refine not_unsat_of_joint_model (no_violation_means_a_joint_model feed feed_has_no_sameAs ?_)
  intro c1 c2 x h1 h2 h3
  have m1 := feed_closure_is_plain.der_mem feed_inside_its_closure h1
  have m2 := feed_closure_is_plain.der_mem feed_inside_its_closure h2
  have m3 := feed_closure_is_plain.der_mem feed_inside_its_closure h3
  exact feed_closure_has_no_clash _ m1 _ m2 _ m3 ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The attempt to refute the consistent graph, which differs from the accepted
refutation only in that `leo rdf:type Herbivore` is not available. -/
def feedAttempt : Refutation :=
  ⟨[{ rule := .rdfs9
      premises := [⟨rLeo, V.type, rLion⟩, ⟨rLion, V.subClassOf, rCarnivore⟩]
      conclusion := ⟨rLeo, V.type, rCarnivore⟩ }],
   grazeFinal⟩

/-- And the checker rejects it. Taken with `feed_is_not_refuted`, the rejection
is correct and not a limitation. -/
theorem the_checker_rejects_the_attempt_on_the_consistent_graph :
    checkRefutation feed feedAttempt = false := by decide

/-! ## The explosion, and the trap inside it

Over a refuted graph the disjointness-aware warrant is empty, so a derivation
certificate says nothing. The trap is that `certificate_sound`'s own verdict does
NOT collapse, because `Entails` quantifies over `Model I G` alone and that class
is never empty. A consumer reading `"ok":true` from `oo-cert` over a
self-contradicting ontology is reading a true sentence about a model class that
ignores disjointness. -/

def rJunk : Triple := ⟨"<http://ex.org/a>", "<http://ex.org/b>", "<http://ex.org/c>"⟩

/-- Any triple at all has the disjointness-aware warrant over `graze`. -/
theorem an_ordinary_certificate_is_worthless_over_the_refuted_graph :
    EntailsIn (RModel graze) rJunk :=
  unsat_entails_everything graze_is_refuted rJunk

def grazeClosure : List Triple := ⟨rLeo, V.type, rCarnivore⟩ :: graze

theorem graze_closure_is_plain : Plain grazeClosure := by
  constructor <;> decide

theorem graze_inside_its_closure : ∀ t ∈ graze, t ∈ grazeClosure := by decide

/-- **And the old verdict does not notice.** `graze` is refuted, yet `Entails
graze` is still a non-trivial relation: `herbrandL grazeClosure` is a model of
`graze` in which the junk triple is false. So a triple certificate over a
refuted graph checks green and means nothing, and nothing in
`certificate_sound` reports that. This is why `oo-refute guard` exists. -/
theorem the_junk_triple_is_not_in_the_closure : rJunk ∉ grazeClosure := by decide

/-- The same obstruction as `feed_closure_misses_the_class_typing`, on the other
graph this file builds a model of. -/
theorem graze_closure_misses_the_class_typing :
    ((⟨rLion, V.subClassOf, rCarnivore⟩ : Triple) ∈ grazeClosure) ∧
      (⟨rLion, V.type, V.Class⟩ : Triple) ∉ grazeClosure := by decide

/-- About `Semantics.lean`'s `Conditions`, like every other negative result built
from a Herbrand interpretation here, and it is one of the four that does not
transfer to `W3CModel`. `grazeClosure` carries `Lion rdfs:subClassOf Carnivore`
and types nothing as an `rdfs:Class`, so `W3C.sc_fwd` fails on the `IC` conjunct
it concludes; `graze_closure_misses_the_class_typing` just above pins that, and the
field mentions no `IP`, so the empty-`IP` reading that carries four other
non-entailments over does not apply. -/
theorem and_the_old_verdict_does_not_notice : ¬ Entails graze rJunk := fun h =>
  the_junk_triple_is_not_in_the_closure
    (h (herbrandL grazeClosure) (graze_closure_is_plain.model graze_inside_its_closure))

/-! ## Axioms, pinned -/

/-- info: 'OOCert.closure_is_a_model' does not depend on any axioms -/
#guard_msgs in
#print axioms closure_is_a_model

/-- info: 'OOCert.Der_sound' does not depend on any axioms -/
#guard_msgs in
#print axioms Der_sound

/-- info: 'OOCert.no_violation_means_a_joint_model' does not depend on any axioms -/
#guard_msgs in
#print axioms no_violation_means_a_joint_model

/-- info: 'OOCert.unsat_means_a_violation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unsat_means_a_violation

/-- info: 'OOCert.graze_is_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms graze_is_refuted

/-- info: 'OOCert.feed_closure_misses_the_class_typing' depends on axioms: [propext] -/
#guard_msgs in
#print axioms feed_closure_misses_the_class_typing

/-- info: 'OOCert.graze_closure_misses_the_class_typing' depends on axioms: [propext] -/
#guard_msgs in
#print axioms graze_closure_misses_the_class_typing

/-- info: 'OOCert.feed_is_not_refuted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms feed_is_not_refuted

/-- info: 'OOCert.and_the_old_verdict_does_not_notice' depends on axioms: [propext] -/
#guard_msgs in
#print axioms and_the_old_verdict_does_not_notice

end OOCert
