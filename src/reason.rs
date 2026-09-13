use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::graph::GraphStore;

// Well-known IRIs
const RDF_TYPE: &str = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>";
const RDFS_SUBCLASS: &str = "<http://www.w3.org/2000/01/rdf-schema#subClassOf>";
const RDFS_SUBPROP: &str = "<http://www.w3.org/2000/01/rdf-schema#subPropertyOf>";
const RDFS_DOMAIN: &str = "<http://www.w3.org/2000/01/rdf-schema#domain>";
const RDFS_RANGE: &str = "<http://www.w3.org/2000/01/rdf-schema#range>";
const OWL_TRANSITIVE: &str = "<http://www.w3.org/2002/07/owl#TransitiveProperty>";
const OWL_SYMMETRIC: &str = "<http://www.w3.org/2002/07/owl#SymmetricProperty>";
const OWL_INVERSE: &str = "<http://www.w3.org/2002/07/owl#inverseOf>";
const OWL_SAMEAS: &str = "<http://www.w3.org/2002/07/owl#sameAs>";
const OWL_EQUIV_CLASS: &str = "<http://www.w3.org/2002/07/owl#equivalentClass>";
const OWL_EQUIV_PROP: &str = "<http://www.w3.org/2002/07/owl#equivalentProperty>";
const OWL_SOME_VALUES: &str = "<http://www.w3.org/2002/07/owl#someValuesFrom>";
const OWL_ALL_VALUES: &str = "<http://www.w3.org/2002/07/owl#allValuesFrom>";
const OWL_HAS_VALUE: &str = "<http://www.w3.org/2002/07/owl#hasValue>";
const OWL_ON_PROPERTY: &str = "<http://www.w3.org/2002/07/owl#onProperty>";
const OWL_INTERSECTION: &str = "<http://www.w3.org/2002/07/owl#intersectionOf>";
const OWL_UNION: &str = "<http://www.w3.org/2002/07/owl#unionOf>";
const RDF_FIRST: &str = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#first>";
const RDF_REST: &str = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#rest>";
const RDF_NIL: &str = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#nil>";

/// A triple over interned ids.
type Fact = (u32, u32, u32);

/// One line of a certificate: the rule, what it concluded, and the premises
/// it read, in the order `lean/OOCert/Rules.lean` documents for that rule.
struct Derivation {
    rule: &'static str,
    conclusion: Fact,
    premises: Vec<Fact>,
}

/// Intern strings to u32 IDs for efficient reasoning.
struct Interner {
    to_id: HashMap<String, u32>,
    to_str: Vec<String>,
}

impl Interner {
    fn new() -> Self {
        Self {
            to_id: HashMap::new(),
            to_str: Vec::new(),
        }
    }

    fn intern(&mut self, s: &str) -> u32 {
        if let Some(&id) = self.to_id.get(s) {
            return id;
        }
        let id = self.to_str.len() as u32;
        self.to_str.push(s.to_string());
        self.to_id.insert(s.to_string(), id);
        id
    }

    fn resolve(&self, id: u32) -> &str {
        &self.to_str[id as usize]
    }
}

/// OWL2-RL reasoner using interned u32 triples and fixpoint iteration.
///
/// Profiles:
///   "rdfs"       — RDFS rules (subclass, domain/range, subproperty)
///   "owl-rl"     — RDFS + core OWL-RL (transitive, symmetric, inverse,
///                  sameAs, equivalentClass/Property)
///   "owl-rl-ext" — All above + someValuesFrom, allValuesFrom, hasValue,
///                  intersectionOf, unionOf
/// The graph materialised inferences are written to when the caller asks for
/// them to be kept apart from what was asserted.
pub const INFERRED_GRAPH: &str = "https://open-ontologies.org/graph/inferred";

/// Where `reason` puts the triples it materialises.
///
/// The choice is a failure-direction one, not a matter of taste. A marker
/// triple on statements sitting in the default graph obliges every consumer to
/// filter, and the one that forgets publishes an inference as an assertion. A
/// separate graph fails the other way: a consumer that forgets sees fewer
/// triples, never wrong ones.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InferenceTarget {
    /// Merge into the default graph beside the asserted statements. The
    /// historical behaviour, kept so existing callers keep their contract.
    DefaultGraph,
    /// Keep them in [`INFERRED_GRAPH`], where nothing downstream can mistake
    /// an inference for an assertion.
    Inferred,
}

pub struct Reasoner;

impl Reasoner {
    pub fn run(
        graph: &Arc<GraphStore>,
        profile: &str,
        materialize: bool,
    ) -> anyhow::Result<String> {
        Self::run_with_target(graph, profile, materialize, InferenceTarget::DefaultGraph)
    }

    pub fn run_with_target(
        graph: &Arc<GraphStore>,
        profile: &str,
        materialize: bool,
        target: InferenceTarget,
    ) -> anyhow::Result<String> {
        Self::run_full(graph, profile, materialize, target, None)
    }

    /// Run the forward-chaining reasoner and, when `certificate_dir` is given,
    /// write a derivation certificate beside the result.
    ///
    /// The certificate is two tab-separated files: `asserted.tsv`, every
    /// triple the run started from, and `derivations.tsv`, one line per
    /// inferred triple naming the rule that produced it and the premises the
    /// rule read. `lean/` holds a checker for that format whose soundness is a
    /// machine-checked theorem (`OOCert.certificate_sound`): a certificate it
    /// accepts contains only triples entailed by the asserted graph under the
    /// RDF-based semantics of the vocabulary the rules use. The engine's own
    /// correctness is therefore not the thing a consumer has to trust; the
    /// checker's is, and the checker is a few hundred lines with a proof.
    ///
    /// The first thing the checker caught was in this file: `cls-svf1` used
    /// to derive membership in a subclass from membership in its restriction
    /// superclass, the converse of the axiom
    /// (tests/reason_rl_ext_soundness_test.rs).
    ///
    /// Not available for `owl-dl`: the tableaux path has no rule trace.
    pub fn run_full(
        graph: &Arc<GraphStore>,
        profile: &str,
        materialize: bool,
        target: InferenceTarget,
        certificate_dir: Option<&std::path::Path>,
    ) -> anyhow::Result<String> {
        // Delegate OWL-DL to tableaux reasoner
        if profile == "owl-dl" {
            if certificate_dir.is_some() {
                anyhow::bail!(
                    "the owl-dl tableaux path emits no derivation certificate; \
                     run rdfs, owl-rl or owl-rl-ext for a certified run"
                );
            }
            if target == InferenceTarget::Inferred {
                // Say so rather than materialise into the default graph while
                // the caller believes the inferences were kept apart.
                anyhow::bail!(
                    "the owl-dl tableaux path does not yet write to {INFERRED_GRAPH}; \
                     run it with the default target, or use owl-rl / owl-rl-ext"
                );
            }
            return crate::tableaux::DlReasoner::run(graph, materialize);
        }

        let profile_used = match profile {
            "owl-rl" => "owl-rl",
            "owl-rl-ext" => "owl-rl-ext",
            _ => "rdfs",
        };
        let include_owl = profile_used == "owl-rl" || profile_used == "owl-rl-ext";
        let include_ext = profile_used == "owl-rl-ext";

        // Extract and intern all triples
        let raw_triples = graph.all_triples()?;
        let mut interner = Interner::new();
        let mut facts: Vec<(u32, u32, u32)> = Vec::with_capacity(raw_triples.len());
        for (s, p, o) in &raw_triples {
            facts.push((interner.intern(s), interner.intern(p), interner.intern(o)));
        }

        // Intern well-known IRIs
        let rdf_type = interner.intern(RDF_TYPE);
        let rdfs_subclass = interner.intern(RDFS_SUBCLASS);
        let rdfs_subprop = interner.intern(RDFS_SUBPROP);
        let owl_sameas = interner.intern(OWL_SAMEAS);
        // Every well-known id is interned once, before the loop, so the
        // schema indices below can be rebuilt from the closure each iteration
        // without borrowing the interner mutably inside it.
        let rdfs_domain = interner.intern(RDFS_DOMAIN);
        let rdfs_range = interner.intern(RDFS_RANGE);
        let owl_transitive = interner.intern(OWL_TRANSITIVE);
        let owl_symmetric = interner.intern(OWL_SYMMETRIC);
        let owl_inverse = interner.intern(OWL_INVERSE);
        let owl_equiv_class = interner.intern(OWL_EQUIV_CLASS);
        let owl_equiv_prop = interner.intern(OWL_EQUIV_PROP);
        let owl_on_property = interner.intern(OWL_ON_PROPERTY);
        let owl_some_values = interner.intern(OWL_SOME_VALUES);
        let owl_all_values = interner.intern(OWL_ALL_VALUES);
        let owl_has_value = interner.intern(OWL_HAS_VALUE);
        let owl_intersection = interner.intern(OWL_INTERSECTION);
        let owl_union = interner.intern(OWL_UNION);
        let rdf_first = interner.intern(RDF_FIRST);
        let rdf_rest = interner.intern(RDF_REST);
        let rdf_nil = interner.intern(RDF_NIL);

        // ── Fixpoint iteration ──────────────────────────────────────
        let mut triple_set: HashSet<Fact> = facts.iter().copied().collect();
        let initial_size = triple_set.len();
        let mut iterations = 0;

        // Certificate bookkeeping. A conclusion is recorded the first time it
        // is derived and never again, so the certificate has exactly one line
        // per inferred triple and `derivations.len() == inferred_count` is an
        // invariant the tests pin. Nothing here runs unless a certificate was
        // asked for: the hot path pays one branch per candidate triple.
        let certify = certificate_dir.is_some();
        let mut derivations: Vec<Derivation> = Vec::new();
        let mut recorded: HashSet<Fact> = HashSet::new();

        loop {
            iterations += 1;
            let before = triple_set.len();
            let mut new: Vec<Fact> = Vec::new();

            // Schema indices, rebuilt from the closure on every iteration.
            //
            // These used to be filtered ONCE out of the pre-loop snapshot while
            // only the three data indices below were rebuilt, so the run was
            // not a fixpoint of its own rule set: a `rdfs:domain` triple that
            // the reasoner itself derived, by rdfs7 over a subproperty of
            // rdfs:domain or by scm-eqp, was never used, and running `reason` a
            // second time derived more than running it once. The number of runs
            // needed was the length of the longest chain of such rules, not two.
            //
            // For certificates that mattered more than for query answers.
            // Materialising turns run N's conclusions into run N+1's premises,
            // so `asserted.tsv` could list the reasoner's own output as an
            // axiom with nothing marking it as derived, and the soundness
            // theorem is conditional on the assertions. Reaching the fixpoint
            // in one run is what makes a single certificate the whole story.
            //
            // The cost is a constant factor on a scan the loop already does.
            let domain_map: Vec<(u32, u32)> = triple_set.iter()
                .filter(|&&(_, p, _)| p == rdfs_domain)
                .map(|&(s, _, o)| (s, o)).collect();
            let range_map: Vec<(u32, u32)> = triple_set.iter()
                .filter(|&&(_, p, _)| p == rdfs_range)
                .map(|&(s, _, o)| (s, o)).collect();
            let transitive_set: HashSet<u32> = triple_set.iter()
                .filter(|&&(_, p, o)| p == rdf_type && o == owl_transitive)
                .map(|&(s, _, _)| s).collect();
            let symmetric_set: HashSet<u32> = triple_set.iter()
                .filter(|&&(_, p, o)| p == rdf_type && o == owl_symmetric)
                .map(|&(s, _, _)| s).collect();
            let inverse_pairs: Vec<(u32, u32)> = triple_set.iter()
                .filter(|&&(_, p, _)| p == owl_inverse)
                .map(|&(s, _, o)| (s, o)).collect();
            let equiv_class: Vec<(u32, u32)> = triple_set.iter()
                .filter(|&&(_, p, _)| p == owl_equiv_class)
                .map(|&(s, _, o)| (s, o)).collect();
            let equiv_prop: Vec<(u32, u32)> = triple_set.iter()
                .filter(|&&(_, p, _)| p == owl_equiv_prop)
                .map(|&(s, _, o)| (s, o)).collect();

            // OWL restriction structures and RDF lists (owl-rl-ext only).
            let mut restr_prop: HashMap<u32, u32> = HashMap::new();
            let mut restr_svf: HashMap<u32, u32> = HashMap::new();
            let mut restr_hv: HashMap<u32, u32> = HashMap::new();
            let mut intersection_classes: Vec<(u32, u32, Vec<Fact>, Vec<u32>)> = Vec::new();
            let mut union_classes: Vec<(u32, u32, Vec<Fact>, Vec<u32>)> = Vec::new();
            let mut svf_rules: Vec<(u32, u32, u32)> = Vec::new();
            let mut hv_rules: Vec<(u32, u32, u32)> = Vec::new();
            let mut avf_rules: Vec<(u32, u32, u32)> = Vec::new();
            if include_ext {
                let mut restr_avf: HashMap<u32, u32> = HashMap::new();
                for &(s, p, o) in triple_set.iter() {
                    if p == owl_on_property { restr_prop.insert(s, o); }
                    if p == owl_some_values { restr_svf.insert(s, o); }
                    if p == owl_all_values { restr_avf.insert(s, o); }
                    if p == owl_has_value { restr_hv.insert(s, o); }
                }
                avf_rules = restr_avf.iter()
                    .filter_map(|(&r, &filler)| restr_prop.get(&r).map(|&prop| (prop, filler, r)))
                    .collect();
                svf_rules = restr_svf.iter()
                    .filter_map(|(&r, &filler)| restr_prop.get(&r).map(|&prop| (prop, filler, r)))
                    .collect();
                hv_rules = restr_hv.iter()
                    .filter_map(|(&r, &val)| restr_prop.get(&r).map(|&prop| (prop, val, r)))
                    .collect();

                // A list is read only when it is well formed: every node carries
                // the rdf:first and rdf:rest the certificate checker will look
                // for, and the chain reaches rdf:nil. It used to be read
                // leniently and the class rules fired on whatever came back. The
                // checker has no rule for a list it cannot walk, so the reasoner
                // no longer derives from one either; deriving less from
                // malformed input is the sound direction. Each entry keeps the
                // head node and the chain triples so a certificate can cite them.
                let first_map: HashMap<u32, u32> = triple_set.iter()
                    .filter(|&&(_, p, _)| p == rdf_first)
                    .map(|&(s, _, o)| (s, o)).collect();
                let rest_map: HashMap<u32, u32> = triple_set.iter()
                    .filter(|&&(_, p, _)| p == rdf_rest)
                    .map(|&(s, _, o)| (s, o)).collect();
                let walk_list = |head: u32| -> Option<(Vec<Fact>, Vec<u32>)> {
                    let mut chain = Vec::new();
                    let mut items = Vec::new();
                    let mut cur = head;
                    // Bounded so that a cyclic rdf:rest cannot spin.
                    for _ in 0..100_000 {
                        if cur == rdf_nil {
                            return Some((chain, items));
                        }
                        let item = *first_map.get(&cur)?;
                        let next = *rest_map.get(&cur)?;
                        chain.push((cur, rdf_first, item));
                        chain.push((cur, rdf_rest, next));
                        items.push(item);
                        cur = next;
                    }
                    None
                };
                for &(s, p, o) in triple_set.iter() {
                    if p == owl_intersection
                        && let Some((chain, items)) = walk_list(o)
                        && !items.is_empty()
                    {
                        intersection_classes.push((s, o, chain, items));
                    }
                    if p == owl_union
                        && let Some((chain, items)) = walk_list(o)
                        && !items.is_empty()
                    {
                        union_classes.push((s, o, chain, items));
                    }
                }
            }

            // Build per-iteration indices
            let type_idx: Vec<(u32, u32)> = triple_set.iter()
                .filter(|&&(_, p, _)| p == rdf_type)
                .map(|&(s, _, o)| (s, o)).collect();
            let subclass_idx: Vec<(u32, u32)> = triple_set.iter()
                .filter(|&&(_, p, _)| p == rdfs_subclass)
                .map(|&(s, _, o)| (s, o)).collect();
            let subprop_idx: Vec<(u32, u32)> = triple_set.iter()
                .filter(|&&(_, p, _)| p == rdfs_subprop)
                .map(|&(s, _, o)| (s, o)).collect();

            // Build a subclass lookup: sub → [super]
            let mut sub_to_super: HashMap<u32, Vec<u32>> = HashMap::new();
            for &(sub, sup) in &subclass_idx {
                sub_to_super.entry(sub).or_default().push(sup);
            }

            // Every rule goes through this. It pushes the candidate and, when a
            // certificate was asked for, records the first derivation of each
            // triple not already in the closure, with the premises in the
            // order the checker expects for that rule.
            let mut emit = |t: Fact, rule: &'static str, premises: &[Fact]| {
                if certify && !triple_set.contains(&t) && recorded.insert(t) {
                    derivations.push(Derivation { rule, conclusion: t, premises: premises.to_vec() });
                }
                new.push(t);
            };

            // ── RDFS rules ──────────────────────────────────────────

            // rdfs9: x type sub, sub subClassOf super → x type super
            for &(x, sub) in &type_idx {
                if let Some(supers) = sub_to_super.get(&sub) {
                    for &sup in supers {
                        if sub != sup {
                            emit((x, rdf_type, sup), "rdfs9",
                                &[(x, rdf_type, sub), (sub, rdfs_subclass, sup)]);
                        }
                    }
                }
            }

            // rdfs11: a subClassOf b, b subClassOf c → a subClassOf c
            for &(a, b) in &subclass_idx {
                if let Some(cs) = sub_to_super.get(&b) {
                    for &c in cs {
                        if a != b && b != c && a != c {
                            emit((a, rdfs_subclass, c), "rdfs11",
                                &[(a, rdfs_subclass, b), (b, rdfs_subclass, c)]);
                        }
                    }
                }
            }

            // rdfs2: s p o, p domain class → s type class
            for &(prop, cls) in &domain_map {
                for &(s, p, o) in triple_set.iter() {
                    if p == prop {
                        emit((s, rdf_type, cls), "rdfs2", &[(s, p, o), (prop, rdfs_domain, cls)]);
                    }
                }
            }

            // rdfs3: s p o, p range class → o type class (IRI only)
            for &(prop, cls) in &range_map {
                for &(s, p, o) in triple_set.iter() {
                    // The guard has to exclude LITERALS, which cannot be the
                    // subject of the conclusion, and nothing else. Requiring an
                    // IRI also dropped every range inference onto a blank node,
                    // so a blank-node value never got typed, rdfs9 starved
                    // behind it, and a SHACL shape targeting that class found
                    // no focus nodes. rdfs2 twelve lines up has no such guard.
                    if p == prop && !interner.resolve(o).starts_with('"') {
                        emit((o, rdf_type, cls), "rdfs3", &[(s, p, o), (prop, rdfs_range, cls)]);
                    }
                }
            }

            // rdfs5: subproperty transitivity
            let mut subp_to_super: HashMap<u32, Vec<u32>> = HashMap::new();
            for &(sub, sup) in &subprop_idx {
                subp_to_super.entry(sub).or_default().push(sup);
            }
            for &(a, b) in &subprop_idx {
                if let Some(cs) = subp_to_super.get(&b) {
                    for &c in cs {
                        if a != b && b != c && a != c {
                            emit((a, rdfs_subprop, c), "rdfs5",
                                &[(a, rdfs_subprop, b), (b, rdfs_subprop, c)]);
                        }
                    }
                }
            }

            // rdfs7: s sub o, sub subPropertyOf super → s super o
            for &(sub, sup) in &subprop_idx {
                if sub != sup {
                    for &(s, p, o) in triple_set.iter() {
                        if p == sub {
                            emit((s, sup, o), "rdfs7", &[(s, sub, o), (sub, rdfs_subprop, sup)]);
                        }
                    }
                }
            }

            // Four rules below conclude a triple whose SUBJECT comes from an
            // object position, so a literal object would produce a triple no
            // RDF serialisation can express. The materialiser then failed on
            // the whole batch with "The subject of a triple must be an IRI or a
            // blank node", at a line number that moved between runs because it
            // depends on hash iteration order, and every inference from that
            // run was lost. OWL 2 RL scopes prp-symp, prp-inv1, prp-inv2 and
            // eq-sym to what can legally appear as a subject; this is that
            // scope, made explicit. Pinned by `tests/reason_literal_subject_test.rs`.
            let is_literal = |id: u32| interner.resolve(id).starts_with('"');

            // ── OWL-RL rules ────────────────────────────────────────
            if include_owl {
                // prp-trp: x P y, y P z → x P z
                for &tp in &transitive_set {
                    let pairs: Vec<(u32, u32)> = triple_set.iter()
                        .filter(|&&(_, p, _)| p == tp)
                        .map(|&(s, _, o)| (s, o)).collect();
                    let mut by_subj: HashMap<u32, Vec<u32>> = HashMap::new();
                    for &(s, o) in &pairs {
                        by_subj.entry(s).or_default().push(o);
                    }
                    for &(x, y) in &pairs {
                        if let Some(zs) = by_subj.get(&y) {
                            for &z in zs {
                                if x != z {
                                    emit((x, tp, z), "prp-trp",
                                        &[(tp, rdf_type, owl_transitive), (x, tp, y), (y, tp, z)]);
                                }
                            }
                        }
                    }
                }

                // prp-symp: s P o → o P s
                for &sp in &symmetric_set {
                    for &(s, p, o) in triple_set.iter() {
                        if p == sp && !is_literal(o) {
                            emit((o, sp, s), "prp-symp", &[(sp, rdf_type, owl_symmetric), (s, sp, o)]);
                        }
                    }
                }

                // prp-inv1, prp-inv2: s P o, P inverseOf Q → o Q s (both directions)
                for &(p, q) in &inverse_pairs {
                    for &(s, pred, o) in triple_set.iter() {
                        if is_literal(o) {
                            continue;
                        }
                        if pred == p {
                            emit((o, q, s), "prp-inv1", &[(p, owl_inverse, q), (s, p, o)]);
                        }
                        if pred == q {
                            emit((o, p, s), "prp-inv2", &[(p, owl_inverse, q), (s, q, o)]);
                        }
                    }
                }

                // eq-sym: sameAs symmetry
                for &(s, p, o) in triple_set.iter() {
                    if p == owl_sameas && !is_literal(o) {
                        emit((o, owl_sameas, s), "eq-sym", &[(s, owl_sameas, o)]);
                    }
                }

                // scm-eqc1, scm-eqc2: equivalentClass → bidirectional subClassOf
                // Both conclusions are W3C scm-eqc1, which licenses two of them
                // from one premise. The second used to be emitted as "scm-eqc2",
                // which is a DIFFERENT W3C rule: it concludes owl:equivalentClass
                // from two subClassOf triples, the opposite direction. An auditor
                // reading that id and looking it up found the wrong rule, which
                // is precisely what the cls-hv1 comment below forbids. Emitting
                // both steps under the rule that licenses them also frees the
                // name for the real scm-eqc2 when it is implemented.
                for &(a, b) in &equiv_class {
                    emit((a, rdfs_subclass, b), "scm-eqc1", &[(a, owl_equiv_class, b)]);
                    emit((b, rdfs_subclass, a), "scm-eqc1", &[(a, owl_equiv_class, b)]);
                }

                // scm-eqp1, scm-eqp2: equivalentProperty → bidirectional subPropertyOf
                // Same for scm-eqp1 and the name scm-eqp2.
                for &(a, b) in &equiv_prop {
                    emit((a, rdfs_subprop, b), "scm-eqp1", &[(a, owl_equiv_prop, b)]);
                    emit((b, rdfs_subprop, a), "scm-eqp1", &[(a, owl_equiv_prop, b)]);
                }
            }

            // ── OWL-RL extended (someValuesFrom, hasValue, intersection, union)
            if include_ext {
                // Build type lookup: instance → set of classes
                let mut inst_types: HashMap<u32, HashSet<u32>> = HashMap::new();
                for &(x, cls) in &type_idx {
                    inst_types.entry(x).or_default().insert(cls);
                }

                // cls-svf1: x P y, y type filler, restriction(P, svf=filler)
                //           → x type restriction
                //
                // Two derivations this rule used to make are gone, both found
                // when every rule had to correspond to one the Lean checker
                // can prove sound (tests/reason_rl_ext_soundness_test.rs):
                //   * `x type C` for every `C rdfs:subClassOf restriction`.
                //     That is the converse of the axiom. Membership in a
                //     superclass never gives membership in a subclass; the
                //     equivalentClass case that made it look right is carried
                //     by rdfs9 over the subClassOf triple scm-eqc emits.
                //   * `x type restriction` from `x P filler`, where the
                //     object is the filler class IRI itself. A class in
                //     object position is a resource, not an instance of
                //     itself.
                for &(prop, filler, restr) in &svf_rules {
                    let prop_pairs: Vec<(u32, u32)> = triple_set.iter()
                        .filter(|&&(_, p, _)| p == prop)
                        .map(|&(s, _, o)| (s, o)).collect();

                    let filler_insts: HashSet<u32> = type_idx.iter()
                        .filter(|&&(_, cls)| cls == filler)
                        .map(|&(inst, _)| inst).collect();

                    for &(x, y) in &prop_pairs {
                        if filler_insts.contains(&y) {
                            emit((x, rdf_type, restr), "cls-svf1", &[
                                (restr, owl_on_property, prop),
                                (restr, owl_some_values, filler),
                                (x, prop, y),
                                (y, rdf_type, filler),
                            ]);
                        }
                    }
                }

                // cls-avf: x type restriction(P, allValuesFrom c), x P y
                //          → y type c
                //
                // The restriction was parsed and the parse was thrown away, so
                // 123 owl:allValuesFrom axioms across six shipped files licensed
                // nothing. It is the cheapest missing rule in the OWL 2 RL
                // profile on both axes: the Rust is the cls-svf1 loop with the
                // premises the other way round, and the semantic condition is
                // the mirror of `svf`.
                for &(prop, filler, restr) in &avf_rules {
                    let in_restr: HashSet<u32> = type_idx.iter()
                        .filter(|&&(_, cls)| cls == restr)
                        .map(|&(inst, _)| inst).collect();
                    if in_restr.is_empty() {
                        continue;
                    }
                    for &(x, p, y) in triple_set.iter() {
                        if p == prop && in_restr.contains(&x) {
                            emit((y, rdf_type, filler), "cls-avf", &[
                                (restr, owl_on_property, prop),
                                (restr, owl_all_values, filler),
                                (x, rdf_type, restr),
                                (x, prop, y),
                            ]);
                        }
                    }
                }

                // cls-hv1: x type restriction(P, hasValue v) → x P v
                // cls-hv2: x P v, restriction(P, hasValue v) → x type restriction
                //
                // The rule emitted under the name `cls-hv1` used to be the
                // composite of `cax-sco` and W3C `cls-hv1`: it demanded an
                // explicit `k rdfs:subClassOf r` hop and fired on `x type k`,
                // so an individual typed with the restriction DIRECTLY derived
                // nothing. The engine reached the restriction class by its own
                // rdfs9 and then refused to use it, and a certificate could
                // carry `rdfs9  <k> rdf:type <R>` right next to a cls-hv1 step
                // that ignored it. Putting a W3C rule name in front of an
                // auditor obliges the rule to be that rule. The W3C form is
                // used here and loses nothing: the composite case is rdfs9
                // followed by this.
                for &(prop, val, restr) in &hv_rules {
                    for &(x, c) in &type_idx {
                        if c == restr {
                            emit((x, prop, val), "cls-hv1", &[
                                (restr, owl_on_property, prop),
                                (restr, owl_has_value, val),
                                (x, rdf_type, restr),
                            ]);
                        }
                    }
                    for &(s, p, o) in triple_set.iter() {
                        if p == prop && o == val {
                            emit((s, rdf_type, restr), "cls-hv2", &[
                                (restr, owl_on_property, prop),
                                (restr, owl_has_value, val),
                                (s, prop, val),
                            ]);
                        }
                    }
                }

                // cls-int1: x type ALL members → x type intersection class
                for (cls, head, chain, members) in &intersection_classes {
                    for (&x, x_types) in &inst_types {
                        if members.iter().all(|m| x_types.contains(m)) {
                            let premises: Vec<Fact> = if certify {
                                let mut v = vec![(*cls, owl_intersection, *head)];
                                v.extend(chain.iter().copied());
                                v.extend(members.iter().map(|&m| (x, rdf_type, m)));
                                v
                            } else {
                                Vec::new()
                            };
                            emit((x, rdf_type, *cls), "cls-int1", &premises);
                        }
                    }
                }

                // cls-uni: x type ANY member → x type union class
                for (cls, head, chain, members) in &union_classes {
                    for &(x, c) in &type_idx {
                        if members.contains(&c) {
                            let premises: Vec<Fact> = if certify {
                                let mut v = vec![(*cls, owl_union, *head)];
                                v.extend(chain.iter().copied());
                                v.push((x, rdf_type, c));
                                v
                            } else {
                                Vec::new()
                            };
                            emit((x, rdf_type, *cls), "cls-uni", &premises);
                        }
                    }
                }
            }

            // Insert new triples (dedup against existing)
            for t in new {
                triple_set.insert(t);
            }

            if triple_set.len() == before || iterations >= crate::runtime::reasoner_max_iterations() {
                break;
            }
        }

        let inferred_count = triple_set.len() - initial_size;

        // Materialize inferred triples
        if materialize && inferred_count > 0 {
            let original: HashSet<Fact> = facts.iter().copied().collect();
            let mut lines = String::new();
            for &(s, p, o) in &triple_set {
                if !original.contains(&(s, p, o)) {
                    lines.push_str(interner.resolve(s));
                    lines.push(' ');
                    lines.push_str(interner.resolve(p));
                    lines.push(' ');
                    lines.push_str(interner.resolve(o));
                    if target == InferenceTarget::Inferred {
                        lines.push_str(" <");
                        lines.push_str(INFERRED_GRAPH);
                        lines.push('>');
                    }
                    lines.push_str(" .\n");
                }
            }
            match target {
                InferenceTarget::DefaultGraph => graph.load_ntriples(&lines)?,
                InferenceTarget::Inferred => graph.load_nquads(&lines)?,
            };
        }

        // Sample
        let original: HashSet<Fact> = facts.iter().copied().collect();
        let sample: Vec<String> = triple_set.iter()
            .filter(|t| !original.contains(t))
            .filter(|&&(_, p, _)| p == rdf_type)
            .take(10)
            .map(|&(s, _, o)| format!("{} a {}", interner.resolve(s), interner.resolve(o)))
            .collect();

        let mut result = serde_json::json!({
            "profile_used": profile_used,
            "inferred_count": inferred_count,
            "iterations": iterations,
            "initial_triples": initial_size,
            "final_triples": triple_set.len(),
            "sample_inferences": sample
        });
        if !materialize {
            result["dry_run"] = serde_json::json!(true);
        }
        if target == InferenceTarget::Inferred {
            // A caller cannot ask the inferences back unless it is told where
            // they were put.
            result["inference_graph"] = serde_json::json!(INFERRED_GRAPH);
        }

        if let Some(dir) = certificate_dir {
            std::fs::create_dir_all(dir)?;
            let mut asserted = String::with_capacity(facts.len() * 96);
            for &(s, p, o) in &facts {
                asserted.push_str(interner.resolve(s));
                asserted.push('\t');
                asserted.push_str(interner.resolve(p));
                asserted.push('\t');
                asserted.push_str(interner.resolve(o));
                asserted.push('\n');
            }
            std::fs::write(dir.join("asserted.tsv"), asserted)?;

            let mut by_rule: std::collections::BTreeMap<&str, usize> = std::collections::BTreeMap::new();
            let mut lines = String::with_capacity(derivations.len() * 256);
            for d in &derivations {
                *by_rule.entry(d.rule).or_default() += 1;
                lines.push_str(d.rule);
                for &(s, p, o) in std::iter::once(&d.conclusion).chain(d.premises.iter()) {
                    lines.push('\t');
                    lines.push_str(interner.resolve(s));
                    lines.push('\t');
                    lines.push_str(interner.resolve(p));
                    lines.push('\t');
                    lines.push_str(interner.resolve(o));
                }
                lines.push('\n');
            }
            std::fs::write(dir.join("derivations.tsv"), lines)?;

            result["certificate"] = serde_json::json!({
                "dir": dir.display().to_string(),
                "format": "oo-cert/1",
                "asserted": facts.len(),
                "derivations": derivations.len(),
                "by_rule": by_rule,
                "check_with": "cd lean && lake exe oo-cert <dir>/asserted.tsv <dir>/derivations.tsv",
            });
        }

        Ok(result.to_string())
    }
}
