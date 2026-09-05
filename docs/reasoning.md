# SHIQ Reasoning

Native Rust SHIQ tableaux reasoner. No JVM is required.

The implemented logic is SHIQ: ALC with transitive roles, role hierarchies,
inverse roles and qualified number restrictions. Nominals are not implemented.
The `Concept` enum has no nominal constructor, `owl:oneOf` is never parsed and
falls through to an opaque atomic class, `owl:hasValue` is approximated as an
existential restriction whose filler is an atomic concept named after the
individual, and datatype ranges are skipped. An ontology that uses
`owl:hasValue` returns undetermined classes rather than a classification. The
measurements are in
[benchmark/reasoner/regressions/README.md](../benchmark/reasoner/regressions/README.md).

| DL Feature | Symbol | OWL Construct |
| ---------- | ------ | ------------- |
| Atomic negation | not A | complementOf |
| Conjunction | C and D | intersectionOf |
| Disjunction | C or D | unionOf |
| Existential | exists R.C | someValuesFrom |
| Universal | forall R.C | allValuesFrom |
| Min cardinality | >=n R.C | minQualifiedCardinality |
| Max cardinality | <=n R.C | maxQualifiedCardinality |
| Role hierarchy | R subprop S | subPropertyOf |
| Transitive roles | Trans(R) | TransitiveProperty |
| Inverse roles | R inverse | inverseOf |
| Symmetric roles | Sym(R) | SymmetricProperty |
| Functional | Fun(R) | FunctionalProperty |
| ABox reasoning | a:C | NamedIndividual |
| Nominals | {a} | oneOf: not implemented |
| Nominal in a restriction | exists R.{a} | hasValue: approximated as an atomic concept |
| Datatypes | d | Datatype ranges are skipped |

## Agent-Based Parallel Classification

1. **Satisfiability Agent** — Tests each class in parallel using rayon
2. **Subsumption Agent** — Pairwise subsumption tests, pruned by told-subsumer closure
3. **Explanation Agent** — Traces clash derivations for unsatisfiable classes
4. **ABox Agent** — Individual consistency and type inference

| Reasoner | Language | JVM | Parallel | Logic |
| -------- | -------- | --- | -------- | ----- |
| **Open Ontologies** | Rust | No | Yes (rayon) | SHIQ |
| HermiT | Java | Yes | No | SROIQ(D) |
| Pellet | Java | Yes | No | SROIQ(D) |

## Reasoning Profiles

| Profile | What it does |
| ------- | ------------ |
| `rdfs` | Subclass closure, domain/range inference |
| `owl-rl` | + transitive/symmetric/inverse, sameAs, equivalentClass |
| `owl-rl-ext` | + someValuesFrom, allValuesFrom, hasValue, intersectionOf, unionOf |
| `owl-dl` | SHIQ tableaux: satisfiability, classification, ABox reasoning. Nominals are not implemented and datatype ranges are skipped |

## Tools

| Tool | Purpose |
| ---- | ------- |
| `onto_reason` | Run inference with selected profile |
| `onto_dl_explain` | Explain why a class is unsatisfiable (clash trace) |
| `onto_dl_check` | Check if one class is subsumed by another |
