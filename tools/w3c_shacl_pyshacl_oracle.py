#!/usr/bin/env python3
"""Calibration for tests/w3c_shacl_conformance_test.rs: run the same suite, the
same walk and the same comparison, with pyshacl as the engine.

A conformance score is only a measurement if the yardstick is known to be
fair. `tests/w3c_shacl_conformance_test.rs` compares the `sh:conforms` verdict
plus the SET of (focus node, sh:sourceShape, sh:sourceConstraintComponent)
triples, with blank nodes canonicalised. That is stricter than the W3C's
"partial compliance" and looser than its "full compliance", so neither
published number tells you whether a low score means a weak engine or a harsh
harness.

This script answers that. It walks `mf:include` from tests/w3c-shacl/manifest.ttl
exactly as the Rust harness does, applies exactly the same comparison, and
drives pyshacl instead of open-ontologies. A mature engine scoring near the top
under this lens means the lens is sound.

Measured 2026-09-13, pyshacl 0.40.1 / rdflib 7.6.0, suite commit 94d8bc2:

    total 120   PASS 111   FAIL 8   ERROR 1

against open-ontologies' PASS 32 / FAIL 26 / UNDETERMINED 62 / ERROR 0 on the
same run. The gap is the engine, not the harness.

Deliberately NOT wired into CI. The `w3c-shacl` job has to stay offline, cheap
and deterministic, and adding a Python dependency to it would buy a number that
changes when pyshacl changes rather than when this engine does. Run it by hand
when the harness itself is edited.

Usage:
    pip install pyshacl
    python3 tools/w3c_shacl_pyshacl_oracle.py [--suite tests/w3c-shacl]
"""
import argparse
import os
import pathlib
import sys

try:
    import pyshacl
    from rdflib import BNode, Graph, Namespace, RDF, URIRef
except ImportError:  # pragma: no cover - the message is the whole handler
    sys.exit("this script needs pyshacl and rdflib: pip install pyshacl")

BASE = "https://w3c.github.io/data-shapes/data-shapes-test-suite/tests/"
MF = Namespace("http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#")
SHT = Namespace("http://www.w3.org/ns/shacl-test#")
SH = Namespace("http://www.w3.org/ns/shacl#")
NONE = URIRef("urn:open-ontologies:absent")


def canon(term):
    """The Rust harness's `canon`: blank nodes are opaque, IRIs are bare, and
    literals keep their N-Triples form."""
    if isinstance(term, BNode):
        return "_:"
    if isinstance(term, URIRef):
        return str(term)
    return term.n3()


def result_keys(graph, report_node, predicate):
    keys = set()
    for r in graph.objects(report_node, predicate):
        keys.add((
            canon(graph.value(r, SH.focusNode) or NONE),
            canon(graph.value(r, SH.sourceShape) or NONE),
            canon(graph.value(r, SH.sourceConstraintComponent) or NONE),
        ))
    return keys


def main():
    ap = argparse.ArgumentParser()
    default_suite = pathlib.Path(__file__).resolve().parent.parent / "tests" / "w3c-shacl"
    ap.add_argument("--suite", default=str(default_suite))
    args = ap.parse_args()
    root = os.path.realpath(args.suite)

    def base_of(p):
        return BASE + os.path.relpath(p, root)

    def path_of(iri):
        if not str(iri).startswith(BASE):
            sys.exit(f"include leaves the vendored suite: {iri}")
        return os.path.join(root, str(iri)[len(BASE):])

    def load(p):
        g = Graph()
        g.parse(p, format="turtle", publicID=base_of(p))
        return g

    cases, seen = [], set()

    def walk(path):
        path = os.path.realpath(path)
        if path in seen:
            return
        seen.add(path)
        g = load(path)
        for manifest in g.subjects(RDF.type, MF.Manifest):
            for entries in g.objects(manifest, MF.entries):
                for entry in g.items(entries):
                    if (entry, RDF.type, SHT.Validate) not in g:
                        continue
                    action = g.value(entry, MF.action)
                    name = os.path.relpath(path, root)[: -len(".ttl")]
                    cases.append((
                        name,
                        path_of(g.value(action, SHT.dataGraph)),
                        path_of(g.value(action, SHT.shapesGraph)),
                        g.value(entry, MF.result),
                        g,
                    ))
        for inc in g.objects(None, MF.include):
            walk(path_of(inc))

    walk(os.path.join(root, "manifest.ttl"))
    cases.sort(key=lambda c: c[0])

    passed = failed = errored = 0
    notes = []
    for name, data_path, shapes_path, result, manifest_graph in cases:
        expect_failure = result == SHT.Failure
        try:
            ok, report, _ = pyshacl.validate(
                load(data_path), shacl_graph=load(shapes_path), advanced=True, inplace=False
            )
        except Exception as exc:  # noqa: BLE001 - an engine crash is a bucket, not a bug here
            if expect_failure:
                passed += 1
            else:
                errored += 1
                notes.append((name, "ERROR", str(exc).splitlines()[0][:100]))
            continue

        if expect_failure:
            failed += 1
            notes.append((name, "FAIL", "the suite requires a reported failure; pyshacl gave a verdict"))
            continue

        expected_conforms = bool(manifest_graph.value(result, SH.conforms))
        expected = result_keys(manifest_graph, result, SH.result)
        actual = result_keys(report, next(report.subjects(RDF.type, SH.ValidationReport)), SH.result)
        if ok != expected_conforms:
            failed += 1
            notes.append((name, "FAIL", f"verdict: expected conforms={expected_conforms}, got {ok}"))
        elif actual != expected:
            failed += 1
            notes.append((
                name,
                "FAIL",
                f"results: {len(expected - actual)} missing, {len(actual - expected)} unexpected",
            ))
        else:
            passed += 1

    print(
        f"pyshacl under the open-ontologies comparison: "
        f"total {len(cases)}  PASS {passed}  FAIL {failed}  ERROR {errored}"
    )
    for name, bucket, why in notes:
        print(f"  {name:<44} {bucket}: {why}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
