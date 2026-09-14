#!/usr/bin/env python3
"""Reason over an ontology, then have a verified checker say what that was worth.

Run it:

    python examples/certified_reasoning.py

It works with no Lean checker installed, which is the point: it writes the
certificate either way and tells you plainly whether anything was proved. To get
a verdict, build the checker once from a checkout of the Rust repository:

    cd lean && lake build

The three things this example is trying to show, in order of importance:

1. The engine states no verdict. It derives triples, writes a certificate and
   reports where it is. `oo-horn` decides what the run earned, and this package
   copies its words rather than forming its own.

2. The built-in table and a table you wrote earn DIFFERENT verdicts, and the
   difference is not a formality. The second run below appends one rule saying
   every supplier is compliant. It is false of the world, the engine fires it
   happily, and the checker accepts the certificate, because the inference really
   does follow FROM THAT RULE. What changes is the verdict word, the theorem
   named, and the digest of the table that was in force. A layer that collapsed
   those two into one word would be a machine for turning an assumption into a
   fact with a proof attached.

3. Nothing is materialised. Look at the store after the run: it is the size it
   was. A conclusion drawn under a supplied rule table holds only in models that
   satisfy that table, so writing it back in beside the assertions is how one
   run's output becomes the next run's axiom.
"""

import json
import tempfile
from pathlib import Path

from open_ontologies_lite import OntologyEngine
from open_ontologies_lite.horn.rules import AtomPat, RulePattern, builtin_rules

TYPE = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>"

ONTOLOGY = """
@prefix ex:   <http://example.org/> .
@prefix owl:  <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .

ex:Supplier    rdfs:subClassOf ex:Organisation .
ex:Organisation rdfs:subClassOf ex:LegalEntity .
ex:acme        a ex:Supplier .
ex:supplies    rdfs:domain ex:Supplier ; rdfs:range ex:Part .
ex:acme        ex:supplies ex:widget .
ex:partners    a owl:SymmetricProperty .
ex:acme        ex:partners ex:globex .
"""

# One rule, in the `rules.tsv` shape: a body of triple patterns and a head.
# Every variable in the head must occur in the body, or the engine would have to
# invent a term to bind it to and the table is refused.
EVERY_SUPPLIER_IS_COMPLIANT = RulePattern(
    name="every-supplier-is-compliant",
    body=(AtomPat("?s", TYPE, "<http://example.org/Supplier>"),),
    head=AtomPat("?s", TYPE, "<http://example.org/Compliant>"),
)


def show(title: str, report: dict) -> None:
    check = report["check"]
    print(f"\n{title}")
    print("-" * len(title))
    print(f"  asserted triples   {report['asserted_triples']}")
    print(f"  derived triples    {report['derived_triples']}")
    print(f"  fixpoint reached   {report['fixpoint_reached']}")
    print(f"  materialised       {report['materialized']}")
    print(f"  certificate        {report['certificate']['dir']}")
    print(f"  check status       {check['status']}")
    print(f"  checked            {check['checked']}")
    print(f"  verdict            {check['verdict']}")
    if check.get("theorem"):
        print(f"  theorem            {check['theorem']}")
        print(f"  rule digest        {check['rules_digest']}")
        print(f"  built-in digest    {check['builtin_rules_digest']}")
        print(f"  digests agree      {check['digests_agree']}")
        print(f"  means              {check['means']}")
    if check.get("warning"):
        print(f"  warning            {check['warning']}")


def main() -> None:
    out = Path(tempfile.mkdtemp(prefix="certified-reasoning-"))

    engine = OntologyEngine()
    engine.load(ONTOLOGY)
    before = engine.stats()["triples"]

    show("Run 1: the built-in table", engine.reason_horn(str(out / "builtin")))

    supplied = list(builtin_rules()) + [EVERY_SUPPLIER_IS_COMPLIANT]
    report = engine.reason_horn(str(out / "supplied"), rules=supplied)
    show("Run 2: the built-in table plus one rule of your own", report)

    compliant = [
        d
        for d in report["sample_derivations"]
        if d.endswith("<http://example.org/Compliant>")
    ]
    print(f"\n  the appended rule fired: {compliant}")
    print(
        "  that conclusion is true in every model of the graph THAT ALSO SATISFIES\n"
        "  your rule, and in no others. The rule was assumed and never checked."
    )

    after = engine.stats()["triples"]
    print(f"\nStore before {before} triples, after {after}. Nothing was materialised.")
    print(f"\nCertificates are in {out}. Check one by hand with:")
    print("  " + report["certificate"]["check_with"])
    print("\nFull report of run 2:")
    print(json.dumps(report, indent=2)[:1200] + "\n  ...")


if __name__ == "__main__":
    main()
