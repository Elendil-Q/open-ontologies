"""The Lean checker's verdict on certificates this package produced.

GATED on `oo-horn`. It skips loudly, naming the binary and how to build it,
because CI installs `[dev]` and nothing else: no elan, no `lake`. A green tick on
that job says the unchecked path is fine and says NOTHING about whether a single
certificate has ever been accepted, and pretending otherwise is the failure this
whole layer exists to prevent. Run `cd lean && lake build` and these run.

Four things are established here and nowhere else.

1. A certificate this Python engine wrote is ACCEPTED by the proved-sound checker
   and earns the absolute verdict, because the table it cites is the built-in one
   byte for byte.
2. A certificate over a table with one extra rule earns the RELATIVISED verdict
   instead, names a different theorem, and reports a different digest. The rule
   appended below says every supplier is compliant, which is true of nothing and
   checks green for ever; that is the point. If this test ever reports the
   absolute word, the layer has become a machine for turning an assumption into a
   fact with a proof attached.
3. Every forgery is REJECTED. A gate that cannot fail is decoration, so the
   certificates below are mutated five ways after being written, on top of the
   six committed fixtures, and each must come back rejected with no verdict.
4. A read or parse error is NOT a rejection. Exit 2 and exit 1 mean different
   things and are never folded together, because folding them is how an emitter
   bug gets mistaken for an uninstalled checker and never investigated.
"""


import shutil
import subprocess
from pathlib import Path

import pyoxigraph as ox
import pytest

from open_ontologies_lite import OntologyEngine
from open_ontologies_lite.horn.certify import CheckerUnavailable, check_horn, find_checker
from open_ontologies_lite.horn.reason import run_horn
from open_ontologies_lite.horn.rules import (
    AtomPat,
    RulePattern,
    builtin_rules,
    builtin_rules_bytes,
)

TYPE = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>"
SUPPLIER = "<http://ex.org/Supplier>"
COMPLIANT = "<http://ex.org/Compliant>"

ONT = """
@prefix ex: <http://ex.org/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
ex:A rdfs:subClassOf ex:B . ex:B rdfs:subClassOf ex:C .
ex:a a ex:A .
ex:acme a ex:Supplier .
ex:knows a owl:SymmetricProperty . ex:a ex:knows ex:b .
ex:p rdfs:domain ex:A ; rdfs:range ex:B . ex:x ex:p ex:y .
"""

EVERY_SUPPLIER_IS_COMPLIANT = RulePattern(
    name="every-supplier-is-compliant",
    body=(AtomPat("?s", TYPE, SUPPLIER),),
    head=AtomPat("?s", TYPE, COMPLIANT),
)


def _checker() -> Path:
    try:
        return find_checker("oo-horn")
    except CheckerUnavailable as exc:
        pytest.skip(str(exc))


def _store() -> ox.Store:
    s = ox.Store()
    s.load(ONT.encode("utf-8"), format=ox.RdfFormat.TURTLE)
    return s


def _fixtures() -> Path:
    d = Path(__file__).resolve().parents[2] / "tests" / "fixtures" / "horn"
    if not d.is_dir():
        pytest.skip(f"not in a repository checkout: {d} is absent")
    return d


def test_the_built_in_table_earns_the_absolute_verdict(tmp_path):
    """THE test. A certificate produced by the PYTHON reasoner, accepted by the
    LEAN checker, over the table `Builtin.asHorn_sound` discharges."""
    _checker()
    result = run_horn(_store(), certificate_dir=tmp_path)
    assert result.derived_triples > 0
    outcome = check_horn(tmp_path)
    assert outcome["status"] == "accepted"
    assert outcome["checked"] is True
    assert outcome["verdict"] == "entailed"
    assert outcome["theorem"] == "OOCert.entails_of_builtin_horn"
    assert outcome["digests_agree"] is True
    assert outcome["vacuous"] is False
    assert outcome["derivations"] == result.derived_triples
    assert "consistency_warning" not in outcome


def test_a_user_rule_never_earns_the_absolute_verdict(tmp_path):
    """The Python mirror of `tests/lean_horn_certificate_test.rs`' test of the
    same name. The table is the built-ins PLUS ONE ROW, which is still not the
    built-in table, and the rule it adds is false of the world."""
    _checker()
    table = list(builtin_rules()) + [EVERY_SUPPLIER_IS_COMPLIANT]
    result = run_horn(_store(), table, certificate_dir=tmp_path)
    assert any(
        conclusion[2] == COMPLIANT for conclusion in result.derived()
    ), "the appended rule must actually fire, or this proves nothing"
    outcome = check_horn(tmp_path)
    assert outcome["status"] == "accepted"
    assert outcome["verdict"] == "entailed_under_supplied_rules"
    assert outcome["theorem"] == "OOCert.horn_certificate_sound"
    assert "assumed, not checked" in outcome["means"]
    assert outcome["digests_agree"] is False
    assert outcome["rules_digest"] != outcome["builtin_rules_digest"]


def test_dropping_one_built_in_rule_also_loses_the_absolute_verdict(tmp_path):
    """A SUBSET of the built-ins is not the built-in table either. `HMain.lean`
    compares the whole rendering in order, so this is a full equality and not a
    containment, and a user who prunes the table for speed must be told."""
    _checker()
    table = list(builtin_rules())[:10]
    run_horn(_store(), table, certificate_dir=tmp_path)
    outcome = check_horn(tmp_path)
    assert outcome["status"] == "accepted"
    assert outcome["verdict"] == "entailed_under_supplied_rules"
    assert outcome["digests_agree"] is False


def test_a_certificate_with_no_derivations_is_reported_as_vacuous(tmp_path):
    """An empty `horn.tsv` is accepted with the absolute verdict and zero
    derivations, and the checker is right: vacuously, every step in an empty list
    holds. The Python report would be what was wrong, so the count travels beside
    the verdict and `vacuous` says so in one word."""
    _checker()
    empty = ox.Store()
    result = run_horn(empty, certificate_dir=tmp_path)
    assert result.derived_triples == 0
    outcome = check_horn(tmp_path)
    assert outcome["status"] == "accepted"
    assert outcome["vacuous"] is True
    assert outcome["derivations"] == 0


def test_every_committed_forgery_fixture_is_rejected():
    """The six certificates in `tests/fixtures/horn/` are the repository's own
    adversarial cases: a wrong conclusion, a rule index off the end of the table,
    a premise that was never asserted, a step citing its own conclusion, and a
    binding that does not instantiate the body."""
    _checker()
    fixtures = _fixtures()
    for bad in (
        "bad_conclusion",
        "bad_index",
        "bad_premise",
        "bad_self",
        "bad_binding",
    ):
        outcome = _check_files(
            fixtures / "builtin_rules.tsv",
            fixtures / "asserted.tsv",
            fixtures / f"{bad}.tsv",
        )
        assert outcome["status"] == "rejected", f"{bad} was not rejected"
        assert outcome["checked"] is True
        assert outcome["verdict"] is None
        assert "establishes nothing" in outcome["means"]


def test_a_rule_index_past_a_short_table_is_rejected():
    """`short_rules.tsv` holds three rules and `good.tsv` cites index 4. The same
    certificate is accepted against the full table, so this isolates the index
    check rather than testing the certificate."""
    _checker()
    fixtures = _fixtures()
    short = _check_files(
        fixtures / "short_rules.tsv", fixtures / "asserted.tsv", fixtures / "good.tsv"
    )
    assert short["status"] == "rejected"
    full = _check_files(
        fixtures / "builtin_rules.tsv", fixtures / "asserted.tsv", fixtures / "good.tsv"
    )
    assert full["status"] == "accepted"


MUTATIONS = {
    # Each rewrites one field of a freshly emitted, freshly accepted certificate.
    "a forged conclusion": lambda f: _swap(f, 5, "<http://ex.org/FORGED>"),
    "a premise that was never asserted": lambda f: _swap(f, 8, "<http://ex.org/ghost>"),
    "a rule index off the end of the table": lambda f: _swap(f, 0, "99"),
    "a binding that does not instantiate the body": lambda f: _swap(
        f, 3, "<http://ex.org/WRONG>"
    ),
    "a binding variable that kept its question mark": lambda f: _swap(
        f, 2, "?" + f[2]
    ),
}


def test_every_mutation_of_an_accepted_certificate_is_rejected(tmp_path):
    """The fixtures above are static. These mutate a certificate this engine
    produced MOMENTS AGO and that the checker has just accepted, which is the
    only way to be sure the acceptance was not an accident of the fixture."""
    _checker()
    run_horn(_store(), certificate_dir=tmp_path)
    assert check_horn(tmp_path)["status"] == "accepted"
    original = (tmp_path / "horn.tsv").read_text("utf-8")
    first, rest = original.split("\n", 1)

    for label, mutate in MUTATIONS.items():
        fields = first.split("\t")
        (tmp_path / "horn.tsv").write_text(
            "\t".join(mutate(fields)) + "\n" + rest, encoding="utf-8"
        )
        outcome = check_horn(tmp_path)
        assert outcome["status"] == "rejected", f"{label} was not rejected"
        assert outcome["verdict"] is None
        assert outcome["checked"] is True
    (tmp_path / "horn.tsv").write_text(original, encoding="utf-8")


def test_a_step_that_cites_its_own_conclusion_is_rejected(tmp_path):
    """Structurally impossible for this engine to emit, because `known` is only
    mutated at the end of a round. Forged by hand here so the property is tested
    and not merely argued."""
    _checker()
    run_horn(_store(), certificate_dir=tmp_path)
    lines = (tmp_path / "horn.tsv").read_text("utf-8").split("\n")[:-1]
    fields = lines[0].split("\t")
    binds = int(fields[1])
    conclusion_at = 2 + 2 * binds
    conclusion = fields[conclusion_at : conclusion_at + 3]
    # Replace the first premise with the step's own conclusion.
    fields[conclusion_at + 3 : conclusion_at + 6] = conclusion
    (tmp_path / "horn.tsv").write_text(
        "\n".join(["\t".join(fields)] + lines[1:]) + "\n", encoding="utf-8"
    )
    outcome = check_horn(tmp_path)
    assert outcome["status"] == "rejected"
    assert outcome["verdict"] is None


def test_an_unreadable_file_is_not_a_rejection(tmp_path):
    """Exit 2 against exit 1. A missing or unparseable file means the checker
    could not read what it was given; it does not mean a step was rejected, and
    the two must never share a status word."""
    _checker()
    run_horn(_store(), certificate_dir=tmp_path)
    (tmp_path / "horn.tsv").unlink()
    outcome = check_horn(tmp_path)
    assert outcome["status"] == "unreadable"
    assert outcome["checked"] is False
    assert outcome["verdict"] is None
    assert "cannot read" in outcome["error"]
    assert "exit 2" in outcome["means"]


def test_the_engine_raises_when_the_checker_cannot_read_what_it_just_wrote(
    tmp_path, monkeypatch
):
    """`check_horn` is a library primitive over a directory it did not
    necessarily write, so it returns the negative in the package's
    `ValidationResult(ok=False, error=...)` idiom. `reason_horn` wrote the three
    files itself, so the same outcome is an emitter bug and must stop the run
    rather than be reported as one more unchecked state.

    The unreadable outcome is injected, because an emitter that can produce one
    on demand is a bug this suite would rather not have. The injected value is
    the real thing: `check_horn` against a certificate with a mangled
    `asserted.tsv`, produced a few lines above."""
    from open_ontologies_lite import CertificateUnreadable
    from open_ontologies_lite.horn import certify

    _checker()
    engine = OntologyEngine()
    engine.load(ONT, "turtle")
    engine.reason_horn(str(tmp_path / "real"), check=False)
    (tmp_path / "real" / "asserted.tsv").write_text(
        "not\ta\ttriple\tat\tall\n", encoding="utf-8"
    )
    genuine = check_horn(tmp_path / "real")
    assert genuine["status"] == "unreadable"

    monkeypatch.setattr(certify, "check_horn", lambda *a, **k: genuine)
    with pytest.raises(CertificateUnreadable, match="emitter"):
        engine.reason_horn(str(tmp_path / "again"))


def test_a_malformed_rule_table_is_unreadable_and_not_a_rejection(tmp_path):
    _checker()
    run_horn(_store(), certificate_dir=tmp_path)
    (tmp_path / "rules.tsv").write_text("garbage\tnotanumber\n", encoding="utf-8")
    outcome = check_horn(tmp_path)
    assert outcome["status"] == "unreadable"
    assert outcome["verdict"] is None


def test_the_vendored_table_is_what_oo_horn_prints():
    """A drifted copy can only weaken a verdict from the absolute one to the
    relativised one, which is the safe direction and also a silent one. This
    FAILS rather than skips, because a silent weakening is precisely the thing a
    skip would let through."""
    checker = _checker()
    proc = subprocess.run([str(checker), "rules"], capture_output=True)
    assert proc.returncode == 0, proc.stderr.decode()
    assert proc.stdout == builtin_rules_bytes(), (
        "the vendored tables/builtin_rules.tsv has drifted from what oo-horn prints. "
        "Every run over the built-in table now earns the relativised verdict instead "
        "of the absolute one, silently. Re-copy tests/fixtures/horn/builtin_rules.tsv"
    )


def test_the_environment_variable_points_at_the_checker(tmp_path, monkeypatch):
    """`OO_HORN` is the documented escape hatch, and the warning text tells users
    to set it, so it had better work."""
    checker = _checker()
    staged = tmp_path / "oo-horn"
    shutil.copy2(checker, staged)
    monkeypatch.setenv("OO_HORN", str(staged))
    assert find_checker("oo-horn") == staged
    monkeypatch.setenv("OO_HORN", str(tmp_path / "absent"))
    # A missing environment binary falls through to the repo and PATH, matching
    # the Rust precedent; an explicit path does not.
    assert find_checker("oo-horn") == checker


def _check_files(rules: Path, asserted: Path, horn: Path) -> dict:
    """Check three files that do not share a directory, by staging them."""
    import tempfile

    with tempfile.TemporaryDirectory() as d:
        shutil.copy2(rules, Path(d) / "rules.tsv")
        shutil.copy2(asserted, Path(d) / "asserted.tsv")
        shutil.copy2(horn, Path(d) / "horn.tsv")
        return check_horn(d)


def _swap(fields: list[str], index: int, value: str) -> list[str]:
    out = list(fields)
    out[index] = value
    return out
