"""The rule table is data, and every refusal in the parser is load-bearing.

Runs with no Lean binary, so it runs in CI. A rule's identity in a certificate is
its INDEX into this table, never its name: `scm-eqc1` occupies rows 11 and 12 and
`scm-eqp1` rows 13 and 14, because each licenses two conclusions. Pinning the
whole table in order is how a reordering that silently repoints every certificate
in the wild gets caught, and it is why nothing in this package keeps a
name-to-index map.

The refusals below go beyond what the Lean parser rejects. That asymmetry is
correct: Lean only has to CHECK a binding, while this side has to PRODUCE one, so
a rule the checker would happily accept can still be one this engine has nothing
to bind. Refusing is the only honest option, and each refusal names the line and
what was wrong rather than guessing.
"""

from pathlib import Path

import pytest

from open_ontologies_lite.horn.rules import (
    AtomPat,
    RulePattern,
    RuleTableError,
    builtin_rules,
    builtin_rules_bytes,
    parse_rules,
    rules_tsv,
    vars_of,
)

SUBCLASS_OF = "<http://www.w3.org/2000/01/rdf-schema#subClassOf>"
TYPE = "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>"

# (index, name, body length), the whole table, in order.
EXPECTED_TABLE = [
    (0, "rdfs2", 2),
    (1, "rdfs3", 2),
    (2, "rdfs5", 2),
    (3, "rdfs7", 2),
    (4, "rdfs9", 2),
    (5, "rdfs11", 2),
    (6, "prp-trp", 3),
    (7, "prp-symp", 2),
    (8, "prp-inv1", 2),
    (9, "prp-inv2", 2),
    (10, "eq-sym", 1),
    (11, "scm-eqc1", 1),
    (12, "scm-eqc1", 1),
    (13, "scm-eqp1", 1),
    (14, "scm-eqp1", 1),
    (15, "cls-svf1", 4),
    (16, "cls-avf", 4),
    (17, "cls-hv1", 3),
    (18, "cls-hv2", 3),
    (19, "scm-svf1", 5),
    (20, "scm-svf2", 5),
    (21, "scm-avf1", 5),
    (22, "scm-avf2", 5),
    (23, "scm-dom1", 2),
    (24, "scm-dom2", 2),
    (25, "scm-rng1", 2),
    (26, "scm-rng2", 2),
]


def test_the_builtin_table_has_twenty_seven_rows_in_this_order():
    table = builtin_rules()
    assert len(table) == 27
    got = [(i, r.name, len(r.body)) for i, r in enumerate(table)]
    assert got == EXPECTED_TABLE


def test_the_two_double_rows_license_opposite_conclusions():
    """`scm-eqc1` and `scm-eqp1` are two rows each, and the second is the
    converse of the first. A name-keyed map would keep one and lose the other,
    and every certificate citing the lost index would then be checked against
    the wrong rule."""
    table = builtin_rules()
    assert table[11].head.fields() == ("?a", SUBCLASS_OF, "?b")
    assert table[12].head.fields() == ("?b", SUBCLASS_OF, "?a")
    assert table[13].head != table[14].head


def test_scm_avf2_head_is_reversed():
    """`lean/OOCert/Rules.lean:47` records that the natural way round is
    unsound: from `?c1 allValuesFrom ?y` and `?p1 subPropertyOf ?p2` the
    subclass runs `?c2 subClassOf ?c1`, not the other way. Pinning it here
    means a "tidy-up" that flips it fails in Python before it reaches Lean."""
    rule = builtin_rules()[22]
    assert rule.name == "scm-avf2"
    assert rule.head.fields() == ("?c2", SUBCLASS_OF, "?c1")


def test_rendering_the_builtin_table_reproduces_its_bytes():
    """The emitter writes the vendored bytes verbatim, so this is not what makes
    the absolute verdict safe; it is what proves the renderer would have been
    safe too, which is the precondition for rendering a table a user supplied."""
    raw = builtin_rules_bytes()
    assert rules_tsv(parse_rules(raw.decode("utf-8"))).encode("utf-8") == raw


def test_the_vendored_table_matches_the_repo_fixture():
    fixture = Path(__file__).resolve().parents[2] / "tests" / "fixtures" / "horn" / "builtin_rules.tsv"
    if not fixture.is_file():
        pytest.skip(f"not in a repository checkout: {fixture} is absent")
    assert builtin_rules_bytes() == fixture.read_bytes()


def test_the_vendored_table_has_no_carriage_return_and_ends_with_a_newline():
    raw = builtin_rules_bytes()
    assert b"\r" not in raw
    assert raw.endswith(b"\n")


def test_variables_are_listed_in_first_occurrence_order():
    """The binding list in horn.tsv is written in this order, matching the Rust
    emitter so a human can diff the two certificates."""
    rule = builtin_rules()[4]  # rdfs9: ?x type ?a . ?a subClassOf ?b -> ?x type ?b
    assert vars_of(rule.atoms()) == ["x", "a", "b"]


def test_a_carriage_return_is_refused_rather_than_stripped():
    line = f"r\t1\t?a\t{SUBCLASS_OF}\t?b\t?a\t{SUBCLASS_OF}\t?b\r\n"
    with pytest.raises(RuleTableError, match="carriage return"):
        parse_rules(line)


def test_a_constant_that_is_not_an_ntriples_term_is_refused():
    """A constant in any other spelling can never equal a term the store holds,
    so the rule silently never fires. That is a typo, not a rule."""
    line = f"r\t1\t?a\trdfs:subClassOf\t?b\t?a\t{SUBCLASS_OF}\t?b\n"
    with pytest.raises(RuleTableError, match="N-Triples term"):
        parse_rules(line)


def test_a_bare_question_mark_is_refused():
    line = f"r\t1\t?\t{SUBCLASS_OF}\t?b\t?b\t{SUBCLASS_OF}\t?b\n"
    with pytest.raises(RuleTableError, match="no variable name"):
        parse_rules(line)


def test_a_head_variable_that_is_not_in_the_body_is_refused():
    line = f"r\t1\t?a\t{SUBCLASS_OF}\t?b\t?a\t{SUBCLASS_OF}\t?zzz\n"
    with pytest.raises(RuleTableError, match="does not occur in the body"):
        parse_rules(line)


def test_a_wrong_field_count_is_refused():
    with pytest.raises(RuleTableError, match="pattern fields"):
        parse_rules(f"r\t2\t?a\t{SUBCLASS_OF}\t?b\t?a\t{SUBCLASS_OF}\t?b\n")


def test_a_non_ascii_digit_body_length_is_refused():
    """`str.isdigit()` is true of '٣' and int() accepts it, so a body length
    Lean's `toNat?` would reject could otherwise be read here."""
    with pytest.raises(RuleTableError, match="not a decimal number"):
        parse_rules(f"r\t٣\t?a\t{SUBCLASS_OF}\t?b\t?a\t{SUBCLASS_OF}\t?b\n")


def test_an_empty_rule_name_is_refused():
    with pytest.raises(RuleTableError, match="name is empty"):
        parse_rules(f"\t1\t?a\t{SUBCLASS_OF}\t?b\t?a\t{SUBCLASS_OF}\t?b\n")


def test_a_tab_in_a_programmatically_built_rule_name_is_refused_on_the_way_out():
    """No parsed table can carry this, because the line was already split on tab.
    A caller building a RulePattern in Python can, and a tab in a rule name would
    shift every field of that line by one."""
    rule = RulePattern(
        name="bad\tname",
        body=(AtomPat("?a", SUBCLASS_OF, "?b"),),
        head=AtomPat("?a", TYPE, "?b"),
    )
    with pytest.raises(ValueError, match="separator"):
        rules_tsv([rule])


def test_blank_lines_and_a_trailing_newline_are_accepted():
    """`HornParse.parseRules` skips empty lines, so this parser must too or a
    file the checker reads happily would be refused here."""
    body = f"r\t1\t?a\t{SUBCLASS_OF}\t?b\t?a\t{SUBCLASS_OF}\t?b\n"
    assert len(parse_rules(body + "\n" + body)) == 2


def test_the_vendored_table_is_tracked_by_git_and_not_ignored():
    """The wheel is built from the FILESYSTEM and the repository is shared from
    GIT, so a data file that is present locally and ignored by git produces a
    working wheel on the machine that wrote it and a BROKEN one from a fresh
    clone or from CI, failing with FileNotFoundError on the first call to
    `builtin_rules()`.

    That is not hypothetical here. The root `.gitignore` carries `data/` with no
    leading slash, which matches a directory of that name at ANY depth, and it
    already carries four negation entries for the same collision under
    `case-studies/`. The directory holding this table is called `tables` for that
    reason, and this test is what keeps it that way: renaming it back to `data`
    fails here rather than three weeks later in someone else's checkout.

    The file is LOCATED BY SEARCHING and then CONFIRMED to be the one the code
    reads, rather than reconstructed from a path spelled here. A reconstructed
    path that no longer exists makes `git check-ignore` report "not ignored",
    which is a vacuous pass: the first version of this test did exactly that and
    passed against the very layout it was written to reject.
    """
    import shutil
    import subprocess

    import open_ontologies_lite.horn as horn

    if shutil.which("git") is None:
        pytest.skip("git is not on PATH")
    repo = Path(__file__).resolve().parents[2]
    if not (repo / ".git").exists():
        pytest.skip("not in a git checkout")

    found = sorted(Path(horn.__file__).parent.rglob("builtin_rules.tsv"))
    assert len(found) == 1, f"expected exactly one vendored table, found {found}"
    table = found[0]
    assert table.read_bytes() == builtin_rules_bytes(), (
        "the file found on disk is not the one importlib.resources reads, so this "
        "test would be checking the wrong path"
    )

    ignored = subprocess.run(
        ["git", "check-ignore", str(table)], cwd=repo, capture_output=True, text=True
    )
    assert ignored.returncode != 0, (
        f"{table} is ignored by git, so it will not be in a fresh clone and every "
        f"wheel built from one ships without the built-in rule table:\n{ignored.stdout}"
    )
