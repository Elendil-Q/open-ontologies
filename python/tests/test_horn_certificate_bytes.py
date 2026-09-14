"""The certificate format is a field-position format, so this is the forgery test.

CI has no Lean binary. Everything the Lean checker would catch about a MALFORMED
certificate therefore has to be caught here, and this file is where the format is
held to its contract byte by byte.

The Lean parsers do nothing but split on tab and newline and read the fields off
by position. There is no quoting layer and no escape pass. A raw tab inside a
bound term shifts every later field of a `horn.tsv` line by one: `rest.take (2*k)`
grabs the wrong fields, the conclusion is read from the wrong positions, and the
checker verifies something that is not what the engine derived. A serialiser that
gets that wrong is not a cosmetic bug, it is a place where a derivation step can
be forged, so the store below is built deliberately full of terms that would
break a naive emitter: a literal with a real tab, a real newline, a real carriage
return, a quote, a backslash, a language tag and a datatype.

The last test in the file is the one that no amount of inspecting the certificate
could replace. An emitter that wrote `.value` instead of `str()` produces a
certificate that is internally CONSISTENT: every line has the right field count,
every premise matches its rule, and `oo-horn` accepts it and reports the absolute
verdict about a graph that is not the graph anyone loaded. The only way to catch
it is to parse `asserted.tsv` back into terms and compare with the store.
"""

import pyoxigraph as ox
import pytest

from open_ontologies_lite.horn.reason import run_horn
from open_ontologies_lite.horn.rules import builtin_rules
from open_ontologies_lite.horn.terms import CertificateFieldError, spell

NASTY = """
@prefix ex:   <http://ex.org/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .

ex:A rdfs:subClassOf ex:B .
ex:B rdfs:subClassOf ex:C .
ex:a a ex:A .
ex:label   rdfs:domain ex:A ; rdfs:range ex:Text .
ex:a ex:label "tab\\there and nl\\nhere and cr\\rhere and quote\\"here and bs\\\\here" .
ex:a ex:label "lang tagged"@en-GB .
ex:a ex:label "42"^^xsd:integer .
_:blank a ex:A .
"""


def _load():
    store = ox.Store()
    store.load(NASTY.encode("utf-8"), format=ox.RdfFormat.TURTLE)
    return store


def test_every_line_of_every_file_splits_into_the_field_count_the_parser_expects(tmp_path):
    result = run_horn(_load(), certificate_dir=tmp_path)
    table = builtin_rules()

    rules_lines = (tmp_path / "rules.tsv").read_text("utf-8").split("\n")[:-1]
    assert len(rules_lines) == len(table)
    for line, rule in zip(rules_lines, table):
        fields = line.split("\t")
        assert fields[1] == str(len(rule.body))
        assert len(fields) - 2 == 3 * len(rule.body) + 3

    for line in (tmp_path / "asserted.tsv").read_text("utf-8").split("\n")[:-1]:
        assert len(line.split("\t")) == 3

    horn_lines = (tmp_path / "horn.tsv").read_text("utf-8").split("\n")[:-1]
    assert len(horn_lines) == result.derived_triples
    for line in horn_lines:
        fields = line.split("\t")
        index, binds = int(fields[0]), int(fields[1])
        rest = fields[2:]
        # This is `parseHornSteps`' arithmetic: 2*k binding fields, then a
        # conclusion, then whole triples for the body of the cited rule.
        assert len(rest) == 2 * binds + 3 + 3 * len(table[index].body)


def test_no_field_anywhere_carries_a_separator(tmp_path):
    run_horn(_load(), certificate_dir=tmp_path)
    for name in ("rules.tsv", "asserted.tsv", "horn.tsv"):
        raw = (tmp_path / name).read_bytes()
        assert b"\r" not in raw, f"{name} carries a CR; HornParse splits on LF alone"
        assert raw == b"" or raw.endswith(b"\n"), f"{name} does not end with a newline"
        for line in raw.decode("utf-8").split("\n")[:-1]:
            for field in line.split("\t"):
                assert "\t" not in field and "\n" not in field and "\r" not in field


def test_binding_variables_are_written_bare_with_no_question_mark(tmp_path):
    """`rules.tsv` spells `?x` and `horn.tsv` spells `x`, because `patOf` strips
    the '?' when it parses the rule and `substOf` looks the bare name up. Getting
    this wrong is exit 1 with a rejection JSON that names nothing at all: no
    diagnostic, no first-rejected index. It is the likeliest emitter bug and the
    one with the worst debugging experience, so it gets its own test."""
    run_horn(_load(), certificate_dir=tmp_path)
    for line in (tmp_path / "horn.tsv").read_text("utf-8").split("\n")[:-1]:
        fields = line.split("\t")
        binds = int(fields[1])
        for i in range(binds):
            var = fields[2 + 2 * i]
            assert not var.startswith("?"), f"binding variable {var!r} carries a '?'"
            assert var != ""


def test_each_step_cites_its_rule_body_instantiated_in_body_order(tmp_path):
    """`checkHornStep` demands `st.premises = r.body.map (inst)`: the DECLARED
    body order, exactly. The engine is free to JOIN the atoms in any order it
    likes, and does, so this is the assertion that keeps the two apart. A
    certificate with the right triples in the wrong order is rejected."""
    result = run_horn(_load(), certificate_dir=tmp_path)
    table = builtin_rules()
    assert result.derived_triples > 0
    for step in result.steps:
        rule = table[step.rule]
        env = dict(step.binds)
        expected = tuple(
            tuple(env[f[1:]] if f.startswith("?") else f for f in atom.fields())
            for atom in rule.body
        )
        assert step.premises == expected
        head = rule.head
        assert step.conclusion == tuple(
            env[f[1:]] if f.startswith("?") else f for f in head.fields()
        )


def test_every_premise_was_asserted_or_concluded_on_an_earlier_line(tmp_path):
    """`checkHornAll`'s requirement, and the reason a step cannot cite itself.
    Asserting it here means the property is tested even where Lean cannot run."""
    result = run_horn(_load(), certificate_dir=tmp_path)
    known = {
        tuple(line.split("\t"))
        for line in (tmp_path / "asserted.tsv").read_text("utf-8").split("\n")[:-1]
    }
    for step in result.steps:
        for premise in step.premises:
            assert premise in known, f"{premise} is cited before it is known"
        assert step.conclusion not in known, "a step re-derives something already known"
        known.add(step.conclusion)


def test_the_asserted_file_reparses_into_exactly_the_graph_that_was_loaded(tmp_path):
    """The `.value` disaster, and nothing that only inspects the certificate can
    catch it. An emitter using the unquoted lexical form writes a certificate
    that is internally consistent and that `oo-horn` ACCEPTS, reporting the
    absolute verdict about a graph nobody loaded."""
    store = _load()
    run_horn(store, certificate_dir=tmp_path)
    text = (tmp_path / "asserted.tsv").read_text("utf-8")
    ntriples = "".join(
        line.replace("\t", " ") + " .\n" for line in text.split("\n")[:-1]
    )
    reparsed = {
        (str(t.subject), str(t.predicate), str(t.object))
        for t in ox.parse(ntriples.encode("utf-8"), format=ox.RdfFormat.N_TRIPLES)
    }
    loaded = {
        (str(q.subject), str(q.predicate), str(q.object))
        for q in store.quads_for_pattern(None, None, None, ox.DefaultGraph())
    }
    # Blank-node labels are scoped to a parse, so compare the shape of each
    # triple with blank labels normalised away rather than the labels themselves.
    def norm(triples):
        return sorted(
            tuple("_:_" if t.startswith("_:") else t for t in triple)
            for triple in triples
        )

    assert norm(reparsed) == norm(loaded)


def test_the_field_guard_refuses_a_term_carrying_a_tab():
    """pyoxigraph will never trip this: its N-Triples spelling escapes tab,
    newline and CR, and NamedNode refuses a tab outright. An untested guard is a
    guard someone deletes, so it is driven here by a hand-built fake term."""

    class ForgedTerm:
        def __str__(self):
            return '<http://ex.org/a>\t<http://ex.org/p>\t"forged"'

    with pytest.raises(CertificateFieldError, match="separator"):
        spell(ForgedTerm(), "subject")


def test_spell_refuses_a_string_because_a_spelling_is_not_a_term():
    """`.value` returns a str, and so does every display path in engine.py. The
    type refusal is what stops that code being reused on this path."""
    with pytest.raises(TypeError, match="not a str"):
        spell("http://ex.org/a", "subject")


def test_a_literal_in_subject_position_is_refused_rather_than_written(tmp_path):
    """`eq-sym` over an owl:sameAs whose subject is a literal instantiates a head
    no serialiser can write. Lean would certify the step, because it compares
    strings and has no RDF well-formedness notion. Refusing derives LESS, which
    is the sound direction, and the count says so out loud."""
    store = ox.Store()
    store.load(
        b'<http://ex.org/a> <http://www.w3.org/2002/07/owl#sameAs> "a literal" .',
        format=ox.RdfFormat.N_TRIPLES,
    )
    result = run_horn(store, certificate_dir=tmp_path)
    assert result.skipped_unserialisable == 1
    assert result.derived_triples == 0
    assert result.skipped_examples
    assert (tmp_path / "horn.tsv").read_bytes() == b""


def test_an_rdf_star_quoted_triple_is_carried_and_counted_not_dropped(tmp_path):
    """Measured against pyoxigraph 0.5.9 and 0.5.11, and pinned because the
    behaviour decides the shape of the serialisability guard.

    A quoted triple is accepted in OBJECT position only; `Quad` refuses one in
    subject or predicate position outright. Its `str()` is `<s> <p> "v"` with RAW
    SPACES, and NOT the `<<( ... )>>` spelling, so a guard keyed on a `<<` prefix
    would be checking for something these versions never produce while a bare
    `<`-prefix test would admit the space-separated spelling as a predicate.

    Carrying it is the right call: it contains no separator, so it occupies one
    field, the checker treats it as an opaque name and soundness is unaffected.
    Dropping it would silently remove an assertion. What it does cost is that
    `asserted.tsv` stops being re-parsable as N-Triples, which is why the count
    and the note exist.
    """
    quoted = ox.Triple(
        ox.NamedNode("http://ex.org/a"),
        ox.NamedNode("http://ex.org/p"),
        ox.Literal("v"),
    )
    with pytest.raises(TypeError):
        ox.Quad(quoted, ox.NamedNode("http://ex.org/q"), ox.NamedNode("http://ex.org/c"))
    with pytest.raises(TypeError):
        ox.Quad(ox.NamedNode("http://ex.org/a"), quoted, ox.NamedNode("http://ex.org/c"))

    store = ox.Store()
    store.add(ox.Quad(ox.NamedNode("http://ex.org/a"), ox.NamedNode("http://ex.org/q"), quoted))
    store.load(
        b"<http://ex.org/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> "
        b"<http://ex.org/A> .\n"
        b"<http://ex.org/A> <http://www.w3.org/2000/01/rdf-schema#subClassOf> "
        b"<http://ex.org/B> .",
        format=ox.RdfFormat.N_TRIPLES,
    )
    result = run_horn(store, certificate_dir=tmp_path)
    report = result.to_dict()
    assert report["quoted_triples"] == 1
    assert "no longer re-parsable as N-Triples" in report["quoted_triples_note"]
    assert " " in str(quoted) and not str(quoted).startswith("<<")
    # The term is carried, in one field, with no separator in it.
    lines = (tmp_path / "asserted.tsv").read_text("utf-8").split("\n")[:-1]
    carried = [line for line in lines if line.endswith(str(quoted))]
    assert len(carried) == 1
    assert len(carried[0].split("\t")) == 3
    # And the rest of the run is unaffected.
    assert result.derived_triples == 1


def test_a_non_atomic_term_can_never_reach_predicate_position():
    from open_ontologies_lite.horn.reason import _serialisable, is_atomic_term

    spelling = '<http://ex.org/a> <http://ex.org/p> "v"'
    assert not is_atomic_term(spelling)
    assert not _serialisable("<http://ex.org/s>", spelling)
    assert not _serialisable("<http://ex.org/s>", "<<(x)>>")
    assert _serialisable("<http://ex.org/s>", "<http://ex.org/p>")
    assert not _serialisable('"a literal"', "<http://ex.org/p>")
    assert _serialisable("_:b0", "<http://ex.org/p>")
