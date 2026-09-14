"""No verdict word may appear as an executable string anywhere in this package.

This is the gate. If either verdict word is ever assigned, defaulted, compared or
formatted in Python, the verdict is being synthesised here and the work is wrong
regardless of what every other test in the suite says.

The scan is over the ABSTRACT SYNTAX TREE and not over grep output, and the
distinction is the whole design. A grep-based rule would have to forbid the word
everywhere, which is impossible and also wrong: `onto_reason`'s docstring and
`horn/__init__.py` have to TEACH the reader what `entailed_under_supplied_rules`
means, and a docstring that cannot name the thing it is warning about is useless.
An AST scan separates the two cleanly. Docstrings are exempt by construction,
comments never reach the tree at all, and every other string constant, f-string
fragment included, is forbidden. The word `entailed` is the whole test, because
the relativised verdict contains it.

The second half of the file pins the module split. `reason.py` must run with no
checker installed and `certify.py` must be usable against a certificate this
package did not write, so neither may import the other. That is what makes "works
with no binary" structural rather than a promise, and an import added in a hurry
is exactly how such a property is lost.
"""

import ast
from pathlib import Path

import open_ontologies_lite

PACKAGE = Path(open_ontologies_lite.__file__).parent
FORBIDDEN = "entailed"


def _python_files():
    return sorted(p for p in PACKAGE.rglob("*.py") if "__pycache__" not in p.parts)


def _docstring_ids(tree: ast.AST) -> set[int]:
    """Identity of every node that is a docstring: the first statement of a
    module, class or function when it is a bare string."""
    out: set[int] = set()
    for node in ast.walk(tree):
        if isinstance(
            node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)
        ):
            body = getattr(node, "body", None)
            if not body:
                continue
            first = body[0]
            if (
                isinstance(first, ast.Expr)
                and isinstance(first.value, ast.Constant)
                and isinstance(first.value.value, str)
            ):
                out.add(id(first.value))
    return out


def test_no_module_writes_a_verdict_word_outside_a_docstring():
    offenders = []
    for path in _python_files():
        tree = ast.parse(path.read_text("utf-8"), filename=str(path))
        exempt = _docstring_ids(tree)
        for node in ast.walk(tree):
            if (
                isinstance(node, ast.Constant)
                and isinstance(node.value, str)
                and id(node) not in exempt
                and FORBIDDEN in node.value
            ):
                offenders.append(
                    f"{path.relative_to(PACKAGE)}:{node.lineno}: {node.value[:80]!r}"
                )
    assert offenders == [], (
        "a verdict word appears as an executable string, so the verdict is being "
        "decided in Python rather than copied from the checker:\n" + "\n".join(offenders)
    )


def test_the_scan_would_catch_a_verdict_word_if_one_were_added():
    """A gate that cannot fail is decoration. This runs the same scan over a
    source file that does synthesise a verdict, and requires it to be caught."""
    source = (
        '"""A docstring may say entailed, and must not be flagged."""\n'
        "def f(ok):\n"
        '    """Nor may this docstring be flagged when it says entailed."""\n'
        '    return "entailed" if ok else None\n'
    )
    tree = ast.parse(source)
    exempt = _docstring_ids(tree)
    caught = [
        node.value
        for node in ast.walk(tree)
        if isinstance(node, ast.Constant)
        and isinstance(node.value, str)
        and id(node) not in exempt
        and FORBIDDEN in node.value
    ]
    assert caught == ["entailed"]


def test_an_fstring_fragment_is_not_a_hiding_place():
    """`JoinedStr` holds `Constant` nodes, so splicing the word into an f-string
    is caught by the same walk. Pinned because it is the obvious way round."""
    tree = ast.parse('def f(x):\n    return f"the run is {x} entailed"\n')
    caught = [
        node.value
        for node in ast.walk(tree)
        if isinstance(node, ast.Constant)
        and isinstance(node.value, str)
        and FORBIDDEN in node.value
    ]
    assert caught != []


def _imports(path: Path) -> set[str]:
    tree = ast.parse(path.read_text("utf-8"), filename=str(path))
    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module:
            names.add(node.module)
        elif isinstance(node, ast.Import):
            names.update(a.name for a in node.names)
    return names


def test_the_reasoner_never_imports_the_checker_bridge():
    """`reason.py` must run with nothing installed but pyoxigraph."""
    assert not any("certify" in m for m in _imports(PACKAGE / "horn" / "reason.py"))


def test_the_checker_bridge_never_imports_the_reasoner():
    """`certify.py` is standard library only and must be usable against a
    certificate directory this package did not write."""
    assert not any("reason" in m for m in _imports(PACKAGE / "horn" / "certify.py"))


def test_the_rule_table_module_needs_no_triple_store():
    """A rule table is text. Keeping pyoxigraph out of `rules.py` is what lets
    the table be parsed, rendered and tested without a store."""
    assert not any(
        "pyoxigraph" in m for m in _imports(PACKAGE / "horn" / "rules.py")
    )
