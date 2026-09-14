"""A Horn rule table, read and written as data.

Mirrors `OOCert.HornParse.parseRules` and `OOCert.HornParse.ruleStr` on the Lean
side and `open_ontologies::reason::parse_rules` on the Rust side. The format is

    name TAB bodyLength TAB (s TAB p TAB o)*bodyLength TAB hs TAB hp TAB ho

one rule per line, LF-terminated, where a field beginning with `?` is a variable
and anything else is a term in its N-Triples spelling. N-Triples terms begin with
`<`, `_:` or `"`, so the encoding is unambiguous and needs no escape layer.

This module imports no triple store. It is pure text and dataclasses, which is
what lets the rule table be tested without pyoxigraph and what keeps the
question "is this a well-formed rule?" separate from "what does this graph
entail?".

Two refusals go beyond what the Lean parser rejects, both because this side has
to PRODUCE bindings rather than check them, and both matching the Rust producer:
a head variable that does not occur in the body, and a carriage return.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from importlib import resources
from typing import Sequence

from .terms import checked_field


class RuleTableError(ValueError):
    """A rule table that cannot be parsed, or that a producer must refuse."""


@dataclass(frozen=True)
class AtomPat:
    """A triple pattern. Each field is in the FILE's own encoding: a leading
    `?` means a variable, anything else is an N-Triples term. Keeping the raw
    spelling means a rule round-trips through `rules.tsv` unchanged, which is
    what `OOCert.HornParse.patOf` and `patStr` do on the Lean side. Predicate
    position may be a variable: `Interp` has one ternary extension, so a
    property is a domain element like any other and the language stays
    first-order."""

    s: str
    p: str
    o: str

    def fields(self) -> tuple[str, str, str]:
        return (self.s, self.p, self.o)


@dataclass(frozen=True)
class RulePattern:
    """`forall vars. body -> head`, the quantifier left implicit."""

    name: str
    body: tuple[AtomPat, ...]
    head: AtomPat

    def atoms(self) -> tuple[AtomPat, ...]:
        return self.body + (self.head,)


def is_var(pat: str) -> bool:
    """True when this pattern field is a variable.

    `parse_rules` refuses any constant not starting with `<`, `_:` or `"`, so a
    leading `?` is an exact test rather than a heuristic: no constant that
    survived parsing can begin with one.
    """
    return pat.startswith("?")


def vars_of(atoms: Sequence[AtomPat]) -> list[str]:
    """Variable names in FIRST-OCCURRENCE order, scanning each atom s, p, o.

    This is the order `src/reason.rs` builds `CRule::vars` in, over
    `RulePattern::atoms()` (body atoms in order, then the head), and it is the
    order the binding list in `horn.tsv` is emitted in. The checker does not care
    about binding order, since `substOf` is a lookup, so this costs nothing and
    buys a diff against the Rust certificate that a human can read.
    """
    out: list[str] = []
    for a in atoms:
        for f in a.fields():
            if is_var(f):
                v = f[1:]
                if v not in out:
                    out.append(v)
    return out


def parse_rules(text: str) -> list[RulePattern]:
    """Parse a rule table. Malformed input names the line and what was wrong."""
    rules: list[RulePattern] = []
    for n, line in enumerate(text.split("\n"), start=1):
        if line == "":
            # `HornParse.parseRules` skips empty lines, so a trailing newline is
            # fine and a blank line in the middle is not an error either.
            continue
        if "\r" in line:
            raise RuleTableError(
                f"rules line {n}: the line contains a carriage return. HornParse splits on "
                f"'\\n' alone, so a CRLF file puts a '\\r' inside the last term of every line "
                f"and silently changes what that term is. Convert the file rather than have "
                f"it stripped here"
            )
        fields = line.split("\t")
        if len(fields) < 2:
            raise RuleTableError(
                f"rules line {n}: expected a name, a body length and then the patterns, got "
                f"{len(fields)} tab-separated field(s)"
            )
        name, count = fields[0], fields[1]
        if not name:
            raise RuleTableError(f"rules line {n}: the rule name is empty")
        checked_field(name, f"rules line {n} rule name")
        if not (count.isascii() and count.isdigit()):
            # `str.isdigit()` is true of '٣' and '²'; `int()` accepts the first
            # and would read a body length the Lean `toNat?` never would.
            raise RuleTableError(
                f"rules line {n}: body length {count!r} is not a decimal number"
            )
        m = int(count)
        rest = fields[2:]
        if len(rest) != 3 * m + 3:
            raise RuleTableError(
                f"rules line {n}: a body of {m} atom(s) plus a head needs {3 * m + 3} "
                f"pattern fields, got {len(rest)}"
            )
        for i, pat in enumerate(rest):
            _check_pattern(pat, n, i, m)
        body = tuple(
            AtomPat(rest[3 * i], rest[3 * i + 1], rest[3 * i + 2]) for i in range(m)
        )
        head = AtomPat(rest[3 * m], rest[3 * m + 1], rest[3 * m + 2])
        body_vars = set(vars_of(body))
        loose = [f[1:] for f in head.fields() if is_var(f) and f[1:] not in body_vars]
        if loose:
            raise RuleTableError(
                f"rules line {n}: rule {name!r} has head variable ?{loose[0]}, which does not "
                f"occur in the body. The checker accepts such a rule, because SatRule "
                f"quantifies over every substitution, but this engine has nothing to bind it "
                f"to and would have to invent a term. Refusing is the only honest option"
            )
        rules.append(RulePattern(name=name, body=body, head=head))
    return rules


def _check_pattern(pat: str, line: int, index: int, body_len: int) -> None:
    which = (
        f"body atom {index // 3 + 1} position {index % 3 + 1}"
        if index < 3 * body_len
        else f"head position {index - 3 * body_len + 1}"
    )
    if is_var(pat):
        if len(pat) == 1:
            raise RuleTableError(
                f"rules line {line}: {which} is '?' with no variable name"
            )
        checked_field(pat, f"rules line {line} {which}")
        return
    if not (pat.startswith("<") or pat.startswith("_:") or pat.startswith('"')):
        raise RuleTableError(
            f"rules line {line}: {which} is {pat!r}, which is neither a variable (?x) nor an "
            f"N-Triples term (<iri>, _:blank, or a quoted literal). The store spells every "
            f"term in N-Triples, so a constant in any other spelling would match nothing and "
            f"the rule would silently never fire. That is a typo, not a rule"
        )
    checked_field(pat, f"rules line {line} {which}")


def rules_tsv(rules: Sequence[RulePattern]) -> str:
    """Render a rule table back to `rules.tsv`.

    Byte-for-byte `OOCert.HornParse.ruleStr` per line, LF-terminated, so a table
    read here and written back out digests to the value it came in with. The
    fields are re-checked on the way out because a `RulePattern` can be built
    programmatically by a caller who never went through `parse_rules`.
    """
    lines = []
    for r in rules:
        fields = [checked_field(r.name, f"rule {r.name!r} name"), str(len(r.body))]
        for a in r.atoms():
            for f in a.fields():
                fields.append(checked_field(f, f"rule {r.name!r} pattern field"))
        lines.append("\t".join(fields))
    return "".join(line + "\n" for line in lines)


def builtin_rules_bytes() -> bytes:
    """The vendored built-in table, as BYTES, to be written verbatim.

    Verbatim and not re-rendered: `lean/HMain.lean` decides which warrant a run
    earned by `tableLines R == tableLines Builtin.asHorn`, a full ordered
    equality over the canonical rendering of the whole table. Copying bytes
    removes every way a renderer could cost the absolute verdict.
    """
    return (
        resources.files("open_ontologies_lite.horn")
        .joinpath("tables/builtin_rules.tsv")
        .read_bytes()
    )


@lru_cache(maxsize=1)
def builtin_rules() -> tuple[RulePattern, ...]:
    """The vendored built-in table, parsed, for matching against a graph.

    A rule's identity in a certificate is its INDEX, never its name: `scm-eqc1`
    occupies rows 11 and 12 and `scm-eqp1` rows 13 and 14, because each licenses
    two conclusions. There is deliberately no name-to-index map anywhere in this
    package; a `dict[str, int]` would silently lose one of each pair.
    """
    return tuple(parse_rules(builtin_rules_bytes().decode("utf-8")))
