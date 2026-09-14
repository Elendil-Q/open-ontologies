"""The one place a term becomes a certificate field.

The Lean parsers do nothing but split on tab and newline. There is no quoting
layer, no length prefix and no escape pass: ``OOCert.HornParse.parseHornSteps``
calls ``line.splitOn "\\t"`` and reads the fields off by position. It relies on
the fact that an N-Triples term cannot contain a raw tab or newline, because the
serialisation escapes them. That invariant is the format's entire safety
argument, so it is asserted here on every field of every line rather than
assumed, and a violation aborts the run instead of writing a file.

A raw tab inside a bound term shifts every later field of a ``horn.tsv`` line by
one. ``rest.take (2 * k)`` then grabs the wrong fields, the conclusion is read
from the wrong positions, and the checker verifies something that is not what
the engine derived. That is the difference between a format and an attack
surface, and it is why this module exists at all rather than the emitter calling
``str()`` at six different places.
"""

from __future__ import annotations

FORBIDDEN = ("\t", "\n", "\r")


class CertificateFieldError(ValueError):
    """A term or rule field carried a separator. The run stops here."""


def checked_field(text: str, where: str) -> str:
    """Return ``text`` if it can be a certificate field; raise otherwise."""
    for ch in FORBIDDEN:
        if ch in text:
            raise CertificateFieldError(
                f"{where}: the field contains {ch!r}, which is the certificate's "
                f"field or record separator. A term reaching here must already be "
                f"in N-Triples spelling, where tab, newline and carriage return "
                f"are escaped. Field was {text!r}"
            )
    return text


def spell(term, where: str) -> str:
    """The N-Triples spelling of a pyoxigraph term.

    ``str()`` and nothing else. pyoxigraph delegates to oxrdf's Display, which is
    the same code the Rust engine's ``quad.subject.to_string()`` goes through, so
    byte-compatibility with the Lean parser is structural rather than a Python
    re-implementation that can drift.

    Never ``.value``: that is the UNQUOTED lexical form. ``ox.Literal('a\\tb').value``
    returns a string with a RAW tab in it, and an IRI's ``.value`` loses its angle
    brackets, so the field starts with none of ``<``, ``_:`` or ``"`` and matches
    nothing the store holds. ``engine.py``'s ``_terms()`` and ``query()`` use
    ``.value`` for display, and ``dataframe.py``'s ``_literal`` escapes backslash,
    quote and newline but neither tab nor carriage return; none of that code may be
    reused on this path, and the type refusal below is what stops it being.
    """
    if isinstance(term, str):
        raise TypeError(
            f"{where}: spell() takes a pyoxigraph term, not a str. A string that "
            f"is already a spelling goes through checked_field(); a string that is "
            f"not must be parsed into a term first, never formatted into one"
        )
    return checked_field(str(term), where)
