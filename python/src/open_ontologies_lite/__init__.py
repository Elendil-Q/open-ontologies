"""Open Ontologies Lite: a lightweight, pip-installable Python bridge to the
Oxigraph RDF/OWL engine. No Rust toolchain, no compilation, prebuilt wheels only.
"""

from .dataframe import rows_from_dataframe, rows_to_turtle
from .engine import OntologyEngine, ValidationResult, resolve_format
from .horn import (
    AssertedGraphError,
    CertificateFieldError,
    CertificateUnreadable,
    CheckerUnavailable,
    HornResult,
    RulePattern,
    RuleTableError,
    builtin_rules,
    check_horn,
    find_checker,
    parse_rules,
    rules_tsv,
    run_horn,
)
from .kgcl import ChangeSet, kgcl_diff
from .vocab_check import vocab_check

__version__ = "0.5.0"
__all__ = [
    "OntologyEngine",
    "ValidationResult",
    "resolve_format",
    "ChangeSet",
    "kgcl_diff",
    "vocab_check",
    "rows_from_dataframe",
    "rows_to_turtle",
    "__version__",
]

# The Horn reasoner and the certificate bridge are UNCONDITIONAL exports, with no
# extra to install: the reasoner is pure Python over the pyoxigraph the package
# already requires, and the bridge is standard library. The Lean checker itself is
# an external binary built by `lake`, deliberately not packaged and not a
# dependency of any kind; `check_horn` reports its absence and never works around
# it. See horn/__init__.py for the verdict vocabulary before using any of this.
__all__ += [
    "run_horn",
    "check_horn",
    "find_checker",
    "builtin_rules",
    "parse_rules",
    "rules_tsv",
    "HornResult",
    "RulePattern",
    "RuleTableError",
    "CheckerUnavailable",
    "CertificateUnreadable",
    "CertificateFieldError",
    "AssertedGraphError",
]

# AlignmentIndex needs the optional [align] extra (hnswlib); export it only when
# importable so the base package stays dependency-light.
try:  # pragma: no cover
    from .align import AlignmentIndex, Candidate  # noqa: F401
    __all__ += ["AlignmentIndex", "Candidate"]
except ImportError:  # pragma: no cover
    pass
