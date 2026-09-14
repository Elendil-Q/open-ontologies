"""A pure-Python Horn reasoner whose conclusions carry Lean-checked certificates.

Four modules, split so that "this works with no binary installed" is structural
rather than a promise:

* `terms`   the one place a term becomes a certificate field, and the guard that
            makes a forged derivation step impossible to write by accident.
* `rules`   the rule table as data. Text and dataclasses, no triple store.
* `reason`  the forward chainer and the certificate emitter. Imports pyoxigraph.
* `certify` the bridge to `oo-horn`, the verified checker. Standard library only.

`reason` never imports `certify` and `certify` never imports `reason`, and
`test_the_verdict_words_are_never_written_in_python.py` fails if either ever
does. That is what guarantees the reasoner runs with no checker installed and
that the bridge can be exercised against a certificate this package did not
write. This file imports both, because re-exporting is what it is for, and the
invariant that matters is between the two working modules.

# The verdict vocabulary, which this package never speaks

A certificate over the BUILT-IN rule table can earn `entailed`: every conclusion
is true in every model of the asserted graph. A certificate over ANY other
table, the built-ins plus one extra rule included, earns
`entailed_under_supplied_rules`: every conclusion is true in every model of the
asserted graph THAT ALSO SATISFIES those rules, which are assumed and never
checked. A result the Lean checker has not accepted earns neither and says so.

Only `lean/HMain.lean` decides which of the two a run earned. No module in this
package contains either word as an executable string, and an AST scan in the
test suite enforces it: `verdict` is only ever copied out of the checker's own
report. Read `docs/decisions/0003-a-rule-is-data-and-an-assumption-is-not-a-fact.md`
before changing anything here.
"""

from __future__ import annotations

from .certify import (
    CertificateUnreadable,
    CheckerUnavailable,
    check_horn,
    find_checker,
)
from .reason import (
    AssertedGraphError,
    HornResult,
    HornStep,
    run_horn,
)
from .rules import (
    AtomPat,
    RulePattern,
    RuleTableError,
    builtin_rules,
    builtin_rules_bytes,
    parse_rules,
    rules_tsv,
)
from .terms import CertificateFieldError, checked_field, spell

__all__ = [
    "AssertedGraphError",
    "AtomPat",
    "CertificateFieldError",
    "CertificateUnreadable",
    "CheckerUnavailable",
    "HornResult",
    "HornStep",
    "RulePattern",
    "RuleTableError",
    "builtin_rules",
    "builtin_rules_bytes",
    "check_horn",
    "checked_field",
    "find_checker",
    "parse_rules",
    "rules_tsv",
    "run_horn",
    "spell",
]
