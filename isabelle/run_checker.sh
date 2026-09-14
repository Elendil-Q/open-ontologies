#!/bin/sh
# Run the verified checker.
#   usage: run_checker.sh RULES.tsv ASSERTED.tsv CERT.tsv
# Exit 0 = accepted, 1 = rejected, 2 = parse error, 3 = usage or no Poly/ML.
#
# stdout is exactly one JSON object carrying BOTH the strict and the lenient verdict
# (see the comments on conflict C11 in OO_Check.thy).  A differential test should
# compare the accept/reject bit and the verdict word as primary, and the reason and the
# exit code as secondary with a declared tolerance.
#
# Poly/ML prints compiler warnings about the GENERATED code to stdout; they are filtered
# out here.  Set OO_VERBOSE=1 to see everything.
HERE=$(cd "$(dirname "$0")" && pwd)
POLY=${POLY:-$(ls -d /Applications/Isabelle*.app/contrib/polyml-*/*/poly 2>/dev/null | head -1)}
[ -x "$POLY" ] || { echo "poly not found; set POLY=/path/to/poly" >&2; exit 3; }
[ $# -eq 3 ] || { echo "usage: $0 RULES.tsv ASSERTED.tsv CERT.tsv" >&2; exit 3; }

if [ -n "$OO_VERBOSE" ]; then
  OO_RULES="$1" OO_ASSERTED="$2" OO_CERT="$3" \
  exec "$POLY" -q --use "$HERE/driver/oo_horn_generated.ML" \
                  --use "$HERE/driver/oo_horn_driver.sml" --eval 'mainEnv ()'
fi

TMP=$(mktemp "${TMPDIR:-/tmp}/oo_horn.XXXXXX")
OO_RULES="$1" OO_ASSERTED="$2" OO_CERT="$3" \
"$POLY" -q --use "$HERE/driver/oo_horn_generated.ML" \
           --use "$HERE/driver/oo_horn_driver.sml" --eval 'mainEnv ()' >"$TMP" 2>/dev/null
code=$?
grep '^{"rules"' "$TMP" || { echo "no report produced; rerun with OO_VERBOSE=1" >&2; code=3; }
rm -f "$TMP"
exit $code
