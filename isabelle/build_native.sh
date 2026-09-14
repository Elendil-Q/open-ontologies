#!/bin/sh
# Link the verified checker into a native executable, so the differential harness can
# run hundreds of certificates without paying Poly/ML's compile time on every one.
#
#   isabelle/build_native.sh  ->  isabelle/build/oo-horn-isabelle
#
# This is the LINK STEP ONLY. Nothing is recompiled from the theories: the input is
# driver/oo_horn_generated.ML, which `isabelle/export.sh` writes out of the session, plus
# driver/oo_horn_cli.sml, which is untrusted by construction.
#
# Why not `polyc`. Poly/ML ships one, and it does not work here: its CFLAGS carry the
# absolute path of the machine Isabelle was BUILT on
# (/tmp/isabelle-makarius/build.../gmp/target/lib), and `-lgmp` then resolves against a
# directory that does not exist on this machine. The bundled runtime directory holds
# libgmp.10.dylib but no libgmp.dylib, so the linker cannot find it there either. The two
# steps below are what polyc does, with the gmp search path pointed somewhere real.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:-$HERE/build/oo-horn-isabelle}

# Where Poly/ML lives. Ask Isabelle first, because ISABELLE_HOME is the only answer that
# is right on a machine that is not this one; fall back to the macOS app bundle, and let
# POLYDIR override both.
ARCH=$(uname -m); [ "$ARCH" = "aarch64" ] && ARCH=arm64
OS=$(uname -s | tr 'A-Z' 'a-z')
if [ -z "$POLYDIR" ] && command -v isabelle >/dev/null 2>&1; then
  IHOME=$(isabelle getenv -b ISABELLE_HOME 2>/dev/null || true)
  [ -n "$IHOME" ] && POLYDIR=$(ls -d "$IHOME"/contrib/polyml-*/"$ARCH-$OS" 2>/dev/null | head -1)
fi
POLYDIR=${POLYDIR:-$(ls -d /Applications/Isabelle*.app/contrib/polyml-*/"$ARCH-$OS" 2>/dev/null | head -1)}
[ -x "$POLYDIR/poly" ] || { echo "poly not found; set POLYDIR=/path/to/polyml/arch-dir" >&2; exit 3; }

# Where libgmp actually lives on this machine. Homebrew first, then the copy Isabelle
# bundles (which has only the versioned name, so it is linked by full path).
if [ -f /opt/homebrew/lib/libgmp.dylib ]; then
  GMP="-L/opt/homebrew/lib -lgmp"
elif [ -f /usr/local/lib/libgmp.dylib ]; then
  GMP="-L/usr/local/lib -lgmp"
elif [ -f "$POLYDIR/libgmp.10.dylib" ]; then
  GMP="$POLYDIR/libgmp.10.dylib"
else
  echo "libgmp not found; install gmp or set GMP=..." >&2; exit 3
fi

mkdir -p "$(dirname "$OUT")"
OBJ=$(mktemp "${TMPDIR:-/tmp}/oo_horn_obj.XXXXXX").o

# 1. Compile the generated core and the CLI, and export `main` as an object file.
printf 'val () = use "%s";\nval () = use "%s";\nval () = PolyML.export("%s", main);\n' \
  "$HERE/driver/oo_horn_generated.ML" "$HERE/driver/oo_horn_cli.sml" "$OBJ" \
  | "$POLYDIR/poly" -q --error-exit

# 2. Link it against the Poly/ML runtime.
g++ -std=gnu++11 -O2 "$OBJ" -o "$OUT" \
    -L"$POLYDIR" -Wl,-rpath,"$POLYDIR" -lpolymain -lpolyml $GMP -lstdc++ 2>/dev/null

rm -f "$OBJ"
echo "wrote $OUT"
