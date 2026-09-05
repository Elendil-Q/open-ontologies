#!/bin/bash
set -e
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BENCHMARK_DIR="$SCRIPT_DIR/.."
PIZZA_OWL="$BENCHMARK_DIR/reference/pizza-reference.owl"
OO_BIN="${OO_BIN:-open-ontologies}"
RESULTS_DIR="$SCRIPT_DIR/results"

mkdir -p "$RESULTS_DIR"

echo "=== Pizza Ontology Correctness Benchmark ==="
echo ""

if [ ! -f "$PIZZA_OWL" ]; then
    echo "ERROR: Pizza reference ontology not found at $PIZZA_OWL"
    exit 1
fi

# 1. Open Ontologies
#
# `load` and `reason` must run in ONE process. The store is in memory and dies
# with the process, so invoking them separately reasoned over an empty graph
# and wrote a result that described nothing, while the script exited 0 and the
# comparison downstream treated it as a measurement. `batch -` keeps one
# process alive across both commands, which is what benchmark/lubm already
# does (see run_lubm.py:90).
echo "Running Open Ontologies (owl-dl)..."
printf '%s\n' "load $PIZZA_OWL" "reason --profile owl-dl" \
    | $OO_BIN batch - > "$RESULTS_DIR/oo_batch.json"

# Take the reason result, which is the last line, and refuse to continue on an
# empty graph rather than reporting a correctness figure derived from nothing.
python3 - "$RESULTS_DIR/oo_batch.json" "$RESULTS_DIR/oo_result.json" <<'PY'
import json, sys
lines = [l for l in open(sys.argv[1]) if l.strip()]
if not lines:
    sys.exit("ERROR: batch produced no output")
result = json.loads(lines[-1])
if result.get("error"):
    sys.exit("ERROR: reason failed: {}".format(result["error"]))
classes = result.get("classes") or result.get("class_count") or 0
if not classes:
    sys.exit("ERROR: reasoned over an empty graph. The load step did not "
             "reach the reasoner, so any number printed here would be "
             "meaningless. Check that `batch` accepted the load command.")
json.dump(result, open(sys.argv[2], "w"), indent=1)
print("  {} classes reasoned.".format(classes))
PY
echo "  Done."

# 2. HermiT
if ls "$SCRIPT_DIR/lib/"*.jar 1>/dev/null 2>&1; then
    echo "Running HermiT..."
    java -cp "$SCRIPT_DIR:$SCRIPT_DIR/lib/*" JavaReasoner hermit "$PIZZA_OWL" "$RESULTS_DIR/hermit_result.json"

    # 3. Pellet
    echo "Running Pellet..."
    java -cp "$SCRIPT_DIR:$SCRIPT_DIR/lib/*" JavaReasoner pellet "$PIZZA_OWL" "$RESULTS_DIR/pellet_result.json"

    # 4. Compare
    echo ""
    echo "Comparing results..."
    python3 "$SCRIPT_DIR/compare_results.py" \
        "$RESULTS_DIR/hermit_result.json" \
        "$RESULTS_DIR/pellet_result.json" \
        "$RESULTS_DIR/oo_result.json"
else
    echo ""
    echo "SKIPPING Java reasoners (no jars in $SCRIPT_DIR/lib/)"
    echo "See README.md for setup instructions."
    echo ""
    echo "Open Ontologies result saved to $RESULTS_DIR/oo_result.json"
fi
