#!/usr/bin/env bash
# Reproduce all 23 deterministic output files (4 .txt tables and 19 .log files)
# of the extreme-groups computational and formal verification suite.
#
# Usage (from repository root):
#   bash scripts/reproduce_all_outputs.sh [--timings] [OUTPUT_DIR]
# Default: deterministic outputs without runtime stamps.
# Pass --timings (or export SHOW_TIMINGS=1) to include millisecond runtime stamps.
# Default OUTPUT_DIR: ../extreme-groups-output

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

export SHOW_TIMINGS="${SHOW_TIMINGS:-0}"
OUTDIR_ARG=""
for arg in "$@"; do
  case "$arg" in
    --timings)
      export SHOW_TIMINGS=1
      ;;
    --no-timings)
      export SHOW_TIMINGS=0
      ;;
    *)
      OUTDIR_ARG="$arg"
      ;;
  esac
done

OUTDIR="${OUTDIR_ARG:-$REPO_ROOT/../extreme-groups-output}"
if [ -e "$OUTDIR" ]; then
  if [ ! -d "$OUTDIR" ]; then
    echo "Error: Destination '$OUTDIR' exists and is not a directory." >&2
    exit 1
  fi
  if [ -n "$(ls -A "$OUTDIR")" ]; then
    echo "Error: Destination directory '$OUTDIR' is not empty. Please specify a new or empty directory." >&2
    exit 1
  fi
else
  mkdir -p "$OUTDIR"
fi
OUTDIR="$(cd "$OUTDIR" && pwd)"

# Locate a Python 3 interpreter with SymPy installed
PY_SYMPY=""
for cand in $(which -a python3 2>/dev/null || true) /usr/bin/python3; do
  if [ -x "$cand" ] && "$cand" -c "import sympy" >/dev/null 2>&1; then
    PY_SYMPY="$cand"
    break
  fi
done
if [ -z "$PY_SYMPY" ]; then
  echo "Error: Could not find a python3 interpreter with 'sympy' installed." >&2
  exit 1
fi

# Locate Lean 4 binary
LEAN_BIN="$(command -v lean 2>/dev/null || true)"
if [ -z "$LEAN_BIN" ] && [ -x "$HOME/.elan/bin/lean" ]; then
  LEAN_BIN="$HOME/.elan/bin/lean"
fi
if [ -z "$LEAN_BIN" ]; then
  echo "Error: Could not find 'lean' (Lean 4.35.0+). Install via elan or add ~/.elan/bin to PATH." >&2
  exit 1
fi

echo "Reproducing all 23 verification output files into: $OUTDIR"

# Phase 1: Generate iso_classes.txt and launch parallel long-running GAP jobs
gap -q --quitonbreak scripts/iso_orbits_classify.g < /dev/null &
PID_ISO=$!

BG_PIDS=()
for j in 0 1 2 3 4 5; do
  SLICE_REM="$j" gap -q --quitonbreak scripts/exhaustive_5_7/run_slice.g < /dev/null &
  BG_PIDS+=("$!")
done

gap -q --quitonbreak scripts/classify_extreme_7_7_and_7_9.g < /dev/null > "$OUTDIR/classify_extreme_7_7_and_7_9.log" &
BG_PIDS+=("$!")
gap -q --quitonbreak scripts/branch_depth_extreme.g < /dev/null > "$OUTDIR/branch_depth_extreme.log" &
BG_PIDS+=("$!")
gap -q --quitonbreak scripts/classify_extreme_5_5_to_5_9.g < /dev/null > "$OUTDIR/classify_extreme_5_5_to_5_9.log" &
BG_PIDS+=("$!")
gap -q --quitonbreak scripts/verify_extreme_7_9.g < /dev/null > "$OUTDIR/verify_extreme_7_9.log" &
BG_PIDS+=("$!")
gap -q --quitonbreak scripts/check_capable_extreme_7_9.g < /dev/null > "$OUTDIR/check_capable_extreme_7_9.log" &
BG_PIDS+=("$!")
gap -q --quitonbreak scripts/verify_witt_pole_anupq.g < /dev/null > "$OUTDIR/verify_witt_pole_anupq.log" &
BG_PIDS+=("$!")

# Wait for iso_classes.txt before running scripts that read it
wait "$PID_ISO"
cp scripts/iso_classes.txt "$OUTDIR/iso_classes.txt"

# Phase 2: Fast scripts and scripts reading scripts/iso_classes.txt
gap -q --quitonbreak scripts/iso_class_invariants.g < /dev/null > "$OUTDIR/iso_class_invariants.txt"
gap -q --quitonbreak scripts/verify_5_7_consistency_and_types.g < /dev/null > "$OUTDIR/verify_5_7_consistency_and_types.log"
gap -q --quitonbreak scripts/verify_5_7_anupq_completeness.g < /dev/null > "$OUTDIR/verify_5_7_anupq_completeness.log"
gap -q --quitonbreak scripts/verify_5_7_extreme_tower.g < /dev/null > "$OUTDIR/verify_5_7_extreme_tower.log"
gap -q --quitonbreak scripts/verify_5_7_stabilizer_criterion.g < /dev/null > "$OUTDIR/verify_5_7_stabilizer_criterion.log"
gap -q --quitonbreak scripts/verify_e5_stabilizers.g < /dev/null > "$OUTDIR/verify_e5_stabilizers.log"
gap -q --quitonbreak scripts/verify_5_7_fixed_point_layers.g < /dev/null > "$OUTDIR/verify_5_7_fixed_point_layers.log"
gap -q --quitonbreak scripts/verify_e5_substitution.g < /dev/null > "$OUTDIR/verify_e5_substitution.log"
gap -q --quitonbreak scripts/classify_extreme_3_max_class.g < /dev/null > "$OUTDIR/classify_extreme_3_max_class.log"
gap -q --quitonbreak scripts/verify_auxiliary_assertions.g < /dev/null > "$OUTDIR/verify_auxiliary_assertions.log"
echo 'P_TO_RUN := 5; Read("scripts/count_max_class_totals.g");' | gap -q --quitonbreak > "$OUTDIR/count_max_class_totals_p5.log"
echo 'P_TO_RUN := 7; Read("scripts/count_max_class_totals.g");' | gap -q --quitonbreak > "$OUTDIR/count_max_class_totals_p7.log"
"$PY_SYMPY" scripts/verify_jacobi_witt_factorizations.py > "$OUTDIR/verify_jacobi_witt_factorizations.log"
"$LEAN_BIN" scripts/verify_extreme_groups.lean > "$OUTDIR/verify_extreme_groups_lean.log"

# Wait for each parallel background job explicitly so set -e catches any non-zero exit
for pid in "${BG_PIDS[@]}"; do
  wait "$pid"
done

cat scripts/exhaustive_5_7/out0.txt \
    scripts/exhaustive_5_7/out1.txt \
    scripts/exhaustive_5_7/out2.txt \
    scripts/exhaustive_5_7/out3.txt \
    scripts/exhaustive_5_7/out4.txt \
    scripts/exhaustive_5_7/out5.txt > scripts/exhaustive_5_7/all.txt
rm -f scripts/exhaustive_5_7/out0.txt \
      scripts/exhaustive_5_7/out1.txt \
      scripts/exhaustive_5_7/out2.txt \
      scripts/exhaustive_5_7/out3.txt \
      scripts/exhaustive_5_7/out4.txt \
      scripts/exhaustive_5_7/out5.txt

cp scripts/exhaustive_5_7/all.txt "$OUTDIR/all.txt"
python3 scripts/iso_summary.py > "$OUTDIR/iso_summary.txt"

N_TXT=$(ls -1 "$OUTDIR"/*.txt 2>/dev/null | wc -l)
N_LOG=$(ls -1 "$OUTDIR"/*.log 2>/dev/null | wc -l)
echo "Done: generated $N_TXT .txt tables and $N_LOG .log files in $OUTDIR"
if [ "$N_TXT" -ne 4 ] || [ "$N_LOG" -ne 19 ]; then
  echo "Error: Expected 4 .txt and 19 .log files, got $N_TXT .txt and $N_LOG .log" >&2
  exit 1
fi
