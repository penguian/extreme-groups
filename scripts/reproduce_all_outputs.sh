#!/usr/bin/env bash
# Reproduce all 21 archival output files (4 .txt tables and 17 .log files)
# deposited in Zenodo record 10.5281/zenodo.19067332.
#
# Usage (from repository root):
#   bash scripts/reproduce_all_outputs.sh [OUTPUT_DIR]
# Default OUTPUT_DIR: ../extreme-groups-output

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

OUTDIR="${1:-$REPO_ROOT/../extreme-groups-output}"
mkdir -p "$OUTDIR"
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

echo "Reproducing all 21 archival files into: $OUTDIR"
rm -f "$OUTDIR"/*.txt "$OUTDIR"/*.log "$OUTDIR"/*.out

# Phase 1: Generate iso_classes.txt and launch parallel long-running GAP jobs
gap -q scripts/iso_orbits_classify.g < /dev/null &
PID_ISO=$!

for j in 0 1 2 3 4 5; do
  gap -q "scripts/exhaustive_5_7/job${j}.g" < /dev/null &
done

gap -q scripts/classify_extreme_7_7_and_7_9.g < /dev/null > "$OUTDIR/classify_extreme_7_7_and_7_9.log" &
gap -q scripts/branch_depth_extreme.g < /dev/null > "$OUTDIR/branch_depth_extreme.log" &
gap -q scripts/classify_extreme_5_5_to_5_9.g < /dev/null > "$OUTDIR/classify_extreme_5_5_to_5_9.log" &
gap -q scripts/verify_extreme_7_9.g < /dev/null > "$OUTDIR/verify_extreme_7_9.log" &
gap -q scripts/check_capable_extreme_7_9.g < /dev/null > "$OUTDIR/check_capable_extreme_7_9.log" &
gap -q scripts/verify_witt_pole_anupq.g < /dev/null > "$OUTDIR/verify_witt_pole_anupq.log" &

# Wait for iso_classes.txt before running scripts that read it
wait "$PID_ISO"
cp scripts/iso_classes.txt "$OUTDIR/iso_classes.txt"

# Phase 2: Fast scripts and scripts reading scripts/iso_classes.txt
gap -q scripts/iso_class_invariants.g < /dev/null > "$OUTDIR/iso_class_invariants.txt"
gap -q scripts/verify_consistency_and_case_counts.g < /dev/null > "$OUTDIR/verify_consistency_and_case_counts.log"
gap -q scripts/verify_anupq_completeness.g < /dev/null > "$OUTDIR/verify_anupq_completeness.log"
gap -q scripts/verify_cknp_1E_2E_on_extreme_classes.g < /dev/null > "$OUTDIR/verify_cknp_1E_2E_on_extreme_classes.log"
gap -q scripts/test_Sk_all.g < /dev/null > "$OUTDIR/test_Sk_all.log"
gap -q scripts/verify_E5_stabilisers_normal_form.g < /dev/null > "$OUTDIR/verify_E5_stabilisers_normal_form.log"
gap -q scripts/verify_fixed_point_layers.g < /dev/null > "$OUTDIR/verify_fixed_point_layers.log"
gap -q scripts/google_ai_subst_e5.g < /dev/null > "$OUTDIR/google_ai_subst_e5.log"
gap -q scripts/classify_extreme_3_max_class.g < /dev/null > "$OUTDIR/classify_extreme_3_max_class.log"
echo 'P_TO_RUN := 5; Read("scripts/count_max_class_totals.g");' | gap -q > "$OUTDIR/count_max_class_totals_p5.log"
echo 'P_TO_RUN := 7; Read("scripts/count_max_class_totals.g");' | gap -q > "$OUTDIR/count_max_class_totals_p7.log"
"$PY_SYMPY" scripts/verify_jacobi_witt_factorizations.py > "$OUTDIR/verify_jacobi_witt_factorizations.log"

# Wait for all parallel background jobs (including job0..job5) to finish
wait

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
if [ "$N_TXT" -ne 4 ] || [ "$N_LOG" -ne 17 ]; then
  echo "Error: Expected 4 .txt and 17 .log files, got $N_TXT .txt and $N_LOG .log" >&2
  exit 1
fi
