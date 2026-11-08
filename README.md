# Extreme Transitive $p$-Groups of Maximal Class: GAP Verification Suite

This repository contains the complete computational verification scripts and libraries for the paper:
> **Revisiting extreme transitive $p$-groups of maximal class**  
> Paul C. Leopardi (2026).  
> Archival Data: [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19067332.svg)](https://doi.org/10.5281/zenodo.19067332)

---

## Prerequisites

- **GAP**: Version 4.15.1 or newer ([https://www.gap-system.org](https://www.gap-system.org))
- **ANUPQ Package**: Version 3.3.3 or newer (`LoadPackage("anupq");`)
- **Python**: Version 3.8+ (for `iso_summary.py`, and with `sympy` for `verify_jacobi_witt_factorizations.py`)
- **Lean 4**: Version 4.35.0 or newer (for `verify_extreme_groups.lean`)

All scripts should be executed from the **root directory** of this repository.

---

## Repository Structure

```text
extreme-groups/
├── LICENSE                            # MIT License
├── README.md                          # This document
├── lib/                               # Core mathematical libraries
│   ├── alpha_lib.g                    # 1982 family presentation generators (DescGroup, ConsistentAlphas)
│   ├── iso_orbits_lib.g               # Automorphism group & orbit partition algorithms
│   ├── google_ai_subst_lib.g          # Polynomial substitution group calculations
│   ├── klg_lib.g                      # Matrix PcGroups, TwoStepCentralizer, and UltraFastF counters
│   └── timings_lib.g                  # Optional runtime reporting (--timings / SHOW_TIMINGS)
└── scripts/                           # Primary verification drivers
    ├── reproduce_all_outputs.sh       # Automated driver generating all 4 .txt tables & 17 .log files
    ├── classify_extreme_5_5_to_5_9.g  # Complete ANUPQ coclass-1 classification for p=5 (orders 5^3..5^9)
    ├── classify_extreme_7_7_and_7_9.g # Complete ANUPQ coclass-1 classification for p=7 (orders 7^5..7^9)
    ├── classify_extreme_3_max_class.g # Extreme maximal-class 3-groups: orders 3^3, 3^5 (3 classes) and 3^7 (none)
    ├── count_max_class_totals.g       # Total maximal-class groups of order p^4..p^7 (all parents) vs published counts; p=5, 7
    ├── branch_depth_extreme.g         # Coclass-1 branch B_4 and depth audit for p=3, 5, 7 (Prop. 8.4 & Table 3)
    ├── check_capable_extreme_7_9.g    # Verifies 0 of the 20 capable groups at 7^9 are extreme (terminality of 3,677 classes)
    ├── verify_witt_pole_anupq.g       # ANUPQ verification of G(11,m) extremality & Witt pole termination of G(p,p) for p=5..17
    ├── verify_jacobi_witt_factorizations.py # SymPy verification of Vergne-Jacobi & Witt factorizations (Props. 9.1-9.2)
    ├── verify_extreme_groups.lean     # Zero-dependency Lean 4.35.0 formal verification of sieve & Lie algebra certificates
    ├── verify_extreme_7_9.g           # Independent certificate for order-7^9 extreme group in the rho=2 sector
    ├── verify_consistency_and_case_counts.g # 625 consistent presentations & 42/3/25 case split
    ├── verify_anupq_completeness.g    # Exhaustive ANUPQ fit of all 70 order-5^7 descendants of E_5
    ├── verify_E5_stabilisers_normal_form.g  # 125 candidate stabilizers T(k,j,b) of E_5
    ├── test_Sk_all.g                  # Lemma 6.1 & Theorem 6.2 on order-125 stabilizers
    ├── verify_fixed_point_layers.g    # Fixed-point layer distribution across 375 presentations
    ├── verify_cknp_1E_2E_on_extreme_classes.g # CKNP Theorems 1E & 2E on 24 extreme classes
    ├── google_ai_subst_e5.g           # Proof that E_5 is isomorphic to substitution group G(5,5)
    ├── iso_orbits_classify.g          # Generates iso_classes.txt by orbit partition
    ├── iso_class_invariants.g         # Computes all invariants in Table 1
    ├── iso_summary.py                 # Summary and cross-validation of invariants
    ├── iso_classes.txt                # Serialized 70 isomorphism classes and orbits
    └── exhaustive_5_7/                # Parallel parameter-sweep batch jobs
        ├── job0.g ... job5.g          # Distributed fixed-point search across 625 presentations
        └── all.txt                    # Exhaustive per-presentation results
```

---

## Reproduction Guide

### 0. Automated Full Reproduction (All 4 `.txt` Tables and 17 `.log` Files)
To automatically reproduce the complete archival dataset deposited in Zenodo (`10.5281/zenodo.19067332` — 4 `.txt` tables and 17 `.log` files) into a new or empty destination directory:
```bash
bash scripts/reproduce_all_outputs.sh ../extreme-groups-output
```
*(For safety, `reproduce_all_outputs.sh` requires the destination directory to be new or empty and refuses to overwrite a non-empty directory.)*
By default, runtime stamps are omitted so that all 21 output files are 100% deterministic across runs and machines. To include millisecond runtime stamps in `.log` outputs, pass `--timings` (or set `SHOW_TIMINGS=1` / `-c 'SHOW_TIMINGS:=true;'` when invoking individual GAP scripts):
```bash
bash scripts/reproduce_all_outputs.sh --timings ../extreme-groups-output-timed
gap -q scripts/classify_extreme_5_5_to_5_9.g --timings
SHOW_TIMINGS=1 gap -q scripts/classify_extreme_5_5_to_5_9.g
```

### 1. Unified Coclass-1 Classifications
- **Prime $p = 5$ (Orders $5^3, 5^5, 5^7, 5^9$):**
  ```bash
  gap -q scripts/classify_extreme_5_5_to_5_9.g
  ```
  *Result:* Confirms 2 classes at $5^3$ (1 capable, $f=21$), 1 capable class at $5^5$ ($E_5 \cong G(5,5)$, $f=521$), exactly 24 extreme classes out of 70 at $5^7$ ($f=13{,}021$), and 0 extreme classes out of 141 at $5^9$ via the universal depth-2 centralizer cutoff $[G_1, \gamma_6(G)] = 1$ (runtime: ~18 seconds).

- **Prime $p = 7$ (Orders $7^5, 7^7, 7^9$ — Theorem 8.7 & Table 2):**
  ```bash
  gap -q scripts/classify_extreme_7_7_and_7_9.g
  gap -q scripts/verify_extreme_7_9.g
  ```
  *Result:* Classifies all 35 extreme classes of order $7^7$ ($f=102{,}943 = (7^7+1)/8$) and 3,677 extreme classes of order $7^9$ ($f=5{,}044{,}201 = (7^9+1)/8$) (runtime: ~3 minutes).

- **Prime $p = 3$ (Orders $3^3, 3^5, 3^7$):**
  ```bash
  gap -q scripts/classify_extreme_3_max_class.g
  ```
  *Result:* Extreme maximal-class 3-groups exist at orders $3^3$ (2 classes) and $3^5$ (3 classes, `SmallGroup(243,28..30)`, derived length 2, exponent 9), and none at order $3^7$ (6 maximal-class groups, 0 extreme); by Lemma K0 none exists at any odd order $3^m$, $m\ge 7$ (runtime: seconds).

### 2. Order $5^7$ Descendants of $E_5$ (Sections 5 & 6, Table 1)
- **Presentation consistency and case counts:**
  ```bash
  gap -q scripts/verify_consistency_and_case_counts.g
  ```
- **Completeness of 1982 family via ANUPQ:**
  ```bash
  gap -q scripts/verify_anupq_completeness.g
  ```
- **Stabilizer formulas and extremality verification:**
  ```bash
  gap -q scripts/test_Sk_all.g
  gap -q scripts/verify_fixed_point_layers.g
  gap -q scripts/verify_cknp_1E_2E_on_extreme_classes.g
  ```
- **Class invariants summary (Table 1):**
  ```bash
  python3 scripts/iso_summary.py
  ```

### 3. Base Group $E_5$ Structure (Section 4)
- **Normal form and conjugacy of stabilizers:**
  ```bash
  gap -q scripts/verify_E5_stabilisers_normal_form.g
  ```
- **Polynomial substitution group isomorphism:**
  ```bash
  gap -q scripts/google_ai_subst_e5.g
  ```

### 4. Total Maximal-Class Counts, Coclass-1 Branch $\mathcal B_4$ Audit ($p = 3, 5, 7$), and Witt Pole Checks ($p \ge 5$)

```bash
echo "P_TO_RUN := 5; Read(\"scripts/count_max_class_totals.g\");" | gap -q
echo "P_TO_RUN := 7; Read(\"scripts/count_max_class_totals.g\");" | gap -q
gap -q scripts/branch_depth_extreme.g
gap -q scripts/check_capable_extreme_7_9.g
gap -q scripts/verify_witt_pole_anupq.g
python3 scripts/verify_jacobi_witt_factorizations.py
lean scripts/verify_extreme_groups.lean
```

Builds all maximal-class groups of order $p^n$ from all maximal-class parents of order $p^{n-1}$ and compares the totals with published values ($99$ at $5^7$: Newman 1990, O'Brien--Vaughan-Lee 2005; $m(p,n)$ of Lee--Vaughan-Lee for $p=7$), audits the subtree in branch $\mathcal B_4$ of $\mathcal T(p)$ (Proposition 8.4 & Table 3), confirms in ANUPQ that the positive Witt group $G(p,p)$ has $2p^2+3p+3$ immediate maximal-class descendants of order $p^{p+1}$ with $0$ capable for $p\in\{7,11,13,17\}$ (Proposition 9.2(2)), verifies all graded Lie algebra Jacobi and Witt factorizations symbolically in SymPy, and machine-checks the sieve, collection, and Nullstellensatz obstruction certificates in Lean 4.

---

## License

This repository is distributed under the [MIT License](LICENSE).

