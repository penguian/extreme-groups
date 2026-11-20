# Extreme Transitive $p$-Groups of Maximal Class: Computational and Formal Verification Suite

This repository contains the deterministic finite-group computations (GAP 4 and ANUPQ), symbolic polynomial verifications (Python/SymPy), and machine-checked algebraic proofs (Lean 4) for extreme transitive $p$-groups of maximal class.

> Computational verification and classification datasets: [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24083344.svg)](https://doi.org/10.5281/zenodo.24083344)

---

## Prerequisites

- **GAP**: Version 4.15.1 or newer ([https://www.gap-system.org](https://www.gap-system.org)), with packages:
  - **ANUPQ** (`anupq` >= 3.3.3, including its compiled `pq` C binary)
  - **AutPGrp** (`autpgrp`, required by ANUPQ to compute $p$-group automorphisms and descendants)
  - **SmallGroups** (`smallgrp`, used for small-order cross-checks)
  - *Debian/Ubuntu:* `sudo apt install gap gap-anupq gap-autpgrp gap-smallgrp` (or compile `pkg/anupq*` via `./configure && make` in a full GAP installation)
- **Python**: Version 3.8+ with **SymPy** (`sudo apt install python3-sympy` or `pip install sympy`)
- **Lean 4**: Version 4.35.0 or newer via [elan](https://github.com/leanprover/elan) (`elan toolchain install leanprover/lean4:v4.35.0`; no `lake` project or `Mathlib` download is required)

Quick prerequisite check (run from the **root directory** of this repository):
```bash
gap -q --quitonbreak -c 'if LoadPackage("anupq") = fail or LoadPackage("autpgrp") = fail or LoadPackage("smallgrp") = fail then Error("Missing GAP package"); fi; QUIT;'
python3 -c 'import sympy'
lean --version
```

All verification scripts should be executed from the **root directory** of this repository.

---

## Repository Structure

```text
extreme-groups/
├── LICENSE                                      # MIT License
├── README.md                                    # This document
├── lib/                                         # Shared GAP libraries
│   ├── extreme_lib.g                            # Package guards, UltraFastF, TwoStepCentralizer, ANUPQ/tower helpers
│   ├── iso_orbits_lib.g                         # Automorphism orbits in G(alpha) and iso_classes.txt parser
│   ├── klg_lib.g                                # Kovacs-Leedham-Green positive Witt matrix groups G(p,m)
│   ├── param_5_7_lib.g                          # Order-5^7 family G(alpha), ConsistentAlphas, and slice worker
│   ├── subst_lib.g                              # Polynomial substitution matrix generators
│   └── timings_lib.g                            # Optional runtime reporting (--timings / SHOW_TIMINGS)
└── scripts/                                     # Verification drivers
    ├── branch_depth_extreme.g                   # Coclass-1 branch B_4 census and depth audit for p=3, 5, 7
    ├── check_capable_extreme_7_9.g              # Verifies 0 of the 20 capable groups at 7^9 are extreme
    ├── classify_extreme_3_max_class.g           # Extreme maximal-class 3-groups at 3^3 (2), 3^5 (3), 3^7 (0)
    ├── classify_extreme_5_5_to_5_9.g            # Complete ANUPQ coclass-1 classification for p=5 (5^3..5^9)
    ├── classify_extreme_7_7_and_7_9.g           # Complete ANUPQ coclass-1 classification for p=7 (7^5..7^9)
    ├── count_max_class_totals.g                 # Total maximal-class group counts for p=5 (5^4..5^7) and p=7 (7^4..7^8)
    ├── exhaustive_5_7/                          # Parallel parameter-sweep worker and full results
    │   ├── all.txt                              # Exhaustive fixed-point results across all 625 tuples
    │   └── run_slice.g                          # Parameterized slice worker (SLICE_REM=0..5)
    ├── iso_class_invariants.g                   # Computes exponent, DL, |Z|, and derived series for all 70 classes
    ├── iso_classes.txt                          # Serialized 70 isomorphism classes and orbits at order 5^7
    ├── iso_orbits_classify.g                    # Generates iso_classes.txt by exact orbit partition
    ├── iso_summary.py                           # Cross-validates and summarizes class invariants across all.txt
    ├── reproduce_all_outputs.sh                 # Automated driver generating all 4 .txt tables & 19 .log files
    ├── verify_5_7_anupq_completeness.g          # Exhaustive ANUPQ fit of all 70 order-5^7 descendants of E_5
    ├── verify_5_7_consistency_and_types.g       # 625 consistent tuples and 42/3/25 presentation-type class split
    ├── verify_5_7_extreme_tower.g               # Subdegrees, suborbit regularity, and normalizer-core towers at 5^7
    ├── verify_5_7_fixed_point_layers.g          # Fixed-point layer distribution (f=13,021) across 375 tuples
    ├── verify_5_7_stabilizer_criterion.g        # Commutator/power formulas and |S_k|=125 criterion across 625 tuples
    ├── verify_auxiliary_assertions.g            # Affine groups, E_5 lattice, mu(E_5), H_2 intersections, d7[85], Witt basis
    ├── verify_e5_stabilizers.g                  # 125 candidate stabilizers T(k,j,b) of E_5 (5 classes, f=521)
    ├── verify_e5_substitution.g                 # Isomorphism between E_5 ~= G(5,5) and substitution group mod x^7
    ├── verify_extreme_7_9.g                     # Independent certificate for order-7^9 extreme group (rho=2 sector)
    ├── verify_extreme_groups.lean               # Zero-dependency Lean 4 formalization (43 theorems) & #print axioms audit
    ├── verify_jacobi_witt_factorizations.py     # SymPy verification of Vergne-Jacobi, Witt poles, and F_p cutoffs
    └── verify_witt_pole_anupq.g                 # G(11,m) extremality (m=3..11) and Witt pole checks for p=5..13
```

---

## Reproduction Guide

### 0. Automated Full Reproduction (All 4 `.txt` Tables and 19 `.log` Files)

To automatically reproduce all 23 deterministic output files (4 `.txt` tables and 19 `.log` files) into a new or empty destination directory:
```bash
bash scripts/reproduce_all_outputs.sh ../extreme-groups-output
```
*(For safety, `reproduce_all_outputs.sh` requires the destination directory to be new or empty and refuses to overwrite a non-empty directory.)*

By default, runtime stamps are omitted so that all 23 output files are 100% deterministic across runs and machines. To include millisecond runtime stamps in `.log` outputs, pass `--timings` (or set `SHOW_TIMINGS=1` / `-c 'SHOW_TIMINGS:=true;'` when invoking individual scripts):
```bash
bash scripts/reproduce_all_outputs.sh --timings ../extreme-groups-output-timed
gap -q scripts/classify_extreme_5_5_to_5_9.g --timings
SHOW_TIMINGS=1 gap -q scripts/classify_extreme_5_5_to_5_9.g
```

### 1. Coclass-1 Classifications ($p = 3, 5, 7$)

- **Prime $p = 3$ (Orders $3^3, 3^5, 3^7$):**
  ```bash
  gap -q scripts/classify_extreme_3_max_class.g
  ```
  *Result:* Extreme maximal-class 3-groups exist at orders $3^3$ (2 classes) and $3^5$ (3 classes, `SmallGroup(243,28..30)`, derived length 2, exponent 9), and none exist at order $3^7$ (6 maximal-class groups, 0 extreme; hence none at any odd order $3^m$, $m \ge 7$ by the inductive quotient property).

- **Prime $p = 5$ (Orders $5^3, 5^5, 5^7, 5^9$):**
  ```bash
  gap -q scripts/classify_extreme_5_5_to_5_9.g
  ```
  *Result:* Confirms 2 classes at $5^3$ (1 capable, $f = 21$), 1 capable class at $5^5$ ($E_5 \cong G(5,5)$, $f = 521$), 24 extreme classes out of 70 at $5^7$ ($f = 13{,}021$, derived length 3, exponent 25), and 0 extreme classes out of 141 at $5^9$ via $[G_1, \gamma_6(G)] = 1$.

- **Prime $p = 7$ (Orders $7^5, 7^7, 7^9$):**
  ```bash
  gap -q scripts/classify_extreme_7_7_and_7_9.g
  gap -q scripts/verify_extreme_7_9.g
  ```
  *Result:* Classifies all 35 extreme classes of order $7^7$ ($f = 102{,}943 = (7^7+1)/8$) and 3,677 extreme classes of order $7^9$ ($f = 5{,}044{,}201 = (7^9+1)/8$, derived length 3, exponent 49).

### 2. Order-$5^7$ Parametric Family and Base Group $E_5$

- **Base group $E_5 \cong G(5,5)$ structure:**
  ```bash
  gap -q scripts/verify_e5_stabilizers.g
  gap -q scripts/verify_e5_substitution.g
  ```
- **Presentation consistency, ANUPQ completeness, and orbit classification:**
  ```bash
  gap -q scripts/iso_orbits_classify.g
  gap -q scripts/verify_5_7_consistency_and_types.g
  gap -q scripts/verify_5_7_anupq_completeness.g
  ```
- **Stabilizer criterion, fixed-point layers, normalizer-core towers, and invariants:**
  ```bash
  gap -q scripts/verify_5_7_stabilizer_criterion.g
  gap -q scripts/verify_5_7_fixed_point_layers.g
  gap -q scripts/verify_5_7_extreme_tower.g
  gap -q scripts/iso_class_invariants.g
  python3 scripts/iso_summary.py
  ```
- **Individual parallel slice worker (indices $i \equiv r \pmod 6$):**
  ```bash
  SLICE_REM=0 gap -q scripts/exhaustive_5_7/run_slice.g
  ```

### 3. Branch $\mathcal{B}_4$, Witt Pole Checks, Auxiliary Checks, SymPy, and Lean 4

```bash
echo 'P_TO_RUN := 5; Read("scripts/count_max_class_totals.g");' | gap -q
echo 'P_TO_RUN := 7; Read("scripts/count_max_class_totals.g");' | gap -q
gap -q scripts/branch_depth_extreme.g
gap -q scripts/check_capable_extreme_7_9.g
gap -q scripts/verify_witt_pole_anupq.g
gap -q scripts/verify_auxiliary_assertions.g
python3 scripts/verify_jacobi_witt_factorizations.py
lean scripts/verify_extreme_groups.lean
```

- `count_max_class_totals.g`: builds all maximal-class groups of order $p^n$ from all maximal-class parents and checks totals against published values (Blackburn 1958; Newman 1990; O'Brien--Vaughan-Lee 2005; Lee--Vaughan-Lee 2024: 99 at $5^7$ and 1,988 at $7^8$).
- `branch_depth_extreme.g` and `check_capable_extreme_7_9.g`: audit branch $\mathcal{B}_4$ counts across $p = 3, 5, 7$ and confirm 0 of the 20 capable groups at $7^9$ are extreme.
- `verify_witt_pole_anupq.g`: verifies extremality of $G(11, m)$ for odd $3 \le m \le 11$, and uses weighted `Pq` presentations to verify immediate maximal-class descendant counts of $G(p, p)$ for $p \in \{5, 7, 11, 13\}$ (`18` / `1` capable at $5^6$; `472` / `0` capable at $7^8$; `0` capable at $11^{12}$ and $13^{14}$).
- `verify_auxiliary_assertions.g`: checks affine chain-ring groups over $\mathbb{Z}/p^n\mathbb{Z}$ and $\mathbb{F}_p[y]/(y^n)$, the subgroup lattice and minimal faithful degree $\mu(E_5) = 125$ of $E_5$, conjugate intersection sizes of $H_2$, non-extreme Type II/III counts, the nine Type-I-only extreme tuples, the 409 non-extreme $7^9$ descendants in sector $\mu_3 = 6\lambda$, and GAP's divided-power Witt basis rescaling.
- `verify_jacobi_witt_factorizations.py`: symbolically verifies the derivation recurrence, weight-9/11/12 Vergne-Jacobi factorizations, degree-0 triangular recurrence, positive Witt structure constants and $p$-adic valuations, and direct modulo-$p$ elimination at $m = p + 2, p + 4$ ($p \le 47$).
- `verify_extreme_groups.lean`: machine-checks 43 standalone formal theorems in Lean 4 covering the disjoint-layer sieve sum, positive Witt identities and top-weight residue factorization, graded Lie recurrences and Vergne-Jacobi Nullstellensatz certificates, order-$p^{p+4}$ cutoffs ($p = 5, 7$), order-$5^7$ stabilizer criteria, and order-$7^9$ sector congruences, together with `#print axioms` checks.

---

## License

This repository is distributed under the [MIT License](LICENSE).
