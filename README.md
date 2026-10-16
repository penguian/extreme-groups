# Extreme Permutation $p$-Groups of Maximal Class: GAP Verification Suite

This repository contains the complete computational verification scripts and libraries for the paper:
> **Extreme Permutation $p$-Groups of Maximal Class: The 1982 NICE Structure Theorem and a Correction at Order $5^7$**  
> Paul Leopardi (2026).  
> Archival Data: [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19067332.svg)](https://doi.org/10.5281/zenodo.19067332)

---

## Prerequisites

- **GAP**: Version 4.15.1 or newer ([https://www.gap-system.org](https://www.gap-system.org))
- **ANUPQ Package**: Version 3.3.3 or newer (`LoadPackage("anupq");`)
- **Python**: Version 3.8+ (for invariant analysis script `iso_summary.py`)

All scripts should be executed from the **root directory** of this repository.

---

## Repository Structure

```text
extreme-groups/
├── README.md                          # This document
├── lib/                               # Core mathematical libraries
│   ├── alpha_lib.g                    # 1982 family presentation generators (DescGroup, ConsistentAlphas)
│   ├── iso_orbits_lib.g               # Automorphism group & orbit partition algorithms
│   ├── google_ai_subst_lib.g          # Polynomial substitution group calculations
│   ├── klg_lib.g                      # Matrix PcGroups and UltraFastF counters
│   └── fsz_lib.g                      # Frobenius-Schur indicator computations
└── scripts/                           # Primary verification drivers
    ├── classify_extreme_5_5_to_5_9.g  # Complete ANUPQ coclass-1 classification for p=5 (orders 5^3..5^9)
    ├── classify_extreme_7_7_and_7_9.g  # Complete ANUPQ coclass-1 classification for p=7 (orders 7^5..7^9)
    ├── verify_consistency_and_case_counts.g # 625 consistent presentations & 42/3/25 case split
    ├── verify_anupq_completeness.g     # Exhaustive ANUPQ fit of all 70 order-5^7 descendants of E_5
    ├── verify_E5_stabilisers_normal_form.g  # 125 candidate stabilizers T(k,j,b) of E_5
    ├── test_Sk_all.g                  # Lemma 6.2 & Theorem 6.3 on order-125 stabilizers
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

### 1. Unified Coclass-1 Classifications
- **Prime $p = 5$ (Orders $5^3, 5^5, 5^7, 5^9$):**
  ```bash
  gap -q scripts/classify_extreme_5_5_to_5_9.g
  ```
  *Result:* Confirms 1 class at $5^3$ ($f=21$), 1 capable class at $5^5$ ($E_5 \cong G(5,5)$, $f=521$), exactly 24 extreme classes out of 70 at $5^7$ ($f=13{,}021$), and 0 extreme classes out of 141 at $5^9$ via the universal depth-2 centralizer cutoff $[G_1, \gamma_6(G)] = 1$ (runtime: ~18 seconds).

- **Prime $p = 7$ (Orders $7^5, 7^7, 7^9$ — Theorem 7.9 & Table 2):**
  ```bash
  gap -q scripts/classify_extreme_7_7_and_7_9.g
  ```
  *Result:* Classifies all 35 extreme classes of order $7^7$ ($f=102{,}879$) and 3,677 extreme classes of order $7^9$ ($f=5{,}042{,}101$) (runtime: ~3 minutes).

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
