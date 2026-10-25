# Rank2ModuleSVP — SVP on rank-two cyclotomic modules

Lean formalisation of Jiaqi Liu, Yansong Feng, and Yanbin Pan,
[SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, v2](paper/rank2svp_v2.pdf)
([searchable text](paper/rank2svp_v2.txt)). The v1 paper, arXiv:2609.01469
(ePrint 2026/1856), remains in [paper/2609.01469.pdf](paper/2609.01469.pdf), with
[LaTeX sources](paper/src/). [specs/v2_diff.md](specs/v2_diff.md) records the version changes.

Theorem 1.1 (v2): as `q` ranges over odd primes, exact decision-SVP in the canonical
Euclidean norm on full-rank free rank-two submodules of `ℤ[ζ_q]²` is NP-complete under
deterministic polynomial-time many-one reductions from X3C. The Lean completeness theorem
is conditional on the explicit hypothesis `WanPowerSumEstimates`; NP membership is unconditional.
Malformed inputs are rejected by the encoded language in [Problem.lean](Problem.lean).

## Main Lean results

All names below are in namespace `Rank2ModuleSVP`. File links are relative to
`Rank2ModuleSVP/`. Import `Rank2ModuleSVP` for the whole library, or
`Rank2ModuleSVP.Main` for the conditional completeness theorem.

| Result | Lean name | File |
| --- | --- | --- |
| NP membership (unconditional) | `moduleSVP_mem_NP : ModuleSVPLang ∈ NP encSVP` | [MembershipCert.lean](MembershipCert.lean) |
| Theorem 5.2, exact X3C encoding | `exact_X3C_encoding` | [Reduction.lean](Reduction.lean) |
| Total map correctness, X3C ↔ SVP | `reductionMap_correct (hWan) (x)` | [Main.lean](Main.lean) |
| Outputs satisfy the SVP promises | `reductionMap_wellFormed` | [Main.lean](Main.lean) |
| Polynomial-time map | `ReductionMap.reductionMap_polytime` | [ReductionMapPoly.lean](ReductionMapPoly.lean) |
| X3C ≤ₚ SVP | `x3c_polyTimeReducible_moduleSVP (hWan)` | [Main.lean](Main.lean) |
| **Theorem 1.1, conditional NP-completeness** | `moduleSVP_npComplete_of (hWan : WanPowerSumEstimates) : NPComplete encSVP ModuleSVPLang` | [Main.lean](Main.lean) |

The sole named mathematical hypothesis is `WanPowerSumEstimates` in [Wan.lean](Wan.lean),
passed explicitly as `hWan`. It requires Weil/Deligne-strength point-count estimates; see
[notes/weil-bound-research.md](notes/weil-bound-research.md). The Bennett–Peikert minimum
is proved. Corollary 1.2 (search-SVP with one oracle call) is not formalised.

## Proof route

1. Develop odd-prime cyclotomic coefficient norms, descent, ramification, and the
   Bennett–Peikert minimum for the relevant ideals.
2. Use the Wan estimates to count collision-free power-sum completions. Derive coordinate
   ratios and ideal-coset separation, then build the integral checker.
3. Combine admissible representatives, checker bounds, and stability to prove the exact
   X3C encoding of Theorem 5.2.
4. Implement a total list reduction with cubic Sidon offsets, bounded prime scans, and fixed
   outputs for degenerate or malformed inputs. Certify its native polynomial running time.
5. Prove polynomial certificate bounds and NP membership independently of Wan, then assemble
   Theorem 1.1 with the explicit hypothesis.

## Layout

| Directory / files | Contents |
| --- | --- |
| `PrimeCyclotomic.lean`, `Problem.lean` | Quotient field, canonical norms, input promises, encoded language |
| `Descent.lean`, `Descent2.lean`, `BennettPeikert.lean` | Descent, ramified ideal, proved minimum |
| `Wan.lean`, `Completions.lean`, `AsymptoticsAux.lean`, `Asymptotics.lean` | Named point-count hypothesis, completions, asymptotic estimates |
| `Sparse.lean`, `SparsePolynomial.lean`, `RobustCenter.lean` | Sparse tools and ideal-coset separation |
| `CheckerAux.lean`, `Checker.lean`, `Admissible.lean`, `ReductionAux.lean`, `Reduction.lean` | Checker, representatives, stability, exact X3C encoding |
| `ReductionMapAux.lean`, `ReductionMap.lean`, `ReductionMapPoly.lean`, `Main.lean` | Total map, prime scan, native runtime, conditional completeness |
| `MembershipAux.lean`, `Membership.lean`, `MembershipCert.lean` | Certificate bounds, verifier, unconditional NP membership |
| `paper/` | Target v2 PDF and text, v1 PDF and LaTeX sources |
| `notes/`, `specs/` | Detailed proof notes, current scope, plan, version comparison |

[NOTES.md](NOTES.md) maps paper results to Lean declarations.
[specs/STATUS.md](specs/STATUS.md) records the scope and remaining hypothesis.
The root import is [Rank2ModuleSVP.lean](../Rank2ModuleSVP.lean).
Shared infrastructure comes from IdealCVP; `Rank2ModuleSVP.ReductionMap` supplies the prime-scan
interface used by Power2ModuleSVP.

## Verification

The library is sorry-free and adds no axioms. Main theorem axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound`; completeness retains the premise
`hWan : WanPowerSumEstimates`.

Build from the repository root with `lake build Rank2ModuleSVP` (Lean / Mathlib `v4.36.0-rc1`).
If the artifact cache is read-only, use
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache lake build Rank2ModuleSVP`.
