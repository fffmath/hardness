# Rank2ModuleSVP — SVP on rank-2 cyclotomic modules

Lean 4 formalisation of

> Jiaqi Liu, Yansong Feng, Yanbin Pan. **SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules.**
> Target version: **v2**, `paper/rank2svp_v2.pdf` (text: `paper/rank2svp_v2.txt`).
> The v1 source (arXiv:2609.01469, ePrint 2026/1856; `paper/2609.01469.pdf`, `paper/src/`) is background only;
> `specs/v2_diff.md` lists the v1 → v2 changes.

Theorem 1.1 (v2): as q ranges over **odd primes**, decision-SVP (ℓ₂, canonical embedding) on full-rank
free rank-2 submodules of ℤ[ζ_q]² is NP-complete under deterministic polynomial-time many-one
reductions from X3C.

## Main Lean results (namespace `Rank2ModuleSVP`, root `Rank2ModuleSVP.lean`)

| Result | Lean name | File |
| --- | --- | --- |
| NP membership (unconditional) | `moduleSVP_mem_NP : ModuleSVPLang ∈ NP encSVP` | [MembershipCert.lean](MembershipCert.lean) |
| Thm 5.2 exact X3C encoding | `exact_X3C_encoding` | [Reduction.lean](Reduction.lean) |
| Total map correctness, X3C ↔ SVP | `reductionMap_correct (hWan) (x)` | [Main.lean](Main.lean) |
| Outputs satisfy the SVP promises | `reductionMap_wellFormed` | [Main.lean](Main.lean) |
| Polynomial-time map | `ReductionMap.reductionMap_polytime` | [ReductionMapPoly.lean](ReductionMapPoly.lean) |
| X3C ≤ₚ SVP | `x3c_polyTimeReducible_moduleSVP (hWan)` | [Main.lean](Main.lean) |
| **Theorem 1.1** | `moduleSVP_npComplete_of (hWan : WanPowerSumEstimates) : NPComplete encSVP ModuleSVPLang` | [Main.lean](Main.lean) |

The only named mathematical hypothesis is `WanPowerSumEstimates` (`Wan.lean`, passed explicitly; it
needs Weil/Deligne-strength point-count bounds, see `notes/weil-bound-research.md`). The
Bennett–Peikert minimum is proved. All main theorems use only `propext`, `Classical.choice`, and
`Quot.sound`. Corollary 1.2 (search-SVP, one-call Turing reduction) is not formalised.

See [NOTES.md](NOTES.md) and `notes/` for the paper ↔ Lean map, and
[specs/STATUS.md](specs/STATUS.md) for the final scope and remaining hypothesis.
Modules `Rank2ModuleSVP.*` import the shared `IdealCVP` infrastructure.
`Rank2ModuleSVP.ReductionMap` supplies the prime-scan interface used by Power2ModuleSVP.

Build from the repository root with `lake build Rank2ModuleSVP`.
The main theorem keeps `hWan` explicit; NP membership does not depend on it.
