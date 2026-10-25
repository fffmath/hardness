# Rank2ModuleSVP — final status

The target is paper v2, `paper/rank2svp_v2.pdf` (text: `paper/rank2svp_v2.txt`).

- `moduleSVP_mem_NP` in `MembershipCert.lean` proves unconditional NP membership.
- `exact_X3C_encoding` in `Reduction.lean` proves the core equivalence of Theorem 5.2.
- `ReductionMap.reductionMap` in `ReductionMap.lean` is a total executable map from list X3C.
- `ReductionMap.reductionMap_polytime` in `ReductionMapPoly.lean` certifies polynomial time.
- `reductionMap_correct` and `reductionMap_wellFormed` in `Main.lean` connect the map to the language.
- `moduleSVP_npComplete_of (hWan : WanPowerSumEstimates)` in `Main.lean` proves Theorem 1.1.

The sole named mathematical hypothesis is `WanPowerSumEstimates` (`Wan.lean`).
The Bennett–Peikert minimum and the remaining reduction estimates are proved.
The main theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
Corollary 1.2 (search-SVP with one oracle call) is not formalised.

See `README.md` for statements and `NOTES.md` for the paper-to-Lean map.
The retained plan and version comparison are `specs/PLAN.md` and `specs/v2_diff.md`;
`notes/` records the detailed arguments. The v1 paper sources are background only.
