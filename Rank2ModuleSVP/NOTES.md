# Rank2ModuleSVP — paper v2 ↔ Lean map

Paper: `paper/rank2svp_v2.pdf`. Detailed per-round maps are in `notes/` (round 2 onwards; files
named after the job). Namespace `Rank2ModuleSVP` unless stated otherwise.

| Paper v2 | Lean | File |
| --- | --- | --- |
| Model of ℤ[ζ_q], canonical norm | `Cyclotomic`, `classOf`, `normSq`, `pairNormSq`, `ramifiedIdeal` | `PrimeCyclotomic.lean` |
| Problem, encoding, well-formedness (odd prime q) | `SVPInput`, `SVPInput.WellFormed`, `SVPYes`, `ModuleSVPLang`, `encSVP` | `Problem.lean` |
| Descent, ideal preimage, coset syndromes | `cyclotomic_descent`, `ideal_preimage`, `ramified_coset_syndrome` | `Descent*.lean` |
| Bennett–Peikert minimum (proved) | `bennettPeikertMinimum`, `ramifiedIdeal_minimum` | `BennettPeikert.lean` |
| Wan point counts (**named hypothesis**) | `WanPowerSumEstimates` | `Wan.lean` |
| Thm 3.4, ratio bound, Thm 4.4 | `uniform_completions_div`, `fixed_coordinate_ratio_div`, `admissible_representative` | `Completions.lean`, `Asymptotics*.lean`, `Admissible.lean` |
| Thm 3.7 separation | `separation_distance_v2`, `sepCenter` | `RobustCenter.lean` |
| Integral checker, Lemma 4.2, Thm 4.3 | `Checker.U/V/Q/g`, `Checker.checker_score_bounds`, `checker_lower`, `checker_upper_of_clean` | `Checker*.lean` |
| Cor 4.5, Lemma 5.1, Thm 5.2 | `red_corollary_4_5`, `red_global_stability`, `red_completeness`, `red_soundness`, `exact_X3C_encoding` | `Reduction*.lean` |
| §5.3 map, fixed instances, Bertrand prime scan | `ReductionMap.reductionMap`, `fixedYes_mem`, `fixedNo_not_mem`, `primeScan_*`, `reductionMap_m₁/m₂/S` | `ReductionMap*.lean` |
| §5.3 polynomial time | `ReductionMap.reductionMap_polytime` | `ReductionMapPoly.lean` |
| §5.4 NP membership | `moduleSVP_mem_NP` | `Membership*.lean` |
| Theorem 1.1 | `reductionMap_correct`, `x3c_polyTimeReducible_moduleSVP`, `moduleSVP_npComplete_of` | `Main.lean` |

Corollary 1.2 (search-SVP under one-call Turing reductions) is not formalised.
