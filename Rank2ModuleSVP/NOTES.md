# Rank2ModuleSVP — paper v2 ↔ Lean map

Target: [paper v2](paper/rank2svp_v2.pdf), with searchable
[text](paper/rank2svp_v2.txt). Names below are in `Rank2ModuleSVP` unless qualified.
The root import is `Rank2ModuleSVP.lean`. Detailed proof notes remain in `notes/`.

| Paper v2 | Lean declarations | Files |
| --- | --- | --- |
| §2, cyclotomic coefficients and canonical norm | `Cyclotomic`, `classOf`, `normSq`, `pairNormSq`, `ramifiedIdeal` | [PrimeCyclotomic.lean](PrimeCyclotomic.lean) |
| §1.1, §5.4, input promises and language | `SVPInput`, `SVPInput.WellFormed`, `SVPYes`, `ModuleSVPLang`, `encSVP` | [Problem.lean](Problem.lean) |
| §3.3, Lemmas 3.5–3.6, sparse vectors and polynomials | `sparse_tools_i`, `sparse_tools_ii` | [Sparse.lean](Sparse.lean), [SparsePolynomial.lean](SparsePolynomial.lean) |
| §3.1, descent and ideal preimage (Theorem 3.2) | `cyclotomic_descent`, `cyclotomicDescentEquiv`, `ideal_preimage`, `total_ramification`, `syndrome_surjective_fixed_sum`, `ramified_coset_syndrome` | [Descent.lean](Descent.lean), [Descent2.lean](Descent2.lean) |
| §3.1, Bennett–Peikert minimum | `bennettPeikertMinimum`, `ramifiedIdeal_minimum` | [BennettPeikert.lean](BennettPeikert.lean) |
| §3.2, Wan point counts (explicit hypothesis) | `WanPowerSumEstimates`, `wan_good_count_bounds` | [Wan.lean](Wan.lean) |
| §3.2, Theorem 3.4 and coordinate ratios | `uniform_completions_div`, `fixed_coordinate_ratio_div` | [Completions.lean](Completions.lean), [AsymptoticsAux.lean](AsymptoticsAux.lean), [Asymptotics.lean](Asymptotics.lean) |
| §3.3, Theorem 3.7, ideal-coset separation | `sparse_tools_i_v2`, `sepCenter`, `separation_distance_v2` | [RobustCenter.lean](RobustCenter.lean) |
| §4, integral checker, Lemma 4.2 and Theorem 4.3 | `Checker.U`, `Checker.V`, `Checker.Q`, `Checker.g`, `Checker.checker_score_bounds`, `Checker.checker_lower`, `Checker.checker_upper_of_clean` | [CheckerAux.lean](CheckerAux.lean), [Checker.lean](Checker.lean) |
| §4, Theorem 4.4, admissible completions | `admissible_representative` | [Admissible.lean](Admissible.lean) |
| §4–5, Corollary 4.5, Lemma 5.1 and Theorem 5.2 | `red_corollary_4_5`, `red_global_stability`, `red_completeness`, `red_soundness`, `exact_X3C_encoding` | [ReductionAux.lean](ReductionAux.lean), [Reduction.lean](Reduction.lean) |
| §5.3, arithmetic and fixed instances | `ReductionMap.coreInput`, `ReductionMap.fixedYes_mem`, `ReductionMap.fixedNo_not_mem` | [ReductionMapAux.lean](ReductionMapAux.lean) |
| §5.3, total map and Bertrand prime scan | `ReductionMap.reductionMap`, `ReductionMap.primeScan`, `ReductionMap.reductionMap_m₁`, `ReductionMap.reductionMap_m₂`, `ReductionMap.reductionMap_S` | [ReductionMap.lean](ReductionMap.lean) |
| §5.3, polynomial running time | `ReductionMap.reductionMap_polytime` | [ReductionMapPoly.lean](ReductionMapPoly.lean) |
| §5.4, polynomial certificate bounds and NP membership | `moduleSVP_mem_NP` | [MembershipAux.lean](MembershipAux.lean), [Membership.lean](Membership.lean), [MembershipCert.lean](MembershipCert.lean) |
| Theorem 1.1, semantic and complexity assembly | `reductionMap_correct`, `reductionMap_wellFormed`, `x3c_polyTimeReducible_moduleSVP`, `moduleSVP_npComplete_of` | [Main.lean](Main.lean) |

`moduleSVP_npComplete_of` retains the explicit premise `hWan : WanPowerSumEstimates`.
NP membership is unconditional. The named estimate is discussed in
[notes/weil-bound-research.md](notes/weil-bound-research.md).
Corollary 1.2 (search-SVP under one-call Turing reductions) is not formalised.

`Rank2ModuleSVP.ReductionMap` also exports the prime-scan interface used by Power2ModuleSVP.
The older paper and TeX source in `paper/` are retained for comparison; see
[specs/v2_diff.md](specs/v2_diff.md). Historical round notes describe intermediate interfaces;
the declarations and paths in the table above describe the final formalisation.
