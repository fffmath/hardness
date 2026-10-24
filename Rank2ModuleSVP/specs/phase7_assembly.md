JOB r2m-p7-assembly. You own: NEW file Rank2ModuleSVP/Main.lean (namespace Rank2ModuleSVP) and
notes/r7-assembly.md only. Do not edit any other Lean file (add helper lemmas in Main.lean).
GOALS (paper v2 Theorem 1.1):
1. Explicit constants mainK0 ≥ redK0, mainC0 ≥ redC0 (≥ 1), and
   theorem reductionMap_correct (hWan : WanPowerSumEstimates) (x) :
     x ∈ IdealCVP.X3CLang ↔ ReductionMap.reductionMap mainK0 mainC0 x ∈ ModuleSVPLang
   Branches: malformed / empty-universe / zero-row via reductionMap_*_correct; nondegenerate branch:
   instantiate exact_X3C_encoding with k = mapK, q = mapped prime, Sidon positions = IdealCVP.cubic
   (bound α ≤ 3n³+n, so τ = O(n³) and 4τ·3M < q follows from q ≥ (2k)^C0, k ≥ (n+2)², M ≤ n),
   n+2 ≤ √k from k ≥ (n+2)², and match redM1/redM2/redS with reductionMap_m₁/m₂/S (powerPair) and
   WellFormed (odd prime, lengths, nonzero determinant redDet_ne_zero, threshold ≥ 0 using
   3·I.q ≤ W from no zero rows).
2. theorem moduleSVP_npComplete_of_polytime (hWan) (hpoly : ComputableTidilyInPolyTime
     (ReductionMap.reductionMap mainK0 mainC0) IdealCVP.encX3C encSVP) :
     NPComplete encSVP ModuleSVPLang   (use moduleSVP_mem_NP and IdealCVP's X3C NP-hardness;
   match the exact complexitylib signatures).
   A parallel job proves `ReductionMap.reductionMap_polytime` in ReductionMapPoly.lean; do NOT import it
   (it may not exist yet); the integrator will add the 2-line final corollary.
3. Optional if time permits: Corollary 1.2 (search version / Turing reduction) only if it can be
   stated faithfully in complexitylib terms; otherwise document why skipped.
Write notes/r7-assembly.md (paper label → Lean name, hypotheses).
