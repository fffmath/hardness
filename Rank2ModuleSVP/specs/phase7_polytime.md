JOB r2m-p7-polytime. You own: NEW file Rank2ModuleSVP/ReductionMapPoly.lean (namespace
Rank2ModuleSVP.ReductionMap), and you MAY edit ReductionMap.lean / ReductionMapAux.lean (do not break
any existing public theorem statement; Main.lean (another job) uses them). Do not touch Reduction*.lean
or Main.lean.
GOAL: prove, for every K0 and every C0 ≥ 1 (or all C0),
  theorem reductionMap_polytime (K0 C0 : ℕ) :
    ComputableTidilyInPolyTime (reductionMap K0 C0) IdealCVP.encX3C encSVP
following "Remaining work" in notes/r6-map.md: (1) compile ringPow with variable exponent/dimension
using ringPow_abs_bound for intermediate size bounds; (2) rewrite the gList/vList loops as plain
List.range/getD loops on X3CList, prove equality with the existing definitions, certify them with
poly_singleList/poly_sumLists/list arithmetic; (3) compose with parameter, threshold, prime-scan and
preprocessing certificates. Then also state
  theorem reductionMap_polyTimeReducible_of_correct (K0 C0) (h : ∀ x, x ∈ IdealCVP.X3CLang ↔
    reductionMap K0 C0 x ∈ ModuleSVPLang) : PolyTimeReducible ... (use the exact complexitylib form).
If the full certificate is out of reach, prove as much as possible as separately named lemmas and
document precisely what remains; never assert unproved statements. Write notes/r7-polytime.md.
