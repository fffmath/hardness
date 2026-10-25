import IdealCVP.Complexity.CompileFastPolyTime

/-! # Native polynomial-time reduction from masked systems to principal CVP

The cubic list compiler has unconditional correctness and runtime certificates.
The original reference compiler's conditional interface is retained separately.
-/

namespace IdealCVP

open Turing.MultiTapeTM Cslib.Complexity

/-- The former reference-compiler interface, retained for compatibility. -/
theorem polyTimeReducible_Masked_CVP_of_compilePoly
    (hcompilePoly : ComputableTidilyInPolyTime compileList encMasked encCVP) :
    PolyTimeReducible encMasked encCVP {S | S.Feasible} PrincipalCVP :=
  ⟨compileList, hcompilePoly, compileList_correct⟩

/-- The total cubic list compiler is an unconditional Karp reduction. -/
theorem polyTimeReducible_Masked_CVP :
    PolyTimeReducible encMasked encCVP {S | S.Feasible} PrincipalCVP :=
  ⟨compileFast, poly_compileFast, compileFast_correct⟩

end IdealCVP
