import Hardness.Complexity.CompileBridge

/-! # The remaining compiler runtime obligation

Correctness of the executable reference compiler is proved. A native runtime
certificate for its finite enumeration / prime search, or a certified equivalent
bounded list implementation, remains open. The hypothesis here is a runtime
statement about the specified function, not an NP-hardness assumption.
-/
namespace Hardness
open Turing.MultiTapeTM Cslib.Complexity

/-- The semantic compiler becomes a Karp reduction once its runtime is certified. -/
theorem polyTimeReducible_Masked_CVP
    (hcompilePoly : ComputableTidilyInPolyTime compileList encMasked encCVP) :
    PolyTimeReducible encMasked encCVP {S | S.Feasible} PrincipalCVP :=
  ⟨compileList, hcompilePoly, compileList_correct⟩

end Hardness
