import Hardness.Complexity.SatToMasked
import Hardness.Complexity.Verifier
import Hardness.Complexity.CompilePolyTime

/-! # Principal cyclotomic CVP: the conditional complexity headline

NP membership and ExactThreeSAT-to-masked hardness are unconditional. The only
remaining hypothesis is a native polynomial-time certificate for the specified
executable compiler. No custom axioms are used.
-/
namespace Hardness
open Cslib.Complexity Turing.MultiTapeTM

/-- NP-hardness from Cook–Levin and the proved gadget/compiler correctness,
conditional only on certifying the reference compiler's runtime. -/
theorem principalCVP_npHard
    (hcompilePoly : ComputableTidilyInPolyTime compileList encMasked encCVP) :
    NPHard encCVP PrincipalCVP :=
  maskedSys_npHard.trans (polyTimeReducible_Masked_CVP hcompilePoly)

/-- Exact principal-ideal CVP in power-of-two cyclotomic dimension, with signed
binary integer data, is NP-complete once the compiler runtime is certified. -/
theorem principalCVP_npComplete
    (hcompilePoly : ComputableTidilyInPolyTime compileList encMasked encCVP) :
    NPComplete encCVP PrincipalCVP :=
  ⟨principalCVP_mem_NP, principalCVP_npHard hcompilePoly⟩

/-- The paper's X3C route, for any supplied encoding and native runtime
certificate. No X3C hardness theorem is postulated in this project. -/
theorem principalCVP_npHard_of_X3C {encX3C : X3CInstance ↪ List Bool}
    (hX3C : NPHard encX3C {I | I.HasExactCover})
    (hpolyX3C : ComputableTidilyInPolyTime (fun I => toCVPInput (x3cToCVP I)) encX3C encCVP) :
    NPHard encCVP PrincipalCVP := by
  apply hX3C.trans
  refine ⟨(fun I => toCVPInput (x3cToCVP I)), hpolyX3C, fun I => ?_⟩
  exact (x3c_correct I).trans (toCVPInput_mem_iff (x3cToCVP I)).symm

end Hardness
