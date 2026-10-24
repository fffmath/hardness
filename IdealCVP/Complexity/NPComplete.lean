import IdealCVP.Complexity.SatToMasked
import IdealCVP.Complexity.Verifier
import IdealCVP.Complexity.CompilePolyTime

/-! # Unconditional NP-completeness of principal cyclotomic CVP

The native complexitylib chain is ExactThreeSAT → masked Boolean equations →
principal CVP. Both reductions and NP membership have proved runtime certificates.
-/
namespace IdealCVP
open Cslib.Complexity Turing.MultiTapeTM

/-- NP-hardness from Cook–Levin, the SAT gadget, and the cubic list compiler. -/
theorem principalCVP_npHard : NPHard encCVP PrincipalCVP :=
  maskedSys_npHard.trans polyTimeReducible_Masked_CVP

/-- Exact principal-ideal CVP in power-of-two cyclotomic dimension, with signed
binary integer data, is NP-complete without additional hypotheses. -/
theorem principalCVP_npComplete : NPComplete encCVP PrincipalCVP :=
  ⟨principalCVP_mem_NP, principalCVP_npHard⟩

/-- The former conditional reference-compiler hardness theorem. -/
theorem principalCVP_npHard_of_compilePoly
    (hcompilePoly : ComputableTidilyInPolyTime compileList encMasked encCVP) :
    NPHard encCVP PrincipalCVP :=
  maskedSys_npHard.trans (polyTimeReducible_Masked_CVP_of_compilePoly hcompilePoly)

/-- The former conditional headline, retained under an explicit name. -/
theorem principalCVP_npComplete_of_compilePoly
    (hcompilePoly : ComputableTidilyInPolyTime compileList encMasked encCVP) :
    NPComplete encCVP PrincipalCVP :=
  ⟨principalCVP_mem_NP, principalCVP_npHard_of_compilePoly hcompilePoly⟩

/-- The paper's X3C route, for any supplied encoding and native runtime
certificate. No X3C hardness theorem is postulated in this project. -/
theorem principalCVP_npHard_of_X3C {encX3C : X3CInstance ↪ List Bool}
    (hX3C : NPHard encX3C {I | I.HasExactCover})
    (hpolyX3C : ComputableTidilyInPolyTime (fun I => toCVPInput (x3cToCVP I)) encX3C encCVP) :
    NPHard encCVP PrincipalCVP := by
  apply hX3C.trans
  refine ⟨(fun I => toCVPInput (x3cToCVP I)), hpolyX3C, fun I => ?_⟩
  exact (x3c_correct I).trans (toCVPInput_mem_iff (x3cToCVP I)).symm

end IdealCVP
