import Power2ModuleSVP.ColoringNative3ConstraintData
import Power2ModuleSVP.ColoringNative3SortCore

/-! Unconditional native certificate for the walk's exact heavy-row ordering. -/
namespace Power2ModuleSVP.ColoringRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
set_option maxHeartbeats 200000

theorem heavyIndices_polytime :
    ComputableTidilyInPolyTime heavyIndices
      (encPair encUnary (encList encColoringRational)) (encList encUnary) := by
  have h : ComputableTidilyInPolyTime
      (fun p : ℕ × List ℚ => (sortWeights p.2).take ((p.1 + 7) / 8))
      (encPair encUnary (encList encColoringRational)) (encList encUnary) := by
    fun_prop
  apply h.of_enc_eq
  intro p
  apply congrArg (encList encUnary)
  rw [heavyIndices, sortWeights_eq_mergeSort]

theorem heavyIndicesNative : HeavyIndicesNativeHypothesis := ⟨heavyIndices_polytime⟩

end Power2ModuleSVP.ColoringRuntime
