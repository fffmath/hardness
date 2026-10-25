import Power2ModuleSVP.AnchorRepairPoly2
import Power2ModuleSVP.FlatSeedMain
import Power2ModuleSVP.FlatFrontend2Main
import Power2ModuleSVP.FlatFrontend3Main
import Power2ModuleSVP.FlatFrontendRuntime
import Power2ModuleSVP.ColoringTrajectory
import Power2ModuleSVP.SineKernelProofDecomposition

/-!
# Assembly of the module-SVP hardness chain

Composes the proved pieces along the AUDIT2 route
`spectralSeedFamily_of_fullColor` with `F := fullColor partialColor`.
Intermediate conditional interfaces; both inputs are now discharged
(`FlatFrontend.markedRunGeometryHypothesis_holds`, FlatFrontend3Main.lean, and
`ColoringRuntime.fullColoringNative_partialColor`, ColoringNative3.lean); the unconditional
theorem is `moduleSVP_npComplete` in MainFinal.lean.
-/

namespace Power2ModuleSVP
open Turing.MultiTapeTM Cslib.Complexity PartialColoringAlg

theorem spectralSeedFamily_of_remaining
    (hG : FlatFrontend.MarkedRunGeometryHypothesis)
    (hN : FullColoringNativeHypothesis partialColor) :
    SpectralSeedFamilyHypothesis :=
  spectralSeedFamily_of_fullColor flatFrontend
    (FlatFrontend.flatFrontend_preparation_of_geometry hG) flatFrontend_runtime
    sineKernelDecompositionHypothesis_holds (fullColor partialColor)
    (fullColoringCorrect_of_partial partialColor partialColor_correct) hN.polytime

theorem moduleSVP_npComplete_of_remaining
    (hG : FlatFrontend.MarkedRunGeometryHypothesis)
    (hN : FullColoringNativeHypothesis partialColor) :
    NPComplete encSVP ModuleSVPLang :=
  moduleSVP_npComplete_of_seed (spectralSeedFamily_of_remaining hG hN)

/-- With the marked-run geometry proved (FlatFrontend3Main.lean), the single remaining input is
the native polynomial-time certificate of the concrete full coloring. -/
theorem moduleSVP_npComplete_of_fullColoringNative
    (hN : FullColoringNativeHypothesis partialColor) :
    NPComplete encSVP ModuleSVPLang :=
  moduleSVP_npComplete_of_remaining FlatFrontend.markedRunGeometryHypothesis_holds hN

end Power2ModuleSVP
