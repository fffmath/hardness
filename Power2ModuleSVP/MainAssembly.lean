import Power2ModuleSVP.AnchorRepairPoly2
import Power2ModuleSVP.FlatSeedMain
import Power2ModuleSVP.FlatFrontend2Main
import Power2ModuleSVP.FlatFrontendRuntime
import Power2ModuleSVP.ColoringTrajectory
import Power2ModuleSVP.SineKernelProofDecomposition

/-!
# Assembly of the module-SVP hardness chain

Composes the proved pieces along the AUDIT2 route
`spectralSeedFamily_of_fullColor` with `F := fullColor partialColor`.
The two remaining inputs are exactly
* `FlatFrontend.MarkedRunGeometryHypothesis` (marked-run geometry of the concrete frontend), and
* `FullColoringNativeHypothesis partialColor` (native polynomial time of the concrete
  full coloring).
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

end Power2ModuleSVP
