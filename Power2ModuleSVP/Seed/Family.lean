import Power2ModuleSVP.Seed.Assembly
import Power2ModuleSVP.FlatFrontend.Geometry.Certificate
import Power2ModuleSVP.Runtime.FlatFrontend.Certificate
import Power2ModuleSVP.Coloring.Trajectory.Basic
import Power2ModuleSVP.Seed.SineKernel.Decomposition
import Power2ModuleSVP.Runtime.Coloring.Certificate

/-!
# The certified spectral seed family

Assemble the rational frontend, sine kernel, and concrete full-coloring
certificates of paper Appendix A, Theorem 5. The seed-to-anchor interface
then supplies the final module-SVP theorem.

Paper: `paper/power2svp.pdf`, Appendix A (Theorem 5, the deterministic flat seed).
-/

namespace Power2ModuleSVP
open Turing.MultiTapeTM Cslib.Complexity PartialColoringAlg

/-- The concrete frontend and coloring program give a uniform spectral seed family. -/
theorem spectralSeedFamily_holds : SpectralSeedFamilyHypothesis :=
  spectralSeedFamily_of_fullColor flatFrontend
    (FlatFrontend.flatFrontend_preparation_of_geometry
      FlatFrontend.markedRunGeometryHypothesis_holds) flatFrontend_runtime
    sineKernelDecompositionHypothesis_holds (fullColor partialColor)
    (fullColoringCorrect_of_partial partialColor partialColor_correct)
    ColoringRuntime.fullColoringNative_partialColor.polytime

end Power2ModuleSVP
