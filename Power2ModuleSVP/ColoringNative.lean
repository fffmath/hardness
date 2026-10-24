import Power2ModuleSVP.ColoringNativeArithmetic
import Power2ModuleSVP.ColoringNativeProjector
import Power2ModuleSVP.ColoringNativeRecursion

/-!
Native coloring runtime components and denominator invariants.

The imported modules prove binary square-root and rational initialization
certificates, an exact native implementation of one projector stage,
additive coordinate-denominator growth conditional on a direction bound,
fixed dyadic weight denominators, and full-coloring output-size facts.

Neither `PartialColoringAlg.PartialColoringNativeHypothesis` nor
`FullColoringNativeHypothesis PartialColoringAlg.partialColor` is discharged
here. In particular, a polynomial number of calls to the projector-stage
certificate does not supply the missing uniform projector bit bound.
-/
