import Power2ModuleSVP.FlatFrontend.Enclosure.Threshold
import Power2ModuleSVP.FlatFrontend.Enclosure.Runs

/-!
# Preparation from marked-run geometry

Assemble rational enclosure estimates into the frontend preparation contract, conditional on
geometry of the computed runs. FlatFrontend/Geometry/Certificate.lean discharges that geometric
premise.

Paper: `paper/power2svp.pdf`, Appendix A.3 (rational enclosures and the two rounding steps).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
noncomputable section

/-- Every enclosure obligation follows from geometry of the computed runs.
In particular, no separate precision or first-coloring estimate is assumed. -/
theorem enclosure_of_geometry {d : ℕ} (G : GeometryCertificate d)
    (hN : 0 < seedN d) : EnclosureHypothesis G.kernelIntervals where
  fractional_bound := fun α hα j =>
    fractional_bound_of_entries G.kernelIntervals hN
      (by exact_mod_cast kernelError_nonnegative (seedN d))
      (geometry_kernel_entries G) (firstThreshold_margin hN G.count) α hα j
  fractional_error := fun α hα j => fractional_error G α hα.1 j
  derivative_error := fun k ell _ j => derivative_error k ell j

/-- The geometric preparation contract for this implementation: the
actual computed marked runs satisfy the geometric certificate. It asserts
neither enclosure estimates nor the spectral seed conclusion. -/
def MarkedRunGeometryHypothesis : Prop :=
  ∀ d, Dyadic d → 2 ^ 512 ≤ d → MarkedRunEstimates d

theorem preparationHypothesis_of_geometry (hG : MarkedRunGeometryHypothesis) :
    PreparationHypothesis := by
  constructor
  intro d hd hlarge
  let G := geometryCertificate_of_estimates (hG d hd hlarge)
  have hN : 0 < seedN d := by have := (seed_degree_bounds hlarge).1; omega
  exact ⟨G, enclosure_of_geometry G hN⟩

/-- Conditional only on the computed-run geometry, rather than on any of the
three enclosure obligations in the original preparation interface. -/
theorem flatFrontend_preparation_of_geometry (hG : MarkedRunGeometryHypothesis) :
    FlatSeedPreparationHypothesis flatFrontend :=
  preparation_of (preparationHypothesis_of_geometry hG)

end
end FlatFrontend
end Power2ModuleSVP
