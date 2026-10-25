import Power2ModuleSVP.Runtime.Repair.Loop
import Power2ModuleSVP.Reduction.Completeness

/-!
# From spectral seeds to module hardness

Compose deterministic repair with the spectral seed family contract. The exported seed-to-anchor
and seed-to-completeness interfaces document the construction in paper Section 5.

Paper: `paper/power2svp.pdf`, Section 5 (Theorems 3–4 and deterministic anchor repair).
-/
namespace Power2ModuleSVP
open Turing.MultiTapeTM Cslib.Complexity

theorem repair_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × List ℤ => repair a.1 a.2)
    AnchorRepairRuntime.encRepairInput (encList encIntBin) :=
  AnchorRepairRuntime.repair_polytime

/-- Deterministic repair turns a uniform spectral seed family into rigid anchors. -/
theorem rigidAnchorFamily_of_seed (h : SpectralSeedFamilyHypothesis) :
    RigidAnchorFamilyHypothesis :=
  AnchorRepairRuntime.rigidAnchorFamily_of_seed_of_repair_polytime repair_polytime h

/-- A uniform spectral seed family gives NP-completeness of module SVP. -/
theorem moduleSVP_npComplete_of_seed (h : SpectralSeedFamilyHypothesis) :
    NPComplete encSVP ModuleSVPLang :=
  moduleSVP_npComplete_of (rigidAnchorFamily_of_seed h)

end Power2ModuleSVP
