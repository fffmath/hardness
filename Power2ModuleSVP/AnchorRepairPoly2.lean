import Power2ModuleSVP.RepairRuntimeLoop
import Power2ModuleSVP.Main

/-! The seed family is the sole remaining premise in the module conclusion. -/
namespace Power2ModuleSVP
open Turing.MultiTapeTM Cslib.Complexity

theorem repair_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × List ℤ => repair a.1 a.2)
    AnchorRepairRuntime.encRepairInput (encList encIntBin) :=
  AnchorRepairRuntime.repair_polytime

theorem rigidAnchorFamily_of_seed (h : SpectralSeedFamilyHypothesis) :
    RigidAnchorFamilyHypothesis :=
  AnchorRepairRuntime.rigidAnchorFamily_of_seed_of_repair_polytime repair_polytime h

theorem moduleSVP_npComplete_of_seed (h : SpectralSeedFamilyHypothesis) :
    NPComplete encSVP ModuleSVPLang :=
  moduleSVP_npComplete_of (rigidAnchorFamily_of_seed h)

end Power2ModuleSVP
