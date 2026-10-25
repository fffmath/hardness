import Power2ModuleSVP.Reduction.PolyTime
import Power2ModuleSVP.Membership.NP

/-!
# Conditional module completeness and the integral gap

Compose the certified 3SAT reduction with a uniform rigid anchor family. The unconditional coset
and module completeness theorems are in Main.lean. The stored module reduction also has first
minimum one on YES inputs and norm at least two on NO inputs.

Paper: `paper/power2svp.pdf`, Sections 1.1 and 3–5 (Theorem 1 and the composed reductions).
-/
namespace Power2ModuleSVP
open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM

/-- A uniform rigid anchor family gives NP-hardness of module SVP. -/
theorem moduleSVP_npHard_of (hJ : RigidAnchorFamilyHypothesis) :
    NPHard encSVP ModuleSVPLang :=
  ThreeSAT_npHard.trans (threeSAT_polyTimeReducible_moduleSVP_of hJ)

/-- A uniform rigid anchor family gives NP-completeness of module SVP. -/
theorem moduleSVP_npComplete_of (hJ : RigidAnchorFamilyHypothesis) :
    NPComplete encSVP ModuleSVPLang :=
  ⟨moduleSVP_mem_NP, moduleSVP_npHard_of hJ⟩

/-- On the actual stored reduction images, YES attains first minimum one,
and every nonzero vector on NO has coefficient maximum at least two. -/
theorem moduleReduction_gap (k0 : ℕ) (J : ℕ → List ℤ)
    (hfamily : ∀ d, Dyadic d → 2 ^ k0 ≤ d →
      (J d).length = d ∧ Signs (IdealCVP.ofList (d := d) (J d)) ∧
        Rigid (IdealCVP.ofList (d := d) (J d))) (f : CNF ℕ) :
    let x := moduleReduction k0 J f
    let a := (IdealCVP.ofList (d := x.1) x.2.1.1,
      IdealCVP.ofList (d := x.1) x.2.1.2)
    let b := (IdealCVP.ofList (d := x.1) x.2.2.1,
      IdealCVP.ofList (d := x.1) x.2.2.2)
    (f ∈ ThreeSAT → FirstMinimum a b 1) ∧
    (f ∉ ThreeSAT → ∀ u v, moduleVector a b u v ≠ 0 →
      2 ≤ pairSup (moduleVector a b u v)) := by
  dsimp only
  have hc := moduleReduction_correct k0 J hfamily f
  constructor
  · intro hf
    obtain ⟨u, v, hn, h1, h2⟩ := (hc.mp hf).2
    exact ⟨⟨u, v, hn, Nat.le_antisymm ((pairSup_le_one_iff _).mpr ⟨h1, h2⟩)
      (one_le_pairSup hn)⟩, fun _ _ hn => one_le_pairSup hn⟩
  · intro hf u v hn
    by_contra! hb
    have hcube := (pairSup_le_one_iff _).mp (Nat.le_of_lt_succ hb)
    exact hf (hc.mpr ⟨moduleReduction_wellFormed k0 J hfamily f,
      u, v, hn, hcube.1, hcube.2⟩)

end Power2ModuleSVP
