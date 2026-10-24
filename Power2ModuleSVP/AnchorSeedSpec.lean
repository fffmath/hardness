import Power2ModuleSVP.Anchor
import IdealCVP.Canonical

/-!
The smaller uniform boundary for the anchor construction. Only evaluations at
the negacyclic roots are required, rather than a lower bound on the full circle.
The constant is the one used in the private manuscript's `thm:spectral-seed`.
-/
namespace Power2ModuleSVP

/-- The fixed rational spectral constant, represented without negative natural powers. -/
def seedConstant : ℚ := 1 / 2 ^ 252

/-- Evaluation of the coefficient representative (also meaningful in degree zero). -/
def coeffEval {d : ℕ} (s : Coeff d) (z : ℂ) : ℂ :=
  ∑ i : Fin d, (s i : ℂ) * z ^ i.val

/-- A sign word with the required lower bound at every root of `X^d + 1`. -/
def SpectralSeed (d : ℕ) (s : Coeff d) : Prop :=
  Signs s ∧ ∀ z : ℂ, z ^ d = -1 →
    (seedConstant : ℝ) * Real.sqrt d ≤ ‖coeffEval s z‖

/-- One uniform native machine produces spectral seeds in polynomial time in
unary degree above a fixed dyadic cutoff. The manuscript supplies cutoff
exponent 512; allowing an arbitrary fixed exponent matches the anchor API. -/
structure SpectralSeedFamilyHypothesis : Prop where
  exists_family :
    ∃ (k0 : ℕ) (s : ℕ → List ℤ),
      Turing.MultiTapeTM.ComputableTidilyInPolyTime s
        Turing.MultiTapeTM.encUnary
        (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encIntBin) ∧
      ∀ d : ℕ, Dyadic d → 2 ^ k0 ≤ d →
        (s d).length = d ∧ SpectralSeed d (IdealCVP.ofList (d := d) (s d))

theorem seedConstant_pos : 0 < seedConstant := by
  unfold seedConstant
  positivity

theorem SpectralSeed.signs {d : ℕ} {s : Coeff d} (hs : SpectralSeed d s) :
    Signs s := hs.1

end Power2ModuleSVP
