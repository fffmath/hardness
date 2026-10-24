module

public import Power2ModuleSVP.SineKernelProof
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
The endpoint-phase estimate behind the total-variation argument in
`lem:sine-kernel`. The primitive vanishes at every grid endpoint even for
an arbitrary phase. This file proves the estimate for a differentiable
monotone weight; specializing the weights and summing their variations
remain separate obligations.
-/

@[expose] public section

namespace Power2ModuleSVP

noncomputable section

/-- A primitive with the same additive constant at all coarse-grid nodes. -/
def gridSinePrimitive (N : ℕ) (φ u : ℝ) : ℝ :=
  (Real.cos φ - Real.cos (2 * (N : ℝ) * u + φ)) / (2 * N)

theorem gridSinePrimitive_continuous (N : ℕ) (φ : ℝ) :
    Continuous (gridSinePrimitive N φ) := by
  unfold gridSinePrimitive
  fun_prop

theorem gridSinePrimitive_hasDerivAt {N : ℕ} (hN : 0 < N) (φ u : ℝ) :
    HasDerivAt (gridSinePrimitive N φ) (Real.sin (2 * (N : ℝ) * u + φ)) u := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have harg := ((hasDerivAt_id u).const_mul (2 * (N : ℝ))).add_const φ
  have h := ((hasDerivAt_const u (Real.cos φ)).sub harg.cos).div_const (2 * (N : ℝ))
  change HasDerivAt (fun x : ℝ =>
    (Real.cos φ - Real.cos (2 * (N : ℝ) * x + φ)) / (2 * N)) _ u
  convert h using 1 <;> simp [hn]

theorem gridSinePrimitive_grid {N : ℕ} (hN : 0 < N) (φ : ℝ) (m : ℕ) :
    gridSinePrimitive N φ (m * Real.pi / N) = 0 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have harg : 2 * (N : ℝ) * ((m : ℝ) * Real.pi / N) + φ =
      φ + m * (2 * Real.pi) := by field_simp; ring
  simp [gridSinePrimitive, harg, Real.cos_add_nat_mul_two_pi]

theorem gridSinePrimitive_abs_le {N : ℕ} (hN : 0 < N) (φ u : ℝ) :
    |gridSinePrimitive N φ u| ≤ 1 / (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hnum : |Real.cos φ - Real.cos (2 * (N : ℝ) * u + φ)| ≤ 2 := by
    calc
      _ ≤ |Real.cos φ| + |Real.cos (2 * (N : ℝ) * u + φ)| := abs_sub _ _
      _ ≤ 2 := by linarith [Real.abs_cos_le_one φ,
        Real.abs_cos_le_one (2 * (N : ℝ) * u + φ)]
  unfold gridSinePrimitive
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * N)]
  calc
    _ ≤ 2 / (2 * (N : ℝ)) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by field_simp

/-- Integration by parts with a nonnegative derivative gives the endpoint
variation divided by `N`. No phase restriction is needed. -/
theorem grid_sine_integral_le_variation {N : ℕ} (hN : 0 < N)
    {g g' : ℝ → ℝ} (φ : ℝ) (a b : ℕ) (hab : a ≤ b)
    (hg : ∀ u ∈ Set.uIcc (a * Real.pi / N) (b * Real.pi / N),
      HasDerivAt g (g' u) u)
    (hgi : IntervalIntegrable g' MeasureTheory.volume
      (a * Real.pi / N) (b * Real.pi / N))
    (hgpos : ∀ u ∈ Set.Icc (a * Real.pi / N) (b * Real.pi / N), 0 ≤ g' u) :
    |∫ u in (a * Real.pi / N)..(b * Real.pi / N),
      g u * Real.sin (2 * (N : ℝ) * u + φ)| ≤
      (g (b * Real.pi / N) - g (a * Real.pi / N)) / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hab' : (a : ℝ) * Real.pi / N ≤ b * Real.pi / N :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hab) Real.pi_pos.le) hn.le
  have hp := gridSinePrimitive_continuous N φ
  have hsin : Continuous (fun u : ℝ => Real.sin (2 * (N : ℝ) * u + φ)) := by fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg
    (fun u _ => gridSinePrimitive_hasDerivAt hN φ u) hgi
    (hsin.intervalIntegrable _ _)
  simp only [gridSinePrimitive_grid hN, mul_zero, sub_self, zero_sub] at hibp
  rw [hibp, abs_neg]
  have hbound : ∀ u ∈ Set.Icc (a * Real.pi / N) (b * Real.pi / N),
      ‖g' u * gridSinePrimitive N φ u‖ ≤ g' u / N := by
    intro u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hgpos u hu), div_eq_mul_inv]
    simpa only [one_div] using
      mul_le_mul_of_nonneg_left (gridSinePrimitive_abs_le hN φ u) (hgpos u hu)
  have hint := intervalIntegral.norm_integral_le_of_norm_le hab'
    (Filter.Eventually.of_forall fun u hu => hbound u ⟨le_of_lt hu.1, hu.2⟩)
    (hgi.div_const (N : ℝ))
  rw [Real.norm_eq_abs, intervalIntegral.integral_div] at hint
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hg hgi
  rwa [hfund] at hint

end

end Power2ModuleSVP
