module

public import Power2ModuleSVP.SineKernelProofCorrection
public import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic

/-!
Certified initial sine-integral values for `lem:sine-kernel`. Finite Taylor
bounds are obtained from the Lagrange remainder and the global cosine
bound, without assuming an infinite-series remainder estimate.
-/

@[expose] public section

namespace Power2ModuleSVP

noncomputable section

theorem seed_sin_le_taylor_five {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.sin) (n := 4) (x₀ := 0) (x := x) hx.ne Real.contDiff_sin.contDiffOn
  have ht : taylorWithinEval Real.sin 4 (Set.uIcc 0 x) 0 x = x - x ^ 3 / 6 := by
    rw [taylor_within_apply, Set.uIcc_of_le hx.le]
    simp_rw [Real.iteratedDerivWithin_sin_Icc _ hx ⟨le_rfl, hx.le⟩]
    norm_num [Finset.sum_range_succ]
    ring
  rw [ht] at heq
  norm_num [show (5 : ℕ) = 2 * 2 + 1 by rfl, Real.iteratedDeriv_odd_sin] at heq
  have hm := mul_le_mul_of_nonneg_right (Real.cos_le_one y) (pow_nonneg hx.le 5)
  nlinarith

theorem seed_sin_ge_taylor_fifteen {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 -
      x ^ 11 / 39916800 + x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 ≤
      Real.sin x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.sin) (n := 14) (x₀ := 0) (x := x) hx.ne Real.contDiff_sin.contDiffOn
  have ht : taylorWithinEval Real.sin 14 (Set.uIcc 0 x) 0 x =
      x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 -
        x ^ 11 / 39916800 + x ^ 13 / 6227020800 := by
    rw [taylor_within_apply, Set.uIcc_of_le hx.le]
    simp_rw [Real.iteratedDerivWithin_sin_Icc _ hx ⟨le_rfl, hx.le⟩]
    norm_num [Finset.sum_range_succ]
    ring
  rw [ht] at heq
  norm_num [show (15 : ℕ) = 2 * 7 + 1 by rfl, Real.iteratedDeriv_odd_sin] at heq
  have hm := mul_le_mul_of_nonneg_right (Real.cos_le_one y) (pow_nonneg hx.le 15)
  nlinarith

theorem seed_sinc_le_taylor_four {x : ℝ} (hx : 0 ≤ x) :
    Real.sinc x ≤ 1 - x ^ 2 / 6 + x ^ 4 / 120 := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rw [Real.sinc_of_ne_zero hx.ne']
  apply (div_le_iff₀ hx).2
  nlinarith [seed_sin_le_taylor_five hx.le]

theorem seed_sinc_ge_taylor_fourteen {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040 + x ^ 8 / 362880 -
      x ^ 10 / 39916800 + x ^ 12 / 6227020800 - x ^ 14 / 1307674368000 ≤
        Real.sinc x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rw [Real.sinc_of_ne_zero hx.ne']
  apply (le_div_iff₀ hx).2
  nlinarith [seed_sin_ge_taylor_fifteen hx.le]

theorem seedSineIntegral_le_taylor_five {x : ℝ} (hx : 0 ≤ x) :
    seedSineIntegral x ≤ x - x ^ 3 / 18 + x ^ 5 / 600 := by
  have hi := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hx
    (Real.continuous_sinc.intervalIntegrable 0 x)
    ((by fun_prop : Continuous (fun u : ℝ => 1 - u ^ 2 / 6 + u ^ 4 / 120)).intervalIntegrable 0 x)
    (fun u hu => seed_sinc_le_taylor_four hu.1)
  change seedSineIntegral x ≤ _ at hi
  convert hi using 1
  symm
  simp (disch := apply Continuous.intervalIntegrable; fun_prop)
    [intervalIntegral.integral_sub, intervalIntegral.integral_add,
      intervalIntegral.integral_div, integral_pow, smul_eq_mul]
  ring

theorem seedSineIntegral_ge_taylor_fifteen {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 18 + x ^ 5 / 600 - x ^ 7 / 35280 + x ^ 9 / 3265920 -
      x ^ 11 / 439084800 + x ^ 13 / 80951270400 - x ^ 15 / 19615115520000 ≤
        seedSineIntegral x := by
  have hi := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hx
    ((by fun_prop : Continuous (fun u : ℝ =>
      1 - u ^ 2 / 6 + u ^ 4 / 120 - u ^ 6 / 5040 + u ^ 8 / 362880 -
        u ^ 10 / 39916800 + u ^ 12 / 6227020800 - u ^ 14 / 1307674368000)).intervalIntegrable 0 x)
    (Real.continuous_sinc.intervalIntegrable 0 x)
    (fun u hu => seed_sinc_ge_taylor_fourteen hu.1)
  change _ ≤ seedSineIntegral x at hi
  convert hi using 1
  simp (disch := apply Continuous.intervalIntegrable; fun_prop)
    [intervalIntegral.integral_sub, intervalIntegral.integral_add,
      intervalIntegral.integral_div, integral_pow, smul_eq_mul]
  ring

theorem seedSineIntegral_pi_lt_two : seedSineIntegral Real.pi < 2 := by
  have hi := seedSineIntegral_le_taylor_five Real.pi_pos.le
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3.14) Real.pi_gt_d2.le 3
  have h5 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 5
  norm_num at h3 h5
  linarith [Real.pi_lt_d2]

theorem seedSineIntegral_two_pi_gt_four_thirds :
    4 / 3 < seedSineIntegral (2 * Real.pi) := by
  have hi := seedSineIntegral_ge_taylor_fifteen (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  have hl : (6.283 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_d4]
  have hu : 2 * Real.pi ≤ (6.2832 : ℝ) := by linarith [Real.pi_lt_d4]
  have hp : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h3 := pow_le_pow_left₀ hp hu 3
  have h5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6.283) hl 5
  have h7 := pow_le_pow_left₀ hp hu 7
  have h9 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6.283) hl 9
  have h11 := pow_le_pow_left₀ hp hu 11
  have h13 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6.283) hl 13
  have h15 := pow_le_pow_left₀ hp hu 15
  norm_num at h3 h5 h7 h9 h11 h13 h15
  linarith

end

end Power2ModuleSVP
