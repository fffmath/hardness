module

public import Power2ModuleSVP.SineKernelProofTail
public import Power2ModuleSVP.SineKernelProofReflected
public import Power2ModuleSVP.SineKernelProofNear
import Mathlib.Tactic

/-!
Unconditional discharge of the local-and-tail decomposition for the odd
sine kernel. All local terms use the continuous sinc function, so the
observation point and interval endpoints require no exceptional values.
-/

@[expose] public section
namespace Power2ModuleSVP
open scoped BigOperators
noncomputable section

private theorem kernel_interval_order {N J : ℕ} (I : SeedKernelIntervals N J)
    (hN : 0 < N) (i : Fin J) : I.leftAngle i ≤ I.rightAngle i := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold SeedKernelIntervals.leftAngle SeedKernelIntervals.rightAngle
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (by exact_mod_cast (I.width_pos i).le) Real.pi_pos.le) hn.le

/-- Exact correction of the sinc kernel on the full first-quadrant
difference range, including the removable singularity at zero. -/
theorem oddCosineKernel_sinc_decomposition {N : ℕ} (hN : 0 < N) {v : ℝ}
    (hvbound : |v| ≤ Real.pi / 2) :
    oddCosineKernel N v = 2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * v) +
      seedCscCorrection v * Real.sin (2 * (N : ℝ) * v) := by
  by_cases hv : v = 0
  · subst v
    simp
  have hs : Real.sin v ≠ 0 := by
    rcases lt_or_gt_of_ne hv with hneg | hpos
    · have h := Real.sin_pos_of_pos_of_lt_pi (x := -v) (by linarith)
        (by have := (abs_le.mp hvbound).1; linarith [Real.pi_pos])
      rw [Real.sin_neg] at h
      linarith
    · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos
        (by have := (abs_le.mp hvbound).2; linarith [Real.pi_pos]))
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [oddCosineKernel_eq_div N hs,
    Real.sinc_of_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hn) hv),
    seedCscCorrection_of_ne_zero hv]
  field_simp
  ring

/-- The previously isolated analytic decomposition is now a theorem. -/
theorem sineKernelDecompositionHypothesis_holds : SineKernelDecompositionHypothesis := by
  classical
  constructor
  intro N J I α hN hα θ hθ
  have hNp : 0 < N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast hNp
  have hc : 0 < Real.pi / N := by positivity
  have hαabs (i : Fin J) : |α i| ≤ 1 := by
    rcases hα i with h | h <;> simp [h]
  let S : ℝ := ∑ i, α i * ∫ u in I.leftAngle i..I.rightAngle i,
    2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ))
  let C : ℝ := ∑ i, α i * ∫ u in I.leftAngle i..I.rightAngle i,
    seedCscCorrection (u - θ) * Real.sin (2 * (N : ℝ) * (u - θ))
  let R : ℝ := ∑ i, α i * ∫ u in I.leftAngle i..I.rightAngle i,
    oddCosineKernel N (u + θ)
  let L : ℝ := ∑ i, if I.rightAngle i ≤ θ - Real.pi / N then
    α i * ∫ u in I.leftAngle i..I.rightAngle i,
      2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ)) else 0
  let U : ℝ := ∑ i, if θ + Real.pi / N ≤ I.leftAngle i then
    α i * ∫ u in I.leftAngle i..I.rightAngle i,
      2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ)) else 0
  have htr : I.transform α θ = S + C - R := by
    have heval (i : Fin J) :
        (∫ u in I.leftAngle i..I.rightAngle i,
          oddCosineKernel N (u - θ) - oddCosineKernel N (u + θ)) =
        (∫ u in I.leftAngle i..I.rightAngle i,
          2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ))) +
        (∫ u in I.leftAngle i..I.rightAngle i,
          seedCscCorrection (u - θ) * Real.sin (2 * (N : ℝ) * (u - θ))) -
        ∫ u in I.leftAngle i..I.rightAngle i, oddCosineKernel N (u + θ) := by
      have hdom {u : ℝ} (hu : u ∈ Set.uIcc (I.leftAngle i) (I.rightAngle i)) :
          u - θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        rw [Set.uIcc_of_le (kernel_interval_order I hNp i)] at hu
        have huq := I.contains_first_quadrant hNp ⟨i, hu⟩
        constructor <;> linarith [huq.1, huq.2, hθ.1, hθ.2]
      have hsi : IntervalIntegrable
          (fun u => 2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ)))
          MeasureTheory.volume (I.leftAngle i) (I.rightAngle i) :=
        (by fun_prop : Continuous
          (fun u : ℝ => 2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ)))).intervalIntegrable _ _
      have hcorr : ContinuousOn (fun u => seedCscCorrection (u - θ))
          (Set.uIcc (I.leftAngle i) (I.rightAngle i)) :=
        seedCscCorrection_continuousOn.comp (by fun_prop) (fun u hu => hdom hu)
      have hci : IntervalIntegrable (fun u => seedCscCorrection (u - θ) *
          Real.sin (2 * (N : ℝ) * (u - θ))) MeasureTheory.volume
          (I.leftAngle i) (I.rightAngle i) := (hcorr.mul (by fun_prop : ContinuousOn
        (fun u : ℝ => Real.sin (2 * (N : ℝ) * (u - θ)))
          (Set.uIcc (I.leftAngle i) (I.rightAngle i)))).intervalIntegrable
      have hri : IntervalIntegrable (fun u => oddCosineKernel N (u + θ))
          MeasureTheory.volume (I.leftAngle i) (I.rightAngle i) :=
        ((oddCosineKernel_continuous N).comp (by fun_prop)).intervalIntegrable _ _
      rw [← intervalIntegral.integral_add hsi hci,
        ← intervalIntegral.integral_sub (hsi.add hci) hri]
      apply intervalIntegral.integral_congr
      intro u hu
      have hbound : |u - θ| ≤ Real.pi / 2 := abs_le.mpr (hdom hu)
      exact congrArg (fun v : ℝ => v - oddCosineKernel N (u + θ))
        (oddCosineKernel_sinc_decomposition hNp hbound)
    dsimp [SeedKernelIntervals.transform, S, C, R]
    simp_rw [heval, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hsplit : S = seedKernelLocalPart I α θ + L + U := by
    dsimp [S, L, U, seedKernelLocalPart, seedKernelSincIntegral]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have horder := kernel_interval_order I hNp i
    by_cases hL : I.rightAngle i ≤ θ - Real.pi / N
    · have hU : ¬ θ + Real.pi / N ≤ I.leftAngle i := by linarith
      simp [hL, hU, not_lt_of_ge hL]
    · by_cases hU : θ + Real.pi / N ≤ I.leftAngle i
      · simp [hL, hU, not_lt_of_ge hU]
      · simp [hL, hU, lt_of_not_ge hL, lt_of_not_ge hU]
  have hL : |L| ≤ 1 / Real.pi := sine_kernel_left_tail_bound hNp I α hαabs θ
    (fun i => I.rightAngle i ≤ θ - Real.pi / N) (fun _ h => h)
  have hU : |U| ≤ 1 / Real.pi := sine_kernel_right_tail_bound hNp I α hαabs θ
    (fun i => θ + Real.pi / N ≤ I.leftAngle i) (fun _ h => h)
  have hC : |C| ≤ (2 - 4 / Real.pi) / N := sine_kernel_correction_sum_bound hNp I α hαabs hθ
  have hR : |R| ≤ 2 / ((N : ℝ) * Real.sin (100 * Real.pi / N)) :=
    sine_kernel_reflected_sum_bound hN I α hαabs hθ
  refine ⟨seedKernelLocalPart I α θ, L + U + C - R, ?_, ?_, ?_, ?_⟩
  · rw [htr, hsplit]
    ring
  · have hb : |L + U + C - R| ≤ |L| + |U| + |C| + |R| := by
      have h₁ := abs_sub (L + U + C) R
      have h₂ := abs_add_le (L + U) C
      have h₃ := abs_add_le L U
      linarith
    have hcorr : (2 - 4 / Real.pi) / (N : ℝ) ≤ (12 * Real.pi + 2) / N := by
      apply div_le_div_of_nonneg_right _ hn.le
      have : 0 < 4 / Real.pi := by positivity
      linarith [Real.pi_pos]
    unfold sineKernelError
    nlinarith [show 1 / Real.pi + 1 / Real.pi = 2 / Real.pi by ring]
  · exact seedKernelLocalPart_abs_le_four I hNp α hαabs θ
  · exact fun hcontains => seedKernelLocalPart_abs_ge_four_thirds I hNp α hα hcontains

/-- The global odd sine-kernel bounds with no analytic hypothesis. -/
theorem sine_kernel_global {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) (hN : 2 ^ 20 ≤ N) (hα : ∀ i, α i = -1 ∨ α i = 1)
    (θ : ℝ) :
    |I.transform α θ| < 5 ∧
      (I.reflectedContains θ → 2 / 3 < |I.transform α θ|) :=
  sine_kernel_global_of_decomposition sineKernelDecompositionHypothesis_holds I α hN hα θ

/-- Scaling recovers the constants used for filling the small intervals. -/
theorem sine_kernel_scaled_global {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) (hN : 2 ^ 20 ≤ N) (hα : ∀ i, α i = -1 ∨ α i = 1)
    {K : ℝ} (hK : 0 ≤ K) (θ : ℝ) :
    |K * Real.sqrt N * I.transform α θ| ≤ 5 * K * Real.sqrt N ∧
      (I.reflectedContains θ → (2 * K / 3) * Real.sqrt N ≤
        |K * Real.sqrt N * I.transform α θ|) :=
  sine_kernel_scaled_global_of_decomposition sineKernelDecompositionHypothesis_holds
    I α hN hα hK θ

end
end Power2ModuleSVP
