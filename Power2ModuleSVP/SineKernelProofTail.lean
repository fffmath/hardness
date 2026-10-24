module

public import Power2ModuleSVP.SineKernelProofVariation
public import Power2ModuleSVP.SineKernelProofLobes
import Mathlib.Tactic

/-!
Distant sinc intervals are controlled by clipped reciprocal weights.
Clipping keeps the weights continuous and monotone even at the observation
point, where the selected distant intervals never evaluate them.
-/

@[expose] public section
namespace Power2ModuleSVP
open scoped BigOperators
noncomputable section

private def reciprocalLeft (c θ u : ℝ) : ℝ := 1 / max (θ - u) c
private def reciprocalRight (c θ u : ℝ) : ℝ := -(1 / max (u - θ) c)

private theorem reciprocalLeft_continuous {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    Continuous (reciprocalLeft c θ) := by
  unfold reciprocalLeft
  exact continuous_const.div (by fun_prop)
    (fun u => ne_of_gt (hc.trans_le (le_max_right _ _)))

private theorem reciprocalRight_continuous {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    Continuous (reciprocalRight c θ) := by
  unfold reciprocalRight
  exact (continuous_const.div (by fun_prop)
    (fun u => ne_of_gt (hc.trans_le (le_max_right _ _)))).neg

private theorem reciprocalLeft_monotone {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    Monotone (reciprocalLeft c θ) := by
  intro u v huv
  exact one_div_le_one_div_of_le (hc.trans_le (le_max_right _ _))
    (max_le_max (by linarith) le_rfl)

private theorem reciprocalRight_monotone {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    Monotone (reciprocalRight c θ) := by
  intro u v huv
  apply neg_le_neg
  exact one_div_le_one_div_of_le (hc.trans_le (le_max_right _ _))
    (max_le_max (by linarith) le_rfl)

private theorem reciprocalLeft_bounds {c : ℝ} (hc : 0 < c) (θ u : ℝ) :
    0 ≤ reciprocalLeft c θ u ∧ reciprocalLeft c θ u ≤ 1 / c := by
  exact ⟨by unfold reciprocalLeft; positivity,
    one_div_le_one_div_of_le hc (le_max_right _ _)⟩

private theorem reciprocalRight_bounds {c : ℝ} (hc : 0 < c) (θ u : ℝ) :
    -(1 / c) ≤ reciprocalRight c θ u ∧ reciprocalRight c θ u ≤ 0 := by
  constructor
  · exact neg_le_neg (one_div_le_one_div_of_le hc (le_max_right _ _))
  · unfold reciprocalRight
    exact neg_nonpos.mpr (by positivity)

private theorem sinc_scaled_eq_div {N : ℕ} (hN : 0 < N) {v : ℝ} (hv : v ≠ 0) :
    2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * v) =
      Real.sin (2 * (N : ℝ) * v) / v := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Real.sinc_of_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hn) hv)]
  field_simp

/-- Each side of the distant family costs at most `1/pi`. The predicate
may select any subfamily on that side. -/
theorem sine_kernel_left_tail_bound {N J : ℕ} (hN : 0 < N)
    (I : SeedKernelIntervals N J) (α : Fin J → ℝ) (hα : ∀ i, |α i| ≤ 1)
    (θ : ℝ) (p : Fin J → Prop) [DecidablePred p]
    (hp : ∀ i, p i → I.rightAngle i ≤ θ - Real.pi / N) :
    |∑ i, if p i then α i * ∫ u in I.leftAngle i..I.rightAngle i,
      2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ)) else 0| ≤ 1 / Real.pi := by
  let c : ℝ := Real.pi / N
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < c := by dsimp [c]; positivity
  let g := reciprocalLeft c θ
  let β : Fin J → ℝ := fun i => if p i then -α i else 0
  have hβ : ∀ i, |β i| ≤ 1 := by
    intro i
    dsimp [β]
    split_ifs <;> simp_all only [abs_neg, abs_zero, zero_le_one]
  have hr (i : Fin J) : I.right i ≤ N := by have := I.right_clearance i; omega
  have hb := grid_sine_sum_le_monotone_variation hN I.left I.right
    (fun i => (I.width_pos i).le) hr
    (fun i j hij => (I.separated i j hij).imp (fun h => by omega) (fun h => by omega))
    g (-2 * N * θ) β hβ (reciprocalLeft_continuous hc θ).continuousOn
    ((reciprocalLeft_monotone hc θ).monotoneOn _)
  have heq : (∑ i, if p i then α i * ∫ u in I.leftAngle i..I.rightAngle i,
      2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ)) else 0) =
      ∑ i, β i * ∫ u in (I.left i * Real.pi / N)..(I.right i * Real.pi / N),
        g u * Real.sin (2 * (N : ℝ) * u + -2 * N * θ) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hpi : p i
    · simp only [hpi, ite_true, β]
      rw [neg_mul, ← mul_neg, ← intervalIntegral.integral_neg]
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      have hab : I.leftAngle i ≤ I.rightAngle i := by
        unfold SeedKernelIntervals.leftAngle SeedKernelIntervals.rightAngle
        gcongr
        exact (I.width_pos i).le
      rw [Set.uIcc_of_le hab] at hu
      have huc : c ≤ θ - u := by have := hp i hpi; dsimp [c]; linarith [hu.2]
      have hv : u - θ ≠ 0 := by linarith
      change 2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ)) =
        -(g u * Real.sin (2 * (N : ℝ) * u + -2 * N * θ))
      rw [sinc_scaled_eq_div hN hv]
      dsimp [g, reciprocalLeft]
      rw [max_eq_left huc]
      have harg : 2 * (N : ℝ) * u + -2 * N * θ = 2 * (N : ℝ) * (u - θ) := by ring
      rw [harg]
      field_simp [hv, show θ - u ≠ 0 by linarith]
      ring
    · simp [hpi, β]
  rw [heq]
  apply hb.trans
  have hga := reciprocalLeft_bounds hc θ 0
  have hgb := reciprocalLeft_bounds hc θ ((N : ℝ) * Real.pi / N)
  have hvar : g ((N : ℝ) * Real.pi / N) - g 0 ≤ 1 / c := by
    dsimp [g]
    linarith
  calc
    _ ≤ (1 / c) / N := div_le_div_of_nonneg_right hvar hn.le
    _ = 1 / Real.pi := by dsimp [c]; field_simp

/-- The right distant subfamily has the same bound. -/
theorem sine_kernel_right_tail_bound {N J : ℕ} (hN : 0 < N)
    (I : SeedKernelIntervals N J) (α : Fin J → ℝ) (hα : ∀ i, |α i| ≤ 1)
    (θ : ℝ) (p : Fin J → Prop) [DecidablePred p]
    (hp : ∀ i, p i → θ + Real.pi / N ≤ I.leftAngle i) :
    |∑ i, if p i then α i * ∫ u in I.leftAngle i..I.rightAngle i,
      2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ)) else 0| ≤ 1 / Real.pi := by
  let c : ℝ := Real.pi / N
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < c := by dsimp [c]; positivity
  let g := reciprocalRight c θ
  let β : Fin J → ℝ := fun i => if p i then -α i else 0
  have hβ : ∀ i, |β i| ≤ 1 := by
    intro i
    dsimp [β]
    split_ifs <;> simp_all only [abs_neg, abs_zero, zero_le_one]
  have hr (i : Fin J) : I.right i ≤ N := by have := I.right_clearance i; omega
  have hb := grid_sine_sum_le_monotone_variation hN I.left I.right
    (fun i => (I.width_pos i).le) hr
    (fun i j hij => (I.separated i j hij).imp (fun h => by omega) (fun h => by omega))
    g (-2 * N * θ) β hβ (reciprocalRight_continuous hc θ).continuousOn
    ((reciprocalRight_monotone hc θ).monotoneOn _)
  have heq : (∑ i, if p i then α i * ∫ u in I.leftAngle i..I.rightAngle i,
      2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ)) else 0) =
      ∑ i, β i * ∫ u in (I.left i * Real.pi / N)..(I.right i * Real.pi / N),
        g u * Real.sin (2 * (N : ℝ) * u + -2 * N * θ) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hpi : p i
    · simp only [hpi, ite_true, β]
      rw [neg_mul, ← mul_neg, ← intervalIntegral.integral_neg]
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      have hab : I.leftAngle i ≤ I.rightAngle i := by
        unfold SeedKernelIntervals.leftAngle SeedKernelIntervals.rightAngle
        gcongr
        exact (I.width_pos i).le
      rw [Set.uIcc_of_le hab] at hu
      have huc : c ≤ u - θ := by have := hp i hpi; dsimp [c]; linarith [hu.1]
      have hv : u - θ ≠ 0 := by linarith
      change 2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ)) =
        -(g u * Real.sin (2 * (N : ℝ) * u + -2 * N * θ))
      rw [sinc_scaled_eq_div hN hv]
      dsimp [g, reciprocalRight]
      rw [max_eq_left huc]
      have harg : 2 * (N : ℝ) * u + -2 * N * θ = 2 * (N : ℝ) * (u - θ) := by ring
      rw [harg]
      field_simp [hv, show θ - u ≠ 0 by linarith]
    · simp [hpi, β]
  rw [heq]
  apply hb.trans
  have hga := reciprocalRight_bounds hc θ 0
  have hgb := reciprocalRight_bounds hc θ ((N : ℝ) * Real.pi / N)
  have hvar : g ((N : ℝ) * Real.pi / N) - g 0 ≤ 1 / c := by
    dsimp [g]
    linarith
  calc
    _ ≤ (1 / c) / N := div_le_div_of_nonneg_right hvar hn.le
    _ = 1 / Real.pi := by dsimp [c]; field_simp

end
end Power2ModuleSVP
