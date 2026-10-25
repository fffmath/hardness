import Power2ModuleSVP.FlatFrontend.Program

/-!
# Rational

Exact rational safeguards used by the frontend, independently of the
transcendental enclosure estimates.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators

theorem clamp_lower {a b q : ℚ} : a ≤ clamp a b q := le_max_left _ _

theorem clamp_upper {a b q : ℚ} (hab : a ≤ b) : clamp a b q ≤ b := by
  exact max_le hab (min_le_left _ _)

theorem clamp_eq {a b q : ℚ} (ha : a ≤ q) (hb : q ≤ b) : clamp a b q = q := by
  simp [clamp, min_eq_right hb, max_eq_right ha]

/-- Clipping cannot worsen an enclosure of a point already in the range. -/
theorem clamp_error {a b q : ℚ} {x ε : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) (he : |(q : ℝ) - x| ≤ ε) :
    |(clamp a b q : ℝ) - x| ≤ ε := by
  have ha := (abs_le.mp he).1
  have hb := (abs_le.mp he).2
  have hε : 0 ≤ ε := (abs_nonneg _).trans he
  unfold clamp
  push_cast
  apply abs_le.mpr
  constructor
  · have hmin : x - ε ≤ min (b : ℝ) q := le_min (by linarith [hx.2]) (by linarith)
    have hm : min (b : ℝ) q ≤ max (a : ℝ) (min (b : ℝ) q) := le_max_right _ _
    linarith
  · have hm : max (a : ℝ) (min (b : ℝ) q) ≤ x + ε :=
      max_le (by linarith [hx.1]) ((min_le_right _ _).trans (by linarith))
    linarith

theorem sqrtApprox_nonnegative (p N : ℕ) : 0 ≤ sqrtApprox p N := by
  unfold sqrtApprox
  positivity

/-- Floor-square-root enclosure; the rational computation never evaluates
the real square root. -/
theorem sqrtApprox_spec (p N : ℕ) :
    (sqrtApprox p N : ℝ) ≤ Real.sqrt N ∧
      Real.sqrt N < (sqrtApprox p N : ℝ) + 1 / (2 : ℝ) ^ p := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hp2 : 0 < (2 : ℝ) ^ p ^ 2 := by positivity
  have hl : (Nat.sqrt (N * (2 ^ p) ^ 2) : ℝ) ^ 2 ≤ (N : ℝ) * (2 ^ p) ^ 2 := by
    have hh := Nat.sqrt_le (N * (2 ^ p) ^ 2)
    rw [← pow_two] at hh
    exact_mod_cast hh
  have hu : (N : ℝ) * (2 ^ p) ^ 2 <
      ((Nat.sqrt (N * (2 ^ p) ^ 2) : ℝ) + 1) ^ 2 := by
    have hh := Nat.lt_succ_sqrt (N * (2 ^ p) ^ 2)
    rw [← pow_two] at hh
    exact_mod_cast hh
  have hs := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hnon := Real.sqrt_nonneg (N : ℝ)
  have hfloor : (Nat.sqrt (N * (2 ^ p) ^ 2) : ℝ) ≤ Real.sqrt N * (2 : ℝ) ^ p := by
    apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity : 0 ≤ Real.sqrt N * (2 : ℝ) ^ p)).mp
    rwa [mul_pow, hs]
  have hceil : Real.sqrt N * (2 : ℝ) ^ p <
      (Nat.sqrt (N * (2 ^ p) ^ 2) : ℝ) + 1 := by
    apply (sq_lt_sq₀ (by positivity : 0 ≤ Real.sqrt N * (2 : ℝ) ^ p)
      (by positivity : 0 ≤ (Nat.sqrt (N * (2 ^ p) ^ 2) : ℝ) + 1)).mp
    rwa [mul_pow, hs]
  have he : (sqrtApprox p N : ℝ) =
      (Nat.sqrt (N * (2 ^ p) ^ 2) : ℝ) / (2 : ℝ) ^ p := by simp [sqrtApprox]
  rw [he]
  constructor
  · exact (div_le_iff₀ hpow).mpr hfloor
  · rw [← add_div, lt_div_iff₀ hpow]
    exact hceil

theorem second_starting_cube (a : ℕ × List ℚ) :
    ∀ x ∈ (coefficientInput a).2.1, |(x : ℝ)| ≤ 4 / 5 := by
  intro x hx
  simp only [coefficientInput, List.mem_map] at hx
  obtain ⟨j, _, rfl⟩ := hx
  apply abs_le.mpr
  have hl := clamp_lower (a := -(4 / 5 : ℚ)) (b := 4 / 5)
    (q := fractionalCoefficient (seedN a.1) (intervals (seedN a.1)) a.2 j)
  have hu := clamp_upper (a := -(4 / 5 : ℚ)) (b := 4 / 5)
    (q := fractionalCoefficient (seedN a.1) (intervals (seedN a.1)) a.2 j) (by norm_num)
  exact ⟨by simpa using (Rat.cast_le (K := ℝ)).mpr hl,
    by simpa using (Rat.cast_le (K := ℝ)).mpr hu⟩

theorem firstThreshold_nonnegative (N J : ℕ) : 0 ≤ firstThreshold N J := by
  unfold firstThreshold
  positivity

/-- An integer threshold suffices. The factor `56/5` uses the elementary
upper bound `log 2 < 7/10`; no executable logarithm is needed. -/
theorem first_threshold_entropy (N J : ℕ) (hJ : 0 < J) :
    coloringEntropy (fun _i : Fin N => firstThreshold N J) ≤ (J : ℝ) / 64 := by
  let l := Nat.log2 (64 * N / J) + 1
  let c := Nat.sqrt (56 * l / 5) + 1
  have hlog : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hsq : 56 * l < c * c * 5 := by
    have hh := Nat.lt_succ_sqrt (56 * l / 5)
    change 56 * l / 5 < c * c at hh
    exact (Nat.div_lt_iff_lt_mul (by norm_num)).mp hh
  have hc : (56 : ℝ) * l < (c : ℝ) ^ 2 * 5 := by
    rw [pow_two]
    exact_mod_cast hsq
  have ht : -((c : ℝ) ^ 2) / 16 ≤ -((l : ℝ) * Real.log 2) := by
    have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg l : (0 : ℝ) ≤ l)
    nlinarith
  have he : Real.exp (-((c : ℝ) ^ 2) / 16) ≤ ((2 : ℝ) ^ l)⁻¹ := by
    have hh := Real.exp_le_exp.mpr ht
    simpa [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hh
  have hquot : 64 * N / J < 2 ^ l := by
    simpa [l, Nat.log2_eq_log_two] using
      Nat.lt_pow_succ_log_self (b := 2) (by omega) (64 * N / J)
  have hsize : 64 * N < 2 ^ l * J :=
    (Nat.div_lt_iff_lt_mul hJ).mp hquot
  have hsizeR : (64 : ℝ) * N ≤ (2 : ℝ) ^ l * J := by exact_mod_cast hsize.le
  have hp : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have hbound : (N : ℝ) * ((2 : ℝ) ^ l)⁻¹ ≤ (J : ℝ) / 64 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hp]
    nlinarith
  change (∑ _i : Fin N, Real.exp (-((firstThreshold N J : ℝ) ^ 2) / 16)) ≤ _
  have hthresh : (firstThreshold N J : ℝ) = c := by simp [firstThreshold, c, l]
  simp only [hthresh, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)).trans hbound

end FlatFrontend
end Power2ModuleSVP
