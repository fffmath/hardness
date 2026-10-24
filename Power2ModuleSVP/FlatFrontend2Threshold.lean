import Power2ModuleSVP.FlatFrontend2Endpoints

/-! A dimension-uniform bound for the integer first-round threshold. -/
namespace Power2ModuleSVP
namespace FlatFrontend

def firstThresholdNat (N J : ℕ) : ℕ :=
  Nat.sqrt (56 * (Nat.log2 (64 * N / J) + 1) / 5) + 1

theorem firstThreshold_cast (N J : ℕ) :
    (firstThresholdNat N J : ℚ) = firstThreshold N J := rfl

private theorem threshold_linear (L : ℕ) (hL : 73 ≤ L) :
    Nat.sqrt (56 * (L + 1) / 5) + 1 ≤ L - 73 + 29 := by
  have hd : 56 * (L + 1) / 5 ≤ 56 * (L + 1) := Nat.div_le_self _ _
  have hdiv : 5 * (56 * (L + 1) / 5) ≤ 56 * (L + 1) := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (56 * (L + 1)) 5
  have he : L = (L - 73) + 73 := by omega
  have hsq : 56 * (L + 1) / 5 < (L - 73 + 29) ^ 2 := by
    nlinarith
  have hh := Nat.sqrt_lt'.mpr hsq
  omega

private theorem linear_sq_le_dyadic (k : ℕ) : (k + 29) ^ 2 ≤ 841 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ (2 : ℕ) k]
    have hh : (k + 1 + 29) ^ 2 ≤ 2 * (k + 29) ^ 2 := by
      simp only [pow_two]
      nlinarith [Nat.zero_le (k * k)]
    nlinarith

/-- The increasing integer threshold is compensated by the decreasing
interval fraction. This is stronger than bounding a single threshold by 29,
which would be false for very sparse interval families. -/
theorem firstThreshold_scale {N J : ℕ} (hJ : 0 < J) (hcount : J * 2 ^ 66 ≤ N) :
    firstThresholdNat N J ^ 2 * J * 2 ^ 66 ≤ 841 * N := by
  let L := Nat.log2 (64 * N / J)
  let c := Nat.sqrt (56 * (L + 1) / 5) + 1
  change c ^ 2 * J * 2 ^ 66 ≤ 841 * N
  by_cases hL : L ≤ 73
  · have hh : 56 * (L + 1) / 5 ≤ 828 := by omega
    have hs : c ≤ 29 := by
      have := Nat.sqrt_le_sqrt hh
      norm_num at this
      dsimp [c]
      omega
    have hsq : c ^ 2 ≤ 841 := by nlinarith
    nlinarith [Nat.mul_le_mul_right (J * 2 ^ 66) hsq]
  · have hlarge : 73 ≤ L := by omega
    have hs : c ^ 2 ≤ 841 * 2 ^ (L - 73) := by
      exact (Nat.pow_le_pow_left (threshold_linear L hlarge) 2).trans (linear_sq_le_dyadic _)
    have hn : 64 * N / J ≠ 0 := by
      have : J ≤ 64 * N := by nlinarith
      exact Nat.ne_of_gt ((Nat.one_le_div_iff hJ).mpr this)
    have hp : 2 ^ L ≤ 64 * N / J := (Nat.le_log2 hn).mp le_rfl
    have hm := (Nat.mul_le_mul_right J hp).trans (Nat.div_mul_le_self (64 * N) J)
    have he : L = (L - 73) + 73 := by omega
    rw [he, pow_add] at hm
    have hscaled : 2 ^ (L - 73) * J * 2 ^ 66 ≤ N := by norm_num at hm ⊢; nlinarith
    calc
      _ ≤ (841 * 2 ^ (L - 73)) * J * 2 ^ 66 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hs)
      _ = 841 * (2 ^ (L - 73) * J * 2 ^ 66) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hscaled

/-- The actual integer threshold leaves a strict numerical margin after
entry enclosure and recomputation error. -/
theorem firstThreshold_margin {N J : ℕ} (hN : 0 < N) (hcount : J * 2 ^ 66 ≤ N) :
    FirstThresholdMargin N J (kernelError N : ℝ) := by
  by_cases hJ : J = 0
  · subst J
    norm_num [FirstThresholdMargin]
  have hJpos : 0 < J := Nat.pos_of_ne_zero hJ
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (0 : ℝ) ≤ firstThreshold N J := by exact_mod_cast firstThreshold_nonnegative N J
  have hce : (firstThreshold N J : ℝ) = (firstThresholdNat N J : ℝ) := by
    rw [← firstThreshold_cast]
    norm_cast
  have hscale : (firstThreshold N J : ℝ) ^ 2 * (J : ℝ) * 2 ^ 66 ≤ 841 * N := by
    rw [hce]
    exact_mod_cast firstThreshold_scale hJpos hcount
  have hcnt : (J : ℝ) * 2 ^ 66 ≤ N := by exact_mod_cast hcount
  have hsN := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hsJ := Real.sq_sqrt (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
  have hrootc : (firstThreshold N J : ℝ) * Real.sqrt J * 2 ^ 33 ≤ 29 * Real.sqrt N := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    norm_num [mul_pow, hsN, hsJ] at *
    convert hscale using 1
    norm_num
  have hroot : Real.sqrt J * 2 ^ 33 ≤ Real.sqrt N := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    norm_num [mul_pow, hsN, hsJ] at *
    exact hcnt
  let S : ℝ := (240 * (firstThreshold N J : ℝ) + 2400) * Real.sqrt J
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hS : S ≤ 9360 * Real.sqrt N / 2 ^ 33 := by
    dsimp [S]
    norm_num at hrootc hroot ⊢
    nlinarith
  have hrootN : Real.sqrt N ≤ N := by
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hs0 := Real.sqrt_nonneg (N : ℝ)
    nlinarith
  have hSN : S ≤ N := by
    norm_num at hS
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hJN : (J : ℝ) ≤ N := by
    norm_num at hcnt
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  have hε : (0 : ℝ) ≤ kernelError N := by exact_mod_cast kernelError_nonnegative N
  have hbudget : (N : ℝ) * (kernelError N : ℝ) ≤ 1 / 2 ^ 20 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (kernelError_budget N)
    have he : (seedRoundingError N : ℝ) ≤ 1 / 2 ^ 20 := by
      simp only [seedRoundingError, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
        Rat.cast_pow, Rat.cast_ofNat, Rat.cast_add, Rat.cast_natCast]
      apply one_div_le_one_div_of_le (by norm_num)
      have hn0 := Nat.cast_nonneg (α := ℝ) N
      nlinarith [sq_nonneg (N : ℝ)]
    have hh' : (N : ℝ) * (kernelError N : ℝ) ≤ (seedRoundingError N : ℝ) := by
      simpa only [Rat.cast_mul, Rat.cast_natCast] using hh
    exact hh'.trans he
  have hmain : S * (216000 * Real.sqrt N * Real.pi / N) ≤
      9360 * 216000 * Real.pi / 2 ^ 33 := by
    have hh := mul_le_mul_of_nonneg_right hS
      (by positivity : 0 ≤ 216000 * Real.sqrt (N : ℝ) * Real.pi / N)
    apply hh.trans_eq
    field_simp
    nlinarith [hsN]
  have hpi := Real.pi_lt_d6
  have hfinal : 9360 * 216000 * Real.pi / 2 ^ 33 + 2 / 2 ^ 20 ≤ (3 : ℝ) / 4 := by
    norm_num at *
    linarith
  unfold FirstThresholdMargin
  change S * (216000 * Real.sqrt N * Real.pi / N + (kernelError N : ℝ)) +
    J * (kernelError N : ℝ) ≤ _
  rw [mul_add]
  have he1 := mul_le_mul_of_nonneg_right hSN hε
  have he2 := mul_le_mul_of_nonneg_right hJN hε
  linarith

end FlatFrontend
end Power2ModuleSVP
