import Power2ModuleSVP.FlatFrontend.Enclosure.Derivative

/-!
# Precision

Uniform elementary estimates for the selected Machin precision.

Paper: `paper/power2svp.pdf`, Appendix A.3 (rational enclosures and the two rounding steps).
-/
namespace Power2ModuleSVP
namespace FlatFrontend

theorem piError_nonnegative (p : ℕ) : 0 ≤ piError p := by
  unfold piError arctanError
  norm_num
  positivity

/-- A convenient geometric majorant for the exact Machin remainder. -/
theorem piError_le (p : ℕ) : piError p ≤ 4 * (1 / 25 : ℚ) ^ p := by
  have hpow : (1 / 239 : ℚ) ^ (2 * p + 1) ≤ (1 / 25 : ℚ) ^ p / 239 := by
    rw [pow_add, pow_mul]
    norm_num
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ (1 / 239) ^ 2)
      (by norm_num : (1 / 239 : ℚ) ^ 2 ≤ 1 / 25) p
    linarith
  have he : (1 / 5 : ℚ) ^ (2 * p + 1) = (1 / 25 : ℚ) ^ p / 5 := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  unfold piError arctanError
  norm_num only [abs_of_pos (by norm_num : (0 : ℚ) < 1 / 5),
    abs_of_pos (by norm_num : (0 : ℚ) < 1 / 239)]
  have hn : (0 : ℚ) ≤ (1 / 25 : ℚ) ^ p := by positivity
  rw [he]
  norm_num at hpow ⊢
  linarith

/-- The computed rational pi value stays in a fixed compact interval. -/
theorem piTaylor_abs_le {p : ℕ} (hp : 1 ≤ p) : |piTaylor p| ≤ 4 := by
  have hpow : (1 / 25 : ℚ) ^ p ≤ 1 / 25 := by
    calc
      _ ≤ (1 / 25 : ℚ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
      _ = _ := pow_one _
  have heq : piError p ≤ 4 / 25 := (piError_le p).trans (by linarith)
  have he : (piError p : ℝ) ≤ 4 / 25 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr heq
    norm_num at hh ⊢
    exact hh
  have h := pi_taylor_error p
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hreal : |(piTaylor p : ℝ)| ≤ 4 := by
    rcases abs_le.mp h with ⟨hl, hu⟩
    apply abs_le.mpr
    constructor <;> linarith
  exact_mod_cast hreal

/-- The Taylor ratio test is automatic for all normalized derivative rows. -/
theorem derivative_ratio {N : ℕ} (k : Fin (16 * N)) (j : Fin N) :
    |derivativePhase N k j * piTaylor (precision N)| /
      (taylorOrder N + 1 : ℚ) ≤ 1 / 2 := by
  have hp : 1 ≤ precision N := by unfold precision; omega
  have hab := piTaylor_abs_le hp
  have hr := derivativePhase_le k j
  have hr0 := derivativePhase_nonnegative N k j
  have hb : |derivativePhase N k j * piTaylor (precision N)| ≤ 4 * N := by
    rw [abs_mul, abs_of_nonneg hr0]
    nlinarith
  have ho : 8 * (N : ℚ) ≤ taylorOrder N + 1 := by
    unfold taylorOrder
    push_cast
    nlinarith [sq_nonneg (N : ℚ)]
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < taylorOrder N + 1)).mpr
  linarith

/-- Keeping only the last half of a factorial gives a useful quadratic-order
Taylor bound without analytic asymptotics. -/
theorem taylorError_two_mul_le (m : ℕ) (q : ℚ) :
    taylorError (2 * m) q ≤ 2 * (q ^ 2 / (m + 1 : ℚ)) ^ m := by
  have hf := Nat.factorial_mul_pow_le_factorial (m := m) (n := m)
  have hf1 : 1 ≤ m.factorial := Nat.factorial_pos m
  have hnat : (m + 1) ^ m ≤ (2 * m).factorial := by
    have hh := Nat.mul_le_mul_right ((m + 1) ^ m) hf1
    simpa [two_mul] using hh.trans hf
  have hrat : ((m : ℚ) + 1) ^ m ≤ ((2 * m).factorial : ℚ) := by exact_mod_cast hnat
  have hd : (0 : ℚ) < (m + 1 : ℚ) ^ m := by positivity
  have he : |q| ^ (2 * m) = (q ^ 2) ^ m := by rw [pow_mul, sq_abs]
  unfold taylorError
  rw [he, div_pow, ← mul_div_assoc]
  exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num)
    (pow_nonneg (sq_nonneg q) m)) hd hrat

/-- Rounding the order down by a factor two is exact for these parameters. -/
theorem taylorOrder_even (N : ℕ) :
    taylorOrder N = 2 * (64 * (N + 1) ^ 2 + 64 + 32 * Nat.log2 (N + 1)) := by
  unfold taylorOrder precision
  omega

theorem taylorError_uniform (N : ℕ) :
    taylorError (taylorOrder N) (4 * N) ≤
      2 * (1 / 4 : ℚ) ^ (64 * (N + 1) ^ 2) := by
  let m := 64 * (N + 1) ^ 2 + 64 + 32 * Nat.log2 (N + 1)
  have hm : 64 * (N + 1) ^ 2 ≤ m := by dsimp [m]; omega
  have hmr : (64 : ℚ) * (N + 1) ^ 2 ≤ m := by exact_mod_cast hm
  have hbase : (4 * (N : ℚ)) ^ 2 / (m + 1 : ℚ) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < m + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℚ) N]
  rw [taylorOrder_even]
  apply (taylorError_two_mul_le m (4 * N)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) hbase m).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm)

private theorem geometric_budget (N k n : ℕ)
    (h : 2 ^ k * (N + 1) ^ 3 ≤ 2 ^ n) :
    (1 / 2 : ℚ) ^ n ≤ 1 / (2 ^ k * ((N : ℚ) + 1) ^ 3) := by
  have hh : (2 : ℚ) ^ k * ((N : ℚ) + 1) ^ 3 ≤ 2 ^ n := by exact_mod_cast h
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) hh

private theorem precision_budget (N : ℕ) :
    2 ^ 23 * (N + 1) ^ 3 ≤ 2 ^ precision N := by
  have hc := prefix_capacity (N + 1)
  have hc3 := Nat.pow_le_pow_left hc 3
  have he : 23 + 3 * (Nat.log2 (N + 1) + 1) ≤ precision N := by
    unfold precision
    omega
  calc
    _ ≤ 2 ^ 23 * (2 ^ (Nat.log2 (N + 1) + 1)) ^ 3 := Nat.mul_le_mul_left _ hc3
    _ = 2 ^ (23 + 3 * (Nat.log2 (N + 1) + 1)) := by rw [← pow_mul, Nat.mul_comm _ 3, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) he

private theorem order_budget (N : ℕ) :
    2 ^ 22 * (N + 1) ^ 3 ≤ 2 ^ (2 * (64 * (N + 1) ^ 2)) := by
  have hc : N + 1 ≤ 2 ^ N := Nat.lt_two_pow_self
  have hc3 := Nat.pow_le_pow_left hc 3
  have he : 22 + 3 * N ≤ 2 * (64 * (N + 1) ^ 2) := by nlinarith
  calc
    _ ≤ 2 ^ 22 * (2 ^ N) ^ 3 := Nat.mul_le_mul_left _ hc3
    _ = 2 ^ (22 + 3 * N) := by rw [← pow_mul, Nat.mul_comm _ 3, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) he

/-- Both selected primitive errors fit in one rounding allowance uniformly
in the dimension, with no asymptotic or large-degree premise. -/
theorem scalar_remainder_budget (N : ℕ) :
    (N : ℚ) * piError (precision N) + taylorError (taylorOrder N) (4 * N) ≤
      seedRoundingError N := by
  have hn : (0 : ℚ) ≤ N := by positivity
  have hp := piError_le (precision N)
  have hpow : (1 / 25 : ℚ) ^ precision N ≤ (1 / 2 : ℚ) ^ precision N :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hg := geometric_budget N 23 (precision N) (precision_budget N)
  have hpi : (N : ℚ) * piError (precision N) ≤
      4 * N / (2 ^ 23 * ((N : ℚ) + 1) ^ 3) := by
    calc
      _ ≤ N * (4 * (1 / 2 : ℚ) ^ precision N) :=
        mul_le_mul_of_nonneg_left (hp.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))) hn
      _ ≤ N * (4 * (1 / (2 ^ 23 * ((N : ℚ) + 1) ^ 3))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (by norm_num)) hn
      _ = _ := by ring
  have ht := taylorError_uniform N
  have hquart : (1 / 4 : ℚ) ^ (64 * (N + 1) ^ 2) =
      (1 / 2 : ℚ) ^ (2 * (64 * (N + 1) ^ 2)) := by rw [pow_mul (1 / 2 : ℚ) 2]; norm_num
  rw [hquart] at ht
  have hgt := geometric_budget N 22 _ (order_budget N)
  have htt : taylorError (taylorOrder N) (4 * N) ≤
      2 / (2 ^ 22 * ((N : ℚ) + 1) ^ 3) := by
    have hh := ht.trans (mul_le_mul_of_nonneg_left hgt (by norm_num : (0 : ℚ) ≤ 2))
    simpa only [mul_one_div] using hh
  have hsum := add_le_add hpi htt
  apply hsum.trans
  unfold seedRoundingError
  have hd : (0 : ℚ) < (N : ℚ) + 1 := by positivity
  field_simp
  nlinarith

theorem taylorError_mono {n : ℕ} {q b : ℚ} (h : |q| ≤ b) :
    taylorError n q ≤ taylorError n b := by
  have hb : 0 ≤ b := (abs_nonneg q).trans h
  unfold taylorError
  rw [abs_of_nonneg hb]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg q) h n) (by norm_num))
    (by positivity)

/-- The originally selected precisions suffice for every derivative entry. -/
theorem derivativeRemainderBound (N : ℕ) : DerivativeRemainderBound N := by
  refine ⟨fun k j => derivative_ratio k j, fun k j => ?_⟩
  have hr := derivativePhase_le k j
  have hr0 := derivativePhase_nonnegative N k j
  have hp := piTaylor_abs_le (p := precision N) (by unfold precision; omega)
  have hq : |derivativePhase N k j * piTaylor (precision N)| ≤ 4 * N := by
    rw [abs_mul, abs_of_nonneg hr0]
    nlinarith
  exact (add_le_add
    (mul_le_mul_of_nonneg_right hr (piError_nonnegative _))
    (taylorError_mono hq)).trans (scalar_remainder_budget N)

/-- Unconditional enclosure of the actual rational derivative matrix. -/
theorem derivative_error {N : ℕ} (k : Fin (16 * N)) (ell : ℕ) (j : Fin N) :
    |derivativeRow N k ell j - (derivativeEntry N k ell j : ℝ)| ≤
      (seedRoundingError N : ℝ) :=
  derivative_error_of_remainder (derivativeRemainderBound N) k ell j

/-- A stronger common tolerance for endpoint evaluation and square roots. -/
def fineError (N : ℕ) : ℚ := 1 / (2 ^ 80 * ((N : ℚ) + 1) ^ 10)

theorem fineError_pos (N : ℕ) : 0 < fineError N := by unfold fineError; positivity

theorem precision_fine (N : ℕ) : (1 / 2 : ℚ) ^ precision N ≤ fineError N := by
  have hc := Nat.pow_le_pow_left (prefix_capacity (N + 1)) 10
  have he : 80 + 10 * (Nat.log2 (N + 1) + 1) ≤ precision N := by unfold precision; omega
  have hh : 2 ^ 80 * (N + 1) ^ 10 ≤ 2 ^ precision N := by
    calc
      _ ≤ 2 ^ 80 * (2 ^ (Nat.log2 (N + 1) + 1)) ^ 10 := Nat.mul_le_mul_left _ hc
      _ = 2 ^ (80 + 10 * (Nat.log2 (N + 1) + 1)) := by
        rw [← pow_mul, Nat.mul_comm _ 10, ← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) he
  have hr : (2 : ℚ) ^ 80 * ((N : ℚ) + 1) ^ 10 ≤ 2 ^ precision N := by exact_mod_cast hh
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) hr

theorem taylor_fine (N : ℕ) :
    taylorError (taylorOrder N) (4 * N) ≤ 2 * fineError N := by
  have hc : N + 1 ≤ 2 ^ N := Nat.lt_two_pow_self
  have he : 80 + 10 * N ≤ 2 * (64 * (N + 1) ^ 2) := by nlinarith
  have hh : 2 ^ 80 * (N + 1) ^ 10 ≤ 2 ^ (2 * (64 * (N + 1) ^ 2)) := by
    calc
      _ ≤ 2 ^ 80 * (2 ^ N) ^ 10 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc 10)
      _ = 2 ^ (80 + 10 * N) := by rw [← pow_mul, Nat.mul_comm _ 10, ← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) he
  have hr : (2 : ℚ) ^ 80 * ((N : ℚ) + 1) ^ 10 ≤ 2 ^ (2 * (64 * (N + 1) ^ 2)) :=
    by exact_mod_cast hh
  have hsmall : (1 / 4 : ℚ) ^ (64 * (N + 1) ^ 2) ≤ fineError N := by
    rw [show (1 / 4 : ℚ) = (1 / 2 : ℚ) ^ 2 by norm_num, ← pow_mul, one_div_pow]
    exact one_div_le_one_div_of_le (by positivity) hr
  exact (taylorError_uniform N).trans (mul_le_mul_of_nonneg_left hsmall (by norm_num))

theorem phase_error_fine {N : ℕ} {r : ℚ} (hr0 : 0 ≤ r) (hr : r ≤ N) (ell : ℕ) :
    |jetSin ell ((r : ℝ) * Real.pi) -
      (phaseTaylor ell (taylorOrder N) (r * piTaylor (precision N)) : ℝ)| ≤
        (((4 * (N : ℚ) + 2) * fineError N : ℚ) : ℝ) := by
  have hp := piTaylor_abs_le (p := precision N) (by unfold precision; omega)
  have hq : |r * piTaylor (precision N)| ≤ 4 * N := by
    rw [abs_mul, abs_of_nonneg hr0]
    nlinarith
  have ho : 8 * (N : ℚ) ≤ taylorOrder N + 1 := by
    unfold taylorOrder
    push_cast
    nlinarith [sq_nonneg (N : ℚ)]
  have hratio : |r * piTaylor (precision N)| / (taylorOrder N + 1 : ℚ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < taylorOrder N + 1)).mpr
    linarith
  have hpi : piError (precision N) ≤ 4 * fineError N :=
    (piError_le _).trans (mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 1 / 25)
        (by norm_num : (1 / 25 : ℚ) ≤ 1 / 2) _).trans (precision_fine N)) (by norm_num))
  have ht := (taylorError_mono hq).trans (taylor_fine N)
  have hsum : |r| * piError (precision N) +
      taylorError (taylorOrder N) (r * piTaylor (precision N)) ≤
        (4 * (N : ℚ) + 2) * fineError N := by
    rw [abs_of_nonneg hr0]
    have hh := mul_le_mul hr hpi (piError_nonnegative _) (by positivity : (0 : ℚ) ≤ N)
    nlinarith
  exact (phaseTaylor_pi_error ell _ _ r hratio).trans ((Rat.cast_le (K := ℝ)).mpr hsum)

end FlatFrontend
end Power2ModuleSVP
