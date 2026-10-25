import Mathlib.Data.Nat.Sqrt
import Rank2ModuleSVP.Completions

/-! # Explicit counting parameters

Explicit parameters for v2 §3.2.  The exponent and threshold are deliberately
conservative and can be increased by downstream reductions.
-/

namespace Rank2ModuleSVP
noncomputable section

/-- Absolute threshold in the counting and admissibility theorems. -/
def cntK0 : ℕ := 100000000
/-- Absolute prime-size exponent in the counting and admissibility theorems. -/
def cntC0 : ℕ := 1000
/-- v2 (6), with k chosen before q. -/
def cntH (k : ℕ) : ℕ := 21 * k / 20

theorem cntH_rounding (k : ℕ) :
    20 * cntH k ≤ 21 * k ∧ 21 * k < 20 * (cntH k + 1) := by
  unfold cntH
  omega

theorem cntH_bounds (k : ℕ) : k ≤ cntH k ∧ cntH k ≤ 2 * k := by
  have := cntH_rounding k
  omega

theorem cnt_sqrt_small {k : ℕ} (hk : cntK0 ≤ k) :
    1000 * Nat.sqrt k ≤ k := by
  have hlo : 10000 ≤ Nat.sqrt k := (Nat.le_sqrt).mpr (by simpa [cntK0] using hk)
  have hs := Nat.sqrt_le k
  nlinarith

/-- The bounded rounding error, in real arithmetic. -/
theorem cntH_real_rounding (k : ℕ) :
    (21 : ℝ) * k / 20 - 1 < cntH k ∧ (cntH k : ℝ) ≤ 21 * k / 20 := by
  obtain ⟨hl, hu⟩ := cntH_rounding k
  have hl' : (20 : ℝ) * cntH k ≤ 21 * k := by exact_mod_cast hl
  have hu' : (21 : ℝ) * k < 20 * ((cntH k : ℝ) + 1) := by exact_mod_cast hu
  constructor <;> linarith

/-- Downstream jobs can increase either absolute constant. -/
theorem cnt_regime_mono {K C k q : ℕ} (hK : cntK0 ≤ K) (hC : cntC0 ≤ C)
    (hk : K ≤ k) (hq : (2 * k) ^ C ≤ q) : cntK0 ≤ k ∧ (2 * k) ^ cntC0 ≤ q := by
  have hk0 : 100000000 ≤ k := hK.trans hk
  exact ⟨hK.trans hk, (Nat.pow_le_pow_right (by omega : 1 ≤ 2 * k) hC).trans hq⟩

/-- Every fixed polynomial needed in the union bound is dominated explicitly. -/
theorem cnt_q_polynomial {k q : ℕ} (hk : cntK0 ≤ k)
    (hq : (2 * k) ^ cntC0 ≤ q) : 1000000 * k ^ 4 < q := by
  have hk1 : 1 ≤ k := by unfold cntK0 at hk; omega
  have hc : 1000000 < k := by unfold cntK0 at hk; omega
  calc
    1000000 * k ^ 4 < k * k ^ 4 := Nat.mul_lt_mul_of_pos_right hc (pow_pos (by omega) _)
    _ = k ^ 5 := by ring
    _ ≤ k ^ cntC0 := Nat.pow_le_pow_right hk1 (by norm_num [cntC0])
    _ ≤ (2 * k) ^ cntC0 := Nat.pow_le_pow_left (by omega) _
    _ ≤ q := hq

/-- Wan's admissible range and the integer exponent margin, uniformly in t. -/
theorem cnt_parameter_range {k q t : ℕ} (hk : cntK0 ≤ k)
    (hq : (2 * k) ^ cntC0 ≤ q) (ht : t ≤ Nat.sqrt k) :
    2 ≤ k ∧ k + 4 ≤ cntH k - t ∧ cntH k - t ≤ 2 * k ∧
      cntH k - t - 2 < q - 2 ∧ 2 * (cntH k - t) ≤ 1000 * (cntH k - t - k - 4) := by
  have hs := cnt_sqrt_small hk
  have hr := cntH_rounding k
  have hh := cntH_bounds k
  have hp := cnt_q_polynomial hk hq
  have hk0 : 100000000 ≤ k := hk
  have hkpow : k ≤ k ^ 4 := Nat.le_self_pow (by norm_num) k
  omega

end
end Rank2ModuleSVP
