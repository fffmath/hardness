module

public import Power2ModuleSVP.RudinShapiro
import Mathlib.Tactic

/-! Stable prefixes of the Rudin--Shapiro words and their circle bounds. -/

@[expose] public section
namespace Power2ModuleSVP
open Polynomial
open scoped BigOperators
noncomputable section

/-- Evaluation of exactly the first `m` coefficients, with no implicit
degree assumptions. -/
def rsPrefixEval (p : ℤ[X]) (m : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range m, (p.coeff j : ℂ) * z ^ j

@[simp] theorem rsPrefixEval_zero (p : ℤ[X]) (z : ℂ) : rsPrefixEval p 0 z = 0 := by
  simp [rsPrefixEval]

theorem rsPrefixEval_eq_eval {p : ℤ[X]} {m : ℕ} (hm : p.natDegree < m) (z : ℂ) :
    rsPrefixEval p m z = rsEval p z :=
  (eval₂_eq_sum_range' (Int.castRingHom ℂ) hm z).symm

theorem rudinShapiro_prefix_low (k m : ℕ) (hm : m ≤ 2 ^ k) (z : ℂ) :
    rsPrefixEval (rudinShapiroP (k + 1)) m z = rsPrefixEval (rudinShapiroP k) m z ∧
    rsPrefixEval (rudinShapiroQ (k + 1)) m z = rsPrefixEval (rudinShapiroP k) m z := by
  constructor <;> apply Finset.sum_congr rfl <;> intro j hj <;>
    have hjk : ¬ 2 ^ k ≤ j := by have := Finset.mem_range.mp hj; omega
  · simp [rudinShapiroP_succ, coeff_X_pow_mul', hjk]
  · simp [rudinShapiroQ_succ, coeff_X_pow_mul', hjk]

theorem rudinShapiro_prefix_high (k r : ℕ) (z : ℂ) :
    rsPrefixEval (rudinShapiroP (k + 1)) (2 ^ k + r) z =
      rsEval (rudinShapiroP k) z + z ^ (2 ^ k) * rsPrefixEval (rudinShapiroQ k) r z ∧
    rsPrefixEval (rudinShapiroQ (k + 1)) (2 ^ k + r) z =
      rsEval (rudinShapiroP k) z - z ^ (2 ^ k) * rsPrefixEval (rudinShapiroQ k) r z := by
  have hn : (rudinShapiroP k).natDegree < 2 ^ k := by
    rw [(rudinShapiro_natDegree k).1]
    exact Nat.sub_lt (by positivity) (by omega)
  have hl := rudinShapiro_prefix_low k (2 ^ k) le_rfl z
  have htailP : (∑ j ∈ Finset.range r,
      ((rudinShapiroP (k + 1)).coeff (2 ^ k + j) : ℂ) * z ^ (2 ^ k + j)) =
      z ^ (2 ^ k) * rsPrefixEval (rudinShapiroQ k) r z := by
    rw [rsPrefixEval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hzero := (rudinShapiro_coefficients k).2 (2 ^ k + j) (by omega)
    simp only [rudinShapiroP_succ, coeff_add, coeff_X_pow_mul',
      ite_eq_left (show 2 ^ k ≤ 2 ^ k + j by omega),
      Nat.add_sub_cancel_left, hzero.1, zero_add, pow_add]
    ring
  have htailQ : (∑ j ∈ Finset.range r,
      ((rudinShapiroQ (k + 1)).coeff (2 ^ k + j) : ℂ) * z ^ (2 ^ k + j)) =
      -(z ^ (2 ^ k) * rsPrefixEval (rudinShapiroQ k) r z) := by
    rw [rsPrefixEval, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hzero := (rudinShapiro_coefficients k).2 (2 ^ k + j) (by omega)
    simp only [rudinShapiroQ_succ, coeff_sub, coeff_X_pow_mul',
      ite_eq_left (show 2 ^ k ≤ 2 ^ k + j by omega),
      Nat.add_sub_cancel_left, hzero.1, zero_sub, Int.cast_neg, pow_add]
    ring
  constructor
  · rw [rsPrefixEval, Finset.sum_range_add]
    change rsPrefixEval (rudinShapiroP (k + 1)) (2 ^ k) z + _ = _
    rw [hl.1, rsPrefixEval_eq_eval hn, htailP]
  · rw [rsPrefixEval, Finset.sum_range_add]
    change rsPrefixEval (rudinShapiroQ (k + 1)) (2 ^ k) z + _ = _
    rw [hl.2, rsPrefixEval_eq_eval hn, htailQ, sub_eq_add_neg]

private theorem sqrt_two_pow_succ (k : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (k + 1)) = Real.sqrt 2 * Real.sqrt ((2 : ℝ) ^ k) := by
  rw [pow_succ, mul_comm, Real.sqrt_mul (by norm_num)]

/-- A geometric-sum bound for every proper prefix of either word. -/
theorem rudinShapiro_prefix_geometric_bound (k m : ℕ) (hm : m < 2 ^ k)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖rsPrefixEval (rudinShapiroP k) m z‖ ≤
      (2 + Real.sqrt 2) * Real.sqrt ((2 : ℝ) ^ k) ∧
    ‖rsPrefixEval (rudinShapiroQ k) m z‖ ≤
      (2 + Real.sqrt 2) * Real.sqrt ((2 : ℝ) ^ k) := by
  induction k generalizing m with
  | zero =>
    have : m = 0 := by simpa using hm
    subst m
    simp only [rsPrefixEval_zero, norm_zero, pow_zero, Real.sqrt_one]
    constructor <;> positivity
  | succ k ih =>
    by_cases hlow : m < 2 ^ k
    · obtain ⟨hp, hq⟩ := ih m hlow
      have hl := rudinShapiro_prefix_low k m hlow.le z
      have hs : (2 + Real.sqrt 2) * Real.sqrt ((2 : ℝ) ^ k) ≤
          (2 + Real.sqrt 2) * Real.sqrt ((2 : ℝ) ^ (k + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.sqrt_le_sqrt
        rw [pow_succ]
        nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) k]
      rw [hl.1, hl.2]
      exact ⟨hp.trans hs, hp.trans hs⟩
    · have hkm : 2 ^ k ≤ m := by omega
      have hr : m - 2 ^ k < 2 ^ k := by rw [pow_succ] at hm; omega
      obtain ⟨hp, hq⟩ := ih (m - 2 ^ k) hr
      have hl := rudinShapiro_prefix_high k (m - 2 ^ k) z
      rw [Nat.add_sub_of_le hkm] at hl
      rw [hl.1, hl.2]
      have hs : ‖z ^ (2 ^ k) * rsPrefixEval (rudinShapiroQ k) (m - 2 ^ k) z‖ =
          ‖rsPrefixEval (rudinShapiroQ k) (m - 2 ^ k) z‖ := by
        simp [norm_pow, hz]
      have he : Real.sqrt ((2 : ℝ) ^ (k + 1)) +
          (2 + Real.sqrt 2) * Real.sqrt ((2 : ℝ) ^ k) =
          (2 + Real.sqrt 2) * Real.sqrt ((2 : ℝ) ^ (k + 1)) := by
        rw [sqrt_two_pow_succ]
        linear_combination -(Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)) *
          Real.sqrt ((2 : ℝ) ^ k)
      constructor
      · calc
          _ ≤ ‖rsEval (rudinShapiroP k) z‖ +
              ‖z ^ (2 ^ k) * rsPrefixEval (rudinShapiroQ k) (m - 2 ^ k) z‖ :=
            norm_add_le _ _
          _ ≤ _ := by rw [hs, ← he]; exact add_le_add (rudinShapiro_norm_bounds k hz).1 hq
      · calc
          _ ≤ ‖rsEval (rudinShapiroP k) z‖ +
              ‖z ^ (2 ^ k) * rsPrefixEval (rudinShapiroQ k) (m - 2 ^ k) z‖ :=
            norm_sub_le _ _
          _ ≤ _ := by rw [hs, ← he]; exact add_le_add (rudinShapiro_norm_bounds k hz).1 hq

/-- The prefix constant used by the seed construction. This is uniform in
the depth of a word containing the requested prefix. -/
theorem rudinShapiro_prefix_bound (k m : ℕ) (hm : m ≤ 2 ^ k) (hm0 : 0 < m)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖rsPrefixEval (rudinShapiroP k) m z‖ < 5 * Real.sqrt m ∧
    ‖rsPrefixEval (rudinShapiroQ k) m z‖ < 5 * Real.sqrt m := by
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm0)
  have hsqrt2 : Real.sqrt 2 < (3 : ℝ) / 2 := by
    apply (Real.sqrt_lt' (by norm_num)).2
    norm_num
  induction k generalizing m with
  | zero =>
    have : m = 1 := by norm_num at hm; omega
    subst m
    norm_num [rsPrefixEval]
  | succ k ih =>
    by_cases hfull : m = 2 ^ (k + 1)
    · subst m
      have hnP : (rudinShapiroP (k + 1)).natDegree < 2 ^ (k + 1) := by
        rw [(rudinShapiro_natDegree _).1]
        exact Nat.sub_lt (by positivity) (by omega)
      have hnQ : (rudinShapiroQ (k + 1)).natDegree < 2 ^ (k + 1) := by
        rw [(rudinShapiro_natDegree _).2]
        exact Nat.sub_lt (by positivity) (by omega)
      rw [rsPrefixEval_eq_eval hnP, rsPrefixEval_eq_eval hnQ]
      have hnat : ((2 ^ (k + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; rfl
      rw [hnat]
      have he : Real.sqrt ((2 : ℝ) ^ (k + 1 + 1)) <
          5 * Real.sqrt ((2 : ℝ) ^ (k + 1)) := by
        rw [sqrt_two_pow_succ]
        exact mul_lt_mul_of_pos_right (hsqrt2.trans (by norm_num))
          (Real.sqrt_pos.2 (by positivity))
      exact ⟨(rudinShapiro_norm_bounds _ hz).1.trans_lt he,
        (rudinShapiro_norm_bounds _ hz).2.trans_lt he⟩
    · by_cases hlow : m ≤ 2 ^ k
      · have hl := rudinShapiro_prefix_low k m hlow z
        rw [hl.1, hl.2]
        have hi := ih m hlow hm0 hsqrtm
        exact ⟨hi.1, hi.1⟩
      · have hkm : 2 ^ k ≤ m := by omega
        have hr : m - 2 ^ k < 2 ^ k := by rw [pow_succ] at hm; omega
        have hq := (rudinShapiro_prefix_geometric_bound k (m - 2 ^ k) hr hz).2
        have hl := rudinShapiro_prefix_high k (m - 2 ^ k) z
        rw [Nat.add_sub_of_le hkm] at hl
        rw [hl.1, hl.2]
        have hs : ‖z ^ (2 ^ k) * rsPrefixEval (rudinShapiroQ k) (m - 2 ^ k) z‖ =
            ‖rsPrefixEval (rudinShapiroQ k) (m - 2 ^ k) z‖ := by
          simp [norm_pow, hz]
        have hn : Real.sqrt ((2 : ℝ) ^ k) ≤ Real.sqrt m := by
          apply Real.sqrt_le_sqrt
          exact_mod_cast hkm
        have hsum : Real.sqrt ((2 : ℝ) ^ (k + 1)) +
            (2 + Real.sqrt 2) * Real.sqrt ((2 : ℝ) ^ k) < 5 * Real.sqrt m := by
          rw [sqrt_two_pow_succ]
          calc
            _ = (2 + 2 * Real.sqrt 2) * Real.sqrt ((2 : ℝ) ^ k) := by ring
            _ ≤ (2 + 2 * Real.sqrt 2) * Real.sqrt m := by gcongr
            _ < _ := mul_lt_mul_of_pos_right (by linarith) hsqrtm
        constructor
        · exact (norm_add_le _ _).trans_lt
            ((add_le_add (rudinShapiro_norm_bounds k hz).1 (by rw [hs]; exact hq)).trans_lt hsum)
        · exact (norm_sub_le _ _).trans_lt
            ((add_le_add (rudinShapiro_norm_bounds k hz).1 (by rw [hs]; exact hq)).trans_lt hsum)

/-- The stable sequence can be defined directly using any sufficiently
deep first word. The depth `j+1` is convenient and entails no choice. -/
def rudinShapiroCoefficient (j : ℕ) : ℤ := (rudinShapiroP (j + 1)).coeff j

theorem rudinShapiroCoefficient_eq {k j : ℕ} (hj : j < 2 ^ k) :
    rudinShapiroCoefficient j = (rudinShapiroP k).coeff j := by
  have hj' : j < 2 ^ (j + 1) := (show j < 2 ^ j from Nat.lt_two_pow_self).trans_le
    (Nat.pow_le_pow_right (by omega) (by omega))
  by_cases hk : k ≤ j + 1
  · exact rudinShapiroP_stable hk hj
  · exact (rudinShapiroP_stable (by omega) hj').symm

theorem rudinShapiroCoefficient_sign (j : ℕ) :
    rudinShapiroCoefficient j = -1 ∨ rudinShapiroCoefficient j = 1 := by
  exact (rudinShapiro_coefficients (j + 1)).1 j
    ((show j < 2 ^ j from Nat.lt_two_pow_self).trans_le
      (Nat.pow_le_pow_right (by omega) (by omega))) |>.1

def rudinShapiroPrefix (m : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range m, (rudinShapiroCoefficient j : ℂ) * z ^ j

theorem rudinShapiroPrefix_eq {k m : ℕ} (hm : m ≤ 2 ^ k) (z : ℂ) :
    rudinShapiroPrefix m z = rsPrefixEval (rudinShapiroP k) m z := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [rudinShapiroCoefficient_eq ((Finset.mem_range.mp hj).trans_le hm)]

theorem rudinShapiroPrefix_bound {m : ℕ} (hm : 0 < m) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖rudinShapiroPrefix m z‖ < 5 * Real.sqrt m := by
  rw [rudinShapiroPrefix_eq (show m < 2 ^ m from Nat.lt_two_pow_self).le]
  exact (rudinShapiro_prefix_bound m m (show m < 2 ^ m from Nat.lt_two_pow_self).le hm hz).1

end
end Power2ModuleSVP
