module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-!
# The integer Rudin–Shapiro recursion

Define the paired integer coefficient polynomials, prove their sign coefficients and stable
prefixes, and establish their unit-circle norm identity and bounds for the flat-seed
construction.

Paper: `paper/power2svp.pdf`, Appendix A.1 (Lemma 9, Rudin–Shapiro waves and small intervals).
-/

@[expose] public section

namespace Power2ModuleSVP

open Polynomial

noncomputable section

/-- Both members of the recursion, constructed together. -/
def rudinShapiroPair : ℕ → ℤ[X] × ℤ[X]
  | 0 => (1, 1)
  | k + 1 =>
    let p := rudinShapiroPair k
    (p.1 + X ^ (2 ^ k) * p.2, p.1 - X ^ (2 ^ k) * p.2)

/-- The first integer polynomial in the Rudin–Shapiro recursion. -/
def rudinShapiroP (k : ℕ) : ℤ[X] := (rudinShapiroPair k).1

/-- The second integer polynomial in the Rudin–Shapiro recursion. -/
def rudinShapiroQ (k : ℕ) : ℤ[X] := (rudinShapiroPair k).2

@[simp] theorem rudinShapiroP_zero : rudinShapiroP 0 = 1 := rfl
@[simp] theorem rudinShapiroQ_zero : rudinShapiroQ 0 = 1 := rfl

theorem rudinShapiroP_succ (k : ℕ) :
    rudinShapiroP (k + 1) = rudinShapiroP k + X ^ (2 ^ k) * rudinShapiroQ k := rfl

theorem rudinShapiroQ_succ (k : ℕ) :
    rudinShapiroQ (k + 1) = rudinShapiroP k - X ^ (2 ^ k) * rudinShapiroQ k := rfl

/-- Simultaneous sign and support specification, including the zero tail. -/
theorem rudinShapiro_coefficients (k : ℕ) :
    (∀ j < 2 ^ k,
      ((rudinShapiroP k).coeff j = -1 ∨ (rudinShapiroP k).coeff j = 1) ∧
      ((rudinShapiroQ k).coeff j = -1 ∨ (rudinShapiroQ k).coeff j = 1)) ∧
    (∀ j, 2 ^ k ≤ j →
      (rudinShapiroP k).coeff j = 0 ∧ (rudinShapiroQ k).coeff j = 0) := by
  induction k with
  | zero =>
    constructor
    · intro j hj
      have : j = 0 := by simpa using hj
      subst j
      simp
    · intro j hj
      have hj0 : j ≠ 0 := by norm_num at hj; omega
      simp [Polynomial.coeff_one, hj0]
  | succ k ih =>
    constructor
    · intro j hj
      rw [pow_succ] at hj
      simp only [rudinShapiroP_succ, rudinShapiroQ_succ, coeff_add, coeff_sub,
        coeff_X_pow_mul']
      by_cases hjk : j < 2 ^ k
      · simp only [ite_eq_right (by omega : ¬ 2 ^ k ≤ j), add_zero, sub_zero]
        exact ⟨(ih.1 j hjk).1, (ih.1 j hjk).1⟩
      · have hjk' : 2 ^ k ≤ j := by omega
        have hr : j - 2 ^ k < 2 ^ k := by omega
        rw [ite_eq_left hjk', (ih.2 j hjk').1, zero_add, zero_sub]
        rcases (ih.1 (j - 2 ^ k) hr).2 with h | h <;> simp [h]
    · intro j hj
      rw [pow_succ] at hj
      have hjk : 2 ^ k ≤ j := by omega
      have hr : 2 ^ k ≤ j - 2 ^ k := by omega
      simp only [rudinShapiroP_succ, rudinShapiroQ_succ, coeff_add, coeff_sub,
        coeff_X_pow_mul', ite_eq_left hjk, (ih.2 j hjk).1,
        (ih.2 (j - 2 ^ k) hr).2, add_zero, sub_zero]
      trivial

theorem rudinShapiro_natDegree (k : ℕ) :
    (rudinShapiroP k).natDegree = 2 ^ k - 1 ∧
    (rudinShapiroQ k).natDegree = 2 ^ k - 1 := by
  have hpos : 0 < 2 ^ k := by positivity
  have hs := rudinShapiro_coefficients k
  have hp : (rudinShapiroP k).coeff (2 ^ k - 1) ≠ 0 := by
    rcases (hs.1 (2 ^ k - 1) (Nat.sub_lt hpos (by omega))).1 with h | h <;>
      rw [h] <;> norm_num
  have hq : (rudinShapiroQ k).coeff (2 ^ k - 1) ≠ 0 := by
    rcases (hs.1 (2 ^ k - 1) (Nat.sub_lt hpos (by omega))).2 with h | h <;>
      rw [h] <;> norm_num
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun j hj => (hs.2 j (by omega)).1)) hp,
    natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun j hj => (hs.2 j (by omega)).2)) hq⟩

/-- Low coefficients of the first member never change in subsequent steps. -/
theorem rudinShapiroP_stable {k l j : ℕ} (hkl : k ≤ l) (hj : j < 2 ^ k) :
    (rudinShapiroP l).coeff j = (rudinShapiroP k).coeff j := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    have hjl : j < 2 ^ l := hj.trans_le (Nat.pow_le_pow_right (by omega) hkl)
    simp only [rudinShapiroP_succ, coeff_add, coeff_X_pow_mul',
      ite_eq_right (by omega : ¬ 2 ^ l ≤ j), add_zero, ih]

/-- Evaluation in the complex numbers without changing the integer recursion. -/
def rsEval (p : ℤ[X]) (z : ℂ) : ℂ := p.eval₂ (Int.castRingHom ℂ) z

@[simp] theorem rsEval_one (z : ℂ) : rsEval 1 z = 1 := by simp [rsEval]
@[simp] theorem rsEval_add (p q : ℤ[X]) (z : ℂ) :
    rsEval (p + q) z = rsEval p z + rsEval q z := by simp [rsEval]
@[simp] theorem rsEval_sub (p q : ℤ[X]) (z : ℂ) :
    rsEval (p - q) z = rsEval p z - rsEval q z := by simp [rsEval]
@[simp] theorem rsEval_shift (p : ℤ[X]) (n : ℕ) (z : ℂ) :
    rsEval (X ^ n * p) z = z ^ n * rsEval p z := by simp [rsEval]

/-- The exact circle identity; the norm here is the ordinary complex norm. -/
theorem rudinShapiro_norm_identity (k : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖rsEval (rudinShapiroP k) z‖ ^ 2 +
      ‖rsEval (rudinShapiroQ k) z‖ ^ 2 = (2 : ℝ) ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [rudinShapiroP_succ, rudinShapiroQ_succ, rsEval_add, rsEval_sub,
      rsEval_shift]
    rw [parallelogram_law_with_norm ℂ, norm_mul, norm_pow, hz, one_pow, one_mul,
      ih, pow_succ]
    ring

theorem rudinShapiro_norm_bounds (k : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖rsEval (rudinShapiroP k) z‖ ≤ Real.sqrt ((2 : ℝ) ^ (k + 1)) ∧
    ‖rsEval (rudinShapiroQ k) z‖ ≤ Real.sqrt ((2 : ℝ) ^ (k + 1)) := by
  have h := rudinShapiro_norm_identity k hz
  constructor <;> apply (Real.le_sqrt (norm_nonneg _) (by positivity)).2 <;>
    nlinarith [sq_nonneg ‖rsEval (rudinShapiroP k) z‖,
      sq_nonneg ‖rsEval (rudinShapiroQ k) z‖]

/-- The two separated blocks have the stronger joint bound furnished by
the norm identity, rather than the sum of two individual bounds. -/
theorem rudinShapiro_two_block_bound (k a b : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖z ^ a * rsEval (rudinShapiroP k) z +
      z ^ b * rsEval (rudinShapiroQ k) z‖ ≤ Real.sqrt ((2 : ℝ) ^ (k + 2)) := by
  have hnorm := rudinShapiro_norm_identity k hz
  have hn := norm_add_le (z ^ a * rsEval (rudinShapiroP k) z)
    (z ^ b * rsEval (rudinShapiroQ k) z)
  simp only [norm_mul, norm_pow, hz, one_pow, one_mul] at hn
  have hsum : ‖rsEval (rudinShapiroP k) z‖ + ‖rsEval (rudinShapiroQ k) z‖ ≤
      Real.sqrt ((2 : ℝ) ^ (k + 2)) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    have hpow : (2 : ℝ) ^ (k + 2) = 2 * (2 : ℝ) ^ (k + 1) := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring
    nlinarith [sq_nonneg
      (‖rsEval (rudinShapiroP k) z‖ - ‖rsEval (rudinShapiroQ k) z‖)]
  exact hn.trans hsum

theorem rudinShapiro_real_part_bound (k a b : ℕ) {z : ℂ} (hz : ‖z‖ = 1)
    {N : ℕ} (hN : 2 ^ (k + 2) ≤ N) :
    |(z ^ a * rsEval (rudinShapiroP k) z +
      z ^ b * rsEval (rudinShapiroQ k) z).re| ≤ Real.sqrt N := by
  apply (Complex.abs_re_le_norm _).trans
  apply (rudinShapiro_two_block_bound k a b hz).trans
  apply Real.sqrt_le_sqrt
  exact_mod_cast hN

/-- Endpoint values after an odd number of recursion steps. They are the
axis values used in the interval exclusion argument. -/
theorem rudinShapiro_odd_endpoints (r : ℕ) :
    rsEval (rudinShapiroP (2 * r + 1)) 1 = (2 : ℂ) ^ (r + 1) ∧
    rsEval (rudinShapiroQ (2 * r + 1)) 1 = 0 ∧
    rsEval (rudinShapiroP (2 * r + 1)) (-1) = 0 ∧
    rsEval (rudinShapiroQ (2 * r + 1)) (-1) = (2 : ℂ) ^ (r + 1) := by
  induction r with
  | zero => norm_num [rudinShapiroP_succ, rudinShapiroQ_succ, rsEval]
  | succ r ih =>
    have hk : 2 * (r + 1) + 1 = (2 * r + 1) + 1 + 1 := by omega
    rw [hk]
    have hpow₁ : (-1 : ℂ) ^ (2 ^ (2 * r + 1)) = 1 := by
      rw [pow_succ, Nat.mul_comm, pow_mul]
      norm_num
    have hpow₂ : (-1 : ℂ) ^ (2 ^ (2 * r + 1 + 1)) = 1 := by
      rw [pow_succ, Nat.mul_comm, pow_mul]
      norm_num
    have hP (k : ℕ) (z : ℂ) : rsEval (rudinShapiroP (k + 1)) z =
        rsEval (rudinShapiroP k) z + z ^ (2 ^ k) * rsEval (rudinShapiroQ k) z := by
      rw [rudinShapiroP_succ, rsEval_add, rsEval_shift]
    have hQ (k : ℕ) (z : ℂ) : rsEval (rudinShapiroQ (k + 1)) z =
        rsEval (rudinShapiroP k) z - z ^ (2 ^ k) * rsEval (rudinShapiroQ k) z := by
      rw [rudinShapiroQ_succ, rsEval_sub, rsEval_shift]
    simp only [hP (2 * r + 1 + 1), hQ (2 * r + 1 + 1),
      hP (2 * r + 1), hQ (2 * r + 1), one_pow, one_mul, hpow₁, hpow₂,
      ih.1, ih.2.1, ih.2.2.1, ih.2.2.2]
    rw [pow_succ (2 : ℂ) (r + 1)]
    constructor
    · ring
    constructor
    · ring
    constructor
    · ring
    · ring

end

end Power2ModuleSVP
