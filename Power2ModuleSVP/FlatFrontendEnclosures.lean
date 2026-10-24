import Power2ModuleSVP.FlatFrontendDerivatives

/-! Certified remainder formulas for rational samples. Turning these
formulas into the fixed per-degree tolerances is a separate finite bound. -/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators

theorem chebyshevPair_spec (n : ℕ) (q : ℚ) :
    (chebyshevPair n q).1 = (Polynomial.Chebyshev.T ℚ n).eval q ∧
    (chebyshevPair n q).2 = (Polynomial.Chebyshev.T ℚ (n + 1)).eval q := by
  induction n with
  | zero => simp [chebyshevPair]
  | succ n ih =>
    constructor
    · simpa only [chebyshevPair, Nat.cast_add, Nat.cast_one] using ih.2
    · simp only [chebyshevPair, ih.1, ih.2, Nat.cast_add, Nat.cast_one]
      rw [show (n : ℤ) + 1 + 1 = n + 2 by omega, Polynomial.Chebyshev.T_add_two]
      simp

/-- Exact agreement of the rational evaluator with an integer Chebyshev
polynomial. No numerical test is made against a real coefficient. -/
noncomputable def cosinePolynomial (N : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range N, Polynomial.C (cosineCoefficient N (j + 1)) *
    Polynomial.Chebyshev.T ℤ (2 * (j + 1))

theorem cosinePolynomialValue_spec (N : ℕ) (q : ℚ) :
    cosinePolynomialValue N q =
      ((cosinePolynomial N).map (Int.castRingHom ℚ)).eval q := by
  simp [cosinePolynomialValue, list_sum_range, cosinePolynomial, chebyshevPair_spec,
    Polynomial.map_sum, Polynomial.Chebyshev.map_T, Polynomial.eval_finsetSum]

def phaseTaylor (ell n : ℕ) (q : ℚ) : ℚ :=
  (phase ell).1 * sinTaylor n q + (phase ell).2 * cosTaylor n q

theorem phaseTaylor_error (ell : ℕ) {n : ℕ} {q : ℚ}
    (h : |q| / (n + 1 : ℚ) ≤ 1 / 2) :
    |jetSin ell (q : ℝ) - (phaseTaylor ell n q : ℝ)| ≤ (taylorError n q : ℝ) := by
  have hh := sin_cos_taylor_error h
  rcases phase_cases ell with he | he | he | he
  · simpa [jetSin, phaseTaylor, he] using hh.2
  · simpa [jetSin, phaseTaylor, he] using hh.1
  · simpa [jetSin, phaseTaylor, he, neg_add_eq_sub, abs_sub_comm] using hh.2
  · simpa [jetSin, phaseTaylor, he, neg_add_eq_sub, abs_sub_comm] using hh.1

theorem jetSin_lipschitz (ell : ℕ) (x y : ℝ) :
    |jetSin ell x - jetSin ell y| ≤ |x - y| := by
  rcases phase_cases ell with he | he | he | he
  · simpa [jetSin, he] using Real.abs_sin_sub_sin_le x y
  · simpa [jetSin, he] using Real.abs_cos_sub_cos_le x y
  · simpa [jetSin, he, neg_add_eq_sub, abs_sub_comm] using Real.abs_sin_sub_sin_le x y
  · simpa [jetSin, he, neg_add_eq_sub, abs_sub_comm] using Real.abs_cos_sub_cos_le x y

/-- A rational multiple of pi has both a finite Taylor error and an exact
Machin-series error. This formula also applies to every grid endpoint. -/
theorem phaseTaylor_pi_error (ell n p : ℕ) (r : ℚ)
    (h : |r * piTaylor p| / (n + 1 : ℚ) ≤ 1 / 2) :
    |jetSin ell ((r : ℝ) * Real.pi) - (phaseTaylor ell n (r * piTaylor p) : ℝ)| ≤
      (|r| * piError p + taylorError n (r * piTaylor p) : ℚ) := by
  have ht := phaseTaylor_error ell h
  have hl := jetSin_lipschitz ell ((r : ℝ) * Real.pi) ((r * piTaylor p : ℚ) : ℝ)
  have hp := mul_le_mul_of_nonneg_left (pi_taylor_error p) (abs_nonneg (r : ℝ))
  have he : |(r : ℝ) * Real.pi - ((r * piTaylor p : ℚ) : ℝ)| =
      |(r : ℝ)| * |Real.pi - (piTaylor p : ℝ)| := by
    push_cast
    rw [← mul_sub, abs_mul]
  rw [he] at hl
  have hh := abs_sub_le (jetSin ell ((r : ℝ) * Real.pi))
    (jetSin ell ((r * piTaylor p : ℚ) : ℝ)) (phaseTaylor ell n (r * piTaylor p) : ℝ)
  have hbound := hh.trans (add_le_add (hl.trans hp) ht)
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_abs] using hbound

end FlatFrontend
end Power2ModuleSVP
