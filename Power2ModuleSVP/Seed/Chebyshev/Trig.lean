module

public import Power2ModuleSVP.Seed.Bernstein
public import Power2ModuleSVP.Seed.Chebyshev.Basic

/-!
# Sine and cosine sums as Laurent polynomials

The centered powers give a direct bridge from ordinary real trigonometric
sums to `HasTrigDegree`, and hence to the sharp Bernstein bounds.

Paper: `paper/power2svp.pdf`, Appendix A (Bernstein and polynomial estimates used in the seed).
-/

@[expose] public section

noncomputable section

namespace Power2ModuleSVP

open Polynomial

/-- Centered polynomial encoding one real sine/cosine mode. -/
def centeredTrigMode (n k : ℕ) (a b : ℝ) : ℂ[X] :=
  C (((a : ℂ) - (b : ℂ) * Complex.I) / 2) * X ^ (n + k) +
    C (((a : ℂ) + (b : ℂ) * Complex.I) / 2) * X ^ (n - k)

theorem centeredTrigMode_degree (n k : ℕ) (a b : ℝ) (hk : k ≤ n) :
    (centeredTrigMode n k a b).degree ≤ (2 * n : ℕ) := by
  apply degree_add_le_of_degree_le
  · exact (degree_C_mul_X_pow_le _ _).trans (by exact_mod_cast (by omega : n + k ≤ 2 * n))
  · exact (degree_C_mul_X_pow_le _ _).trans (by exact_mod_cast (by omega : n - k ≤ 2 * n))

private theorem centeredTrigMode_phase_add (n k : ℕ) (θ : ℝ) :
    Complex.exp (-(n : ℂ) * (θ : ℂ) * Complex.I) *
        Complex.exp ((θ : ℂ) * Complex.I) ^ (n + k) =
      Complex.exp ((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem centeredTrigMode_phase_sub (n k : ℕ) (θ : ℝ) (hk : k ≤ n) :
    Complex.exp (-(n : ℂ) * (θ : ℂ) * Complex.I) *
        Complex.exp ((θ : ℂ) * Complex.I) ^ (n - k) =
      Complex.exp (-(((k : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_add, Nat.cast_sub hk]
  congr 1
  push_cast
  ring

theorem centeredTrigMode_eval (n k : ℕ) (a b θ : ℝ) (hk : k ≤ n) :
    laurentTrig n (centeredTrigMode n k a b) θ =
      ((a * Real.cos (k * θ) + b * Real.sin (k * θ) : ℝ) : ℂ) := by
  unfold laurentTrig centeredTrigMode
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  calc
    _ = (((a : ℂ) - (b : ℂ) * Complex.I) / 2) *
          (Complex.exp (-(n : ℂ) * (θ : ℂ) * Complex.I) *
            Complex.exp ((θ : ℂ) * Complex.I) ^ (n + k)) +
        (((a : ℂ) + (b : ℂ) * Complex.I) / 2) *
          (Complex.exp (-(n : ℂ) * (θ : ℂ) * Complex.I) *
            Complex.exp ((θ : ℂ) * Complex.I) ^ (n - k)) := by ring
    _ = _ := by
      rw [centeredTrigMode_phase_add, centeredTrigMode_phase_sub n k θ hk]
      simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_cos,
        Complex.ofReal_sin, Complex.ofReal_natCast, Complex.cos, Complex.sin]
      ring

/-- A real finite trigonometric sum with arbitrary finite frequency support. -/
def trigSum (s : Finset ℕ) (a b : ℕ → ℝ) (θ : ℝ) : ℝ :=
  ∑ k ∈ s, (a k * Real.cos (k * θ) + b k * Real.sin (k * θ))

/-- The polynomial whose centered unit-circle evaluation is the given sum. -/
def trigSumPolynomial (n : ℕ) (s : Finset ℕ) (a b : ℕ → ℝ) : ℂ[X] :=
  ∑ k ∈ s, centeredTrigMode n k (a k) (b k)

theorem trigSumPolynomial_degree (n : ℕ) (s : Finset ℕ) (a b : ℕ → ℝ)
    (hs : ∀ k ∈ s, k ≤ n) :
    (trigSumPolynomial n s a b).degree ≤ (2 * n : ℕ) := by
  apply (degree_sum_le s _).trans
  exact Finset.sup_le fun k hk => centeredTrigMode_degree n k (a k) (b k) (hs k hk)

theorem trigSumPolynomial_eval (n : ℕ) (s : Finset ℕ) (a b : ℕ → ℝ)
    (hs : ∀ k ∈ s, k ≤ n) (θ : ℝ) :
    laurentTrig n (trigSumPolynomial n s a b) θ = (trigSum s a b θ : ℂ) := by
  simp only [trigSumPolynomial, laurentTrig, eval_finsetSum, Finset.mul_sum]
  change (∑ k ∈ s, laurentTrig n (centeredTrigMode n k (a k) (b k)) θ) = _
  rw [show (trigSum s a b θ : ℂ) =
      ∑ k ∈ s, ((a k * Real.cos (k * θ) + b k * Real.sin (k * θ) : ℝ) : ℂ) by
    simp only [trigSum, Complex.ofReal_sum]]
  exact Finset.sum_congr rfl fun k hk => centeredTrigMode_eval n k (a k) (b k) θ (hs k hk)

theorem hasTrigDegree_trigSum (n : ℕ) (s : Finset ℕ) (a b : ℕ → ℝ)
    (hs : ∀ k ∈ s, k ≤ n) : HasTrigDegree n (trigSum s a b) :=
  ⟨trigSumPolynomial n s a b, trigSumPolynomial_degree n s a b hs,
    fun θ => (trigSumPolynomial_eval n s a b hs θ).symm⟩

/-- Bernstein's inequality in ordinary sine/cosine coefficient notation. -/
theorem bernstein_trigSum (n : ℕ) (s : Finset ℕ) (a b : ℕ → ℝ)
    (hs : ∀ k ∈ s, k ≤ n) {M : ℝ}
    (hM : ∀ θ : ℝ, |trigSum s a b θ| ≤ M) (r : ℕ) (θ : ℝ) :
    |(deriv^[r] (trigSum s a b)) θ| ≤ (n : ℝ) ^ r * M :=
  bernstein_real_iterate (hasTrigDegree_trigSum n s a b hs) hM r θ

theorem hasTrigDegree_cosineSum (n : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ k ∈ s, k ≤ n) :
    HasTrigDegree n (fun θ => ∑ k ∈ s, a k * Real.cos (k * θ)) := by
  have he : trigSum s a 0 = (fun θ => ∑ k ∈ s, a k * Real.cos (k * θ)) := by
    funext θ
    simp [trigSum]
  rw [← he]
  exact hasTrigDegree_trigSum n s a 0 hs

theorem hasTrigDegree_sineSum (n : ℕ) (s : Finset ℕ) (b : ℕ → ℝ)
    (hs : ∀ k ∈ s, k ≤ n) :
    HasTrigDegree n (fun θ => ∑ k ∈ s, b k * Real.sin (k * θ)) := by
  have he : trigSum s 0 b = (fun θ => ∑ k ∈ s, b k * Real.sin (k * θ)) := by
    funext θ
    simp [trigSum]
  rw [← he]
  exact hasTrigDegree_trigSum n s 0 b hs

/-- The exact Chebyshev polynomial used by the grid is a real trig polynomial
of the largest allowed frequency. -/
theorem hasTrigDegree_cosinePolynomial (n : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ k ∈ s, k ≤ n) :
    HasTrigDegree n (fun θ => (cosinePolynomial s a).eval (Real.cos θ)) := by
  simpa only [cosinePolynomial_eval_cos] using hasTrigDegree_cosineSum n s a hs

end Power2ModuleSVP
