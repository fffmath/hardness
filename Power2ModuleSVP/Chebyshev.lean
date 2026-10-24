module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-!
Elementary bounds for the exact Chebyshev evaluation used by the seed grid.
These estimates include both endpoints of the interval; they do not divide
by a sine that could vanish. They are independent of the sharp trigonometric
Bernstein inequality.
-/

@[expose] public section

namespace Power2ModuleSVP

open Polynomial
open scoped BigOperators

noncomputable section

/-- A first-kind Chebyshev polynomial is bounded by one on the closed interval. -/
theorem chebyshev_eval_bound (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(Chebyshev.T ℝ n).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hx.1 hx.2, Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

/-- The second-kind bound, including the points where the sine quotient
formula is undefined, follows from its positive expansion in first-kind
polynomials. -/
theorem chebyshev_U_eval_bound (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(Chebyshev.U ℝ n).eval x| ≤ n + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    norm_num [abs_mul]
    nlinarith [abs_le.mpr hx]
  | more n ih _ =>
    push_cast
    rw [Chebyshev.U_eq_two_mul_T_add_U]
    simp only [eval_add, eval_mul, eval_ofNat]
    calc
      |2 * (Chebyshev.T ℝ (n + 2)).eval x + (Chebyshev.U ℝ n).eval x|
          ≤ 2 * |(Chebyshev.T ℝ (n + 2)).eval x| + |(Chebyshev.U ℝ n).eval x| := by
            simpa [abs_mul] using abs_add_le
              (2 * (Chebyshev.T ℝ (n + 2)).eval x) ((Chebyshev.U ℝ n).eval x)
      _ ≤ 2 * 1 + (n + 1) := by
        gcongr
        exact_mod_cast chebyshev_eval_bound (n + 2) hx
      _ = _ := by ring

/-- The endpoint-sharp derivative bound needed for rational sampling. -/
theorem chebyshev_derivative_eval_bound (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1) 1) :
    |(Chebyshev.T ℝ n).derivative.eval x| ≤ (n : ℝ) ^ 2 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Chebyshev.T_derivative_eq_U]
    simp only [Nat.cast_succ, add_sub_cancel_right, eval_mul, eval_add,
      eval_natCast, eval_one, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_mul]
    have h := chebyshev_U_eval_bound n hx
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
    nlinarith

/-- A finite cosine combination represented by an exact real polynomial. -/
def cosinePolynomial (s : Finset ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ s, Polynomial.C (a j) * Chebyshev.T ℝ j

theorem cosinePolynomial_eval_cos (s : Finset ℕ) (a : ℕ → ℝ) (θ : ℝ) :
    (cosinePolynomial s a).eval (Real.cos θ) =
      ∑ j ∈ s, a j * Real.cos (j * θ) := by
  simp [cosinePolynomial, eval_finsetSum, Chebyshev.T_real_cos]

/-- The weighted coefficient estimate for the polynomial derivative. -/
theorem cosinePolynomial_derivative_bound (s : Finset ℕ) (a : ℕ → ℝ)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(cosinePolynomial s a).derivative.eval x| ≤ ∑ j ∈ s, |a j| * (j : ℝ) ^ 2 := by
  simp only [cosinePolynomial, derivative_sum, derivative_mul, derivative_C,
    zero_mul, zero_add, eval_finsetSum, eval_mul, eval_C]
  calc
    |∑ j ∈ s, a j * (Chebyshev.T ℝ j).derivative.eval x|
        ≤ ∑ j ∈ s, |a j| * |(Chebyshev.T ℝ j).derivative.eval x| := by
          simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
            (fun j => a j * (Chebyshev.T ℝ j).derivative.eval x) s
    _ ≤ ∑ j ∈ s, |a j| * (j : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (chebyshev_derivative_eval_bound j hx) (abs_nonneg _)

/-- Lipschitz control in the cosine coordinate, valid up to the endpoints. -/
theorem cosinePolynomial_eval_sub_bound (s : Finset ℕ) (a : ℕ → ℝ)
    {x y : ℝ} (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc (-1) 1) :
    |(cosinePolynomial s a).eval y - (cosinePolynomial s a).eval x| ≤
      (∑ j ∈ s, |a j| * (j : ℝ) ^ 2) * |y - x| := by
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (f := fun x => (cosinePolynomial s a).eval x)
    (fun x _ => (cosinePolynomial s a).differentiableAt)
    (fun x hx => by simpa using cosinePolynomial_derivative_bound s a hx) hx hy
  simpa only [Real.norm_eq_abs] using h

end

end Power2ModuleSVP
