module

public import Power2ModuleSVP.Seed.RudinShapiro.Basic
public import Power2ModuleSVP.Seed.Bernstein
import Mathlib.Tactic

/-!
# Derivative

Complex Bernstein estimates for the slowly varying Rudin--Shapiro blocks.
The derivative family includes the scaling of the angle explicitly.

Paper: `paper/power2svp.pdf`, Appendix A.1 (Lemma 9, Rudin–Shapiro waves and small intervals).
-/

@[expose] public section
namespace Power2ModuleSVP
open Polynomial
noncomputable section

/-- All angular derivative orders of a complex Laurent polynomial have the
same Bernstein bound as the real-valued special case. -/
theorem bernstein_complex_laurent_iterate (n : ℕ) (P : ℂ[X])
    (hP : P.degree ≤ (2 * n : ℕ)) {M : ℝ}
    (hM : ∀ θ : ℝ, ‖laurentTrig n P θ‖ ≤ M) (r : ℕ) (θ : ℝ) :
    ‖(_root_.deriv^[r] (laurentTrig n P)) θ‖ ≤ (n : ℝ) ^ r * M := by
  induction r generalizing P M with
  | zero => simpa using hM θ
  | succ r ih =>
    rw [Function.iterate_succ_apply, deriv_laurentTrig]
    calc
      _ ≤ (n : ℝ) ^ r * ((n : ℝ) * M) :=
        ih (laurentTrigDerivative n P) (laurentTrigDerivative_degree hP)
          (fun t => by rw [← deriv_laurentTrig]; exact bernstein_laurent n P hP hM t)
      _ = _ := by rw [pow_succ]; ring

/-- Centering an ordinary polynomial introduces only zero coefficients. -/
def rsCenteredPolynomial (n : ℕ) (p : ℤ[X]) : ℂ[X] :=
  X ^ n * p.map (Int.castRingHom ℂ)

theorem rsCenteredPolynomial_degree {n : ℕ} {p : ℤ[X]} (hp : p.natDegree ≤ n) :
    (rsCenteredPolynomial n p).degree ≤ (2 * n : ℕ) := by
  apply natDegree_le_iff_degree_le.mp
  calc
    (rsCenteredPolynomial n p).natDegree ≤ n + p.natDegree := by
      exact natDegree_mul_le.trans (Nat.add_le_add (natDegree_X_pow_le n) natDegree_map_le)
    _ ≤ 2 * n := by omega

theorem rsCenteredPolynomial_eval (n : ℕ) (p : ℤ[X]) (θ : ℝ) :
    laurentTrig n (rsCenteredPolynomial n p) θ =
      rsEval p (Complex.exp ((θ : ℂ) * Complex.I)) := by
  unfold laurentTrig rsCenteredPolynomial
  simp only [eval_mul, eval_pow, eval_X, ← eval₂_eq_eval_map]
  rw [← mul_assoc]
  have hphase : Complex.exp (-(n : ℂ) * (θ : ℂ) * Complex.I) *
      Complex.exp ((θ : ℂ) * Complex.I) ^ n = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    ring
  rw [hphase, one_mul]
  rfl

/-- Exact scaled angular derivative family of a centered polynomial. -/
def rsScaledDerivative (n : ℕ) (P : ℂ[X]) (scale : ℝ) (r : ℕ) (x : ℝ) : ℂ :=
  (scale : ℂ) ^ r *
    laurentTrig n ((laurentTrigDerivative n)^[r] P) (scale * x)

theorem rsScaledDerivative_hasDerivAt (n : ℕ) (P : ℂ[X]) (scale : ℝ)
    (r : ℕ) (x : ℝ) :
    HasDerivAt (rsScaledDerivative n P scale r)
      (rsScaledDerivative n P scale (r + 1) x) x := by
  let Q := (laurentTrigDerivative n)^[r] P
  have hd : HasDerivAt (laurentTrig n Q)
      (laurentTrig n (laurentTrigDerivative n Q) (scale * x)) (scale * x) := by
    rw [← deriv_laurentTrig]
    exact (laurentTrig_hasDerivAt n Q (scale * x)).differentiableAt.hasDerivAt
  have hc := hd.scomp x ((hasDerivAt_id x).const_mul scale)
  have hh := hc.const_mul ((scale : ℂ) ^ r)
  convert! hh using 1
  simp only [rsScaledDerivative, Function.iterate_succ_apply', Q, Complex.real_smul,
    mul_one, pow_succ, mul_assoc]

theorem rsScaledDerivative_eq_iterate (n : ℕ) (P : ℂ[X]) (scale : ℝ) (r : ℕ) :
    rsScaledDerivative n P scale r =
      _root_.deriv^[r] (fun x => laurentTrig n P (scale * x)) := by
  induction r with
  | zero => funext x; simp [rsScaledDerivative]
  | succ r ih =>
    rw [Function.iterate_succ_apply', ← ih]
    exact funext (fun x => (rsScaledDerivative_hasDerivAt n P scale r x).deriv.symm)

theorem rsScaledDerivative_bound (n : ℕ) (P : ℂ[X])
    (hP : P.degree ≤ (2 * n : ℕ)) {M : ℝ}
    (hM : ∀ θ : ℝ, ‖laurentTrig n P θ‖ ≤ M) (scale : ℝ) (r : ℕ) (x : ℝ) :
    ‖rsScaledDerivative n P scale r x‖ ≤ (|scale| * n) ^ r * M := by
  have hrepr : ∀ s : ℕ,
      (_root_.deriv^[s] (laurentTrig n P)) =
        laurentTrig n ((laurentTrigDerivative n)^[s] P) := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih =>
      rw [Function.iterate_succ_apply', ih, deriv_laurentTrig,
        Function.iterate_succ_apply']
  have hb := bernstein_complex_laurent_iterate n P hP hM r (scale * x)
  rw [hrepr r] at hb
  unfold rsScaledDerivative
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |scale| ^ r * ((n : ℝ) ^ r * M) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- Both starting blocks satisfy the exact derivative-rate bound used in
the slowly varying two-frequency wave. -/
theorem rudinShapiro_scaled_derivative_bounds (k : ℕ) (scale : ℝ) (r : ℕ) (x : ℝ) :
    ‖rsScaledDerivative (2 ^ k) (rsCenteredPolynomial (2 ^ k) (rudinShapiroP k))
        scale r x‖ ≤ (|scale| * (2 : ℝ) ^ k) ^ r * Real.sqrt ((2 : ℝ) ^ (k + 1)) ∧
    ‖rsScaledDerivative (2 ^ k) (rsCenteredPolynomial (2 ^ k) (rudinShapiroQ k))
        scale r x‖ ≤ (|scale| * (2 : ℝ) ^ k) ^ r * Real.sqrt ((2 : ℝ) ^ (k + 1)) := by
  have hp : (rudinShapiroP k).natDegree ≤ 2 ^ k := by
    rw [(rudinShapiro_natDegree k).1]
    exact Nat.sub_le _ _
  have hq : (rudinShapiroQ k).natDegree ≤ 2 ^ k := by
    rw [(rudinShapiro_natDegree k).2]
    exact Nat.sub_le _ _
  constructor
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      rsScaledDerivative_bound (2 ^ k) _ (rsCenteredPolynomial_degree hp)
        (fun θ => by
          rw [rsCenteredPolynomial_eval]
          exact (rudinShapiro_norm_bounds k (by simp)).1) scale r x
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      rsScaledDerivative_bound (2 ^ k) _ (rsCenteredPolynomial_degree hq)
        (fun θ => by
          rw [rsCenteredPolynomial_eval]
          exact (rudinShapiro_norm_bounds k (by simp)).2) scale r x

/-- With the manuscript's block spacing, normalization leaves the fixed
derivative rate `1/1024` at every order. -/
theorem rudinShapiro_slow_block_bounds (k r : ℕ) (x : ℝ) :
    ‖rsScaledDerivative (2 ^ k) (rsCenteredPolynomial (2 ^ k) (rudinShapiroP k))
        (1 / (2 : ℝ) ^ (k + 10)) r x‖ / Real.sqrt ((2 : ℝ) ^ (k + 1)) ≤
      (1 / 1024 : ℝ) ^ r ∧
    ‖rsScaledDerivative (2 ^ k) (rsCenteredPolynomial (2 ^ k) (rudinShapiroQ k))
        (1 / (2 : ℝ) ^ (k + 10)) r x‖ / Real.sqrt ((2 : ℝ) ^ (k + 1)) ≤
      (1 / 1024 : ℝ) ^ r := by
  have hs : |1 / (2 : ℝ) ^ (k + 10)| * (2 : ℝ) ^ k = 1 / 1024 := by
    rw [abs_of_pos (by positivity), pow_add]
    norm_num
  have hb := rudinShapiro_scaled_derivative_bounds k (1 / (2 : ℝ) ^ (k + 10)) r x
  rw [hs] at hb
  have hp : 0 < Real.sqrt ((2 : ℝ) ^ (k + 1)) := Real.sqrt_pos.2 (by positivity)
  exact ⟨(div_le_iff₀ hp).2 hb.1, (div_le_iff₀ hp).2 hb.2⟩

end
end Power2ModuleSVP
