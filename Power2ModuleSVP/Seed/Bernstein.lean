module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.FieldTheory.Separable
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Sharp Bernstein bounds via polynomial interpolation

The interpolation nodes are the roots of `X^(2*n)+1`.  The functional
`P ↦ P'(1)-n*P(1)` annihilates that polynomial.  Its interpolation weights
are negative real numbers; their absolute values sum to `n`.
This is the finite interpolation proof underlying the trigonometric bound.

Paper: `paper/power2svp.pdf`, Appendix A (Bernstein and polynomial estimates used in the seed).
-/

@[expose] public section

noncomputable section

namespace Power2ModuleSVP

open Polynomial
open scoped ComplexConjugate

/-- The algebraic functional used in the sharp Bernstein inequality. -/
def bernsteinFunctional (n : ℕ) (P : ℂ[X]) : ℂ :=
  P.derivative.eval 1 - (n : ℂ) * P.eval 1

/-- Roots used by the finite interpolation formula. -/
def bernsteinNodes (n : ℕ) : Finset ℂ :=
  ((X : ℂ[X]) ^ (2 * n) + 1).roots.toFinset

private theorem bernsteinModulus_monic {n : ℕ} (hn : 0 < n) :
    ((X : ℂ[X]) ^ (2 * n) + 1).Monic := by
  simpa only [sub_neg_eq_add, map_neg, map_one] using
    (monic_X_pow_sub_C (-1 : ℂ) (by omega : 2 * n ≠ 0))

private theorem bernsteinModulus_nodup {n : ℕ} (hn : 0 < n) :
    (((X : ℂ[X]) ^ (2 * n) + 1).roots).Nodup := by
  apply nodup_roots
  simpa only [sub_neg_eq_add, map_neg, map_one] using
    (separable_X_pow_sub_C (-1 : ℂ) (by exact_mod_cast (by omega : 2 * n ≠ 0))
      (by norm_num))

theorem bernsteinNodes_card {n : ℕ} (hn : 0 < n) :
    (bernsteinNodes n).card = 2 * n := by
  rw [bernsteinNodes, Multiset.toFinset_card_of_nodup (bernsteinModulus_nodup hn),
    IsAlgClosed.card_roots_eq_natDegree]
  simpa only [sub_neg_eq_add, map_neg, map_one] using
    (natDegree_X_pow_sub_C (n := 2 * n) (r := (-1 : ℂ)))

theorem bernsteinNodes_nodal {n : ℕ} (hn : 0 < n) :
    Lagrange.nodal (bernsteinNodes n) id = (X : ℂ[X]) ^ (2 * n) + 1 := by
  rw [Lagrange.nodal, bernsteinNodes]
  rw [← Multiset.toFinset_eq (bernsteinModulus_nodup hn)]
  exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (bernsteinModulus_monic hn) IsAlgClosed.card_roots_eq_natDegree

theorem bernsteinNode_pow {n : ℕ} (hn : 0 < n) {a : ℂ}
    (ha : a ∈ bernsteinNodes n) : a ^ (2 * n) = -1 := by
  have hzero := (mem_roots (bernsteinModulus_monic hn).ne_zero).mp
    (Multiset.mem_toFinset.mp ha)
  simpa [IsRoot.def, eq_neg_iff_add_eq_zero] using hzero

theorem bernsteinNode_norm {n : ℕ} (hn : 0 < n) {a : ℂ}
    (ha : a ∈ bernsteinNodes n) : ‖a‖ = 1 := by
  have he := congrArg norm (bernsteinNode_pow hn ha)
  rw [norm_pow, norm_neg, norm_one] at he
  exact (pow_left_inj₀ (norm_nonneg a) zero_le_one (by omega : 2 * n ≠ 0)).mp
    (by simpa using he)

theorem bernsteinNode_ne_one {n : ℕ} (hn : 0 < n) {a : ℂ}
    (ha : a ∈ bernsteinNodes n) : a ≠ 1 := by
  intro he
  have h := bernsteinNode_pow hn ha
  norm_num [he] at h

private theorem bernsteinNode_weight {n : ℕ} (hn : 0 < n) {a : ℂ}
    (ha : a ∈ bernsteinNodes n) :
    Lagrange.nodalWeight (bernsteinNodes n) id a = -a / (2 * n : ℂ) := by
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal ha, bernsteinNodes_nodal hn]
  simp only [derivative_add, derivative_pow, derivative_X, mul_one, derivative_one,
    add_zero, eval_mul, eval_C, eval_pow, eval_X, id_eq]
  push_cast
  have hpow : a ^ (2 * n - 1) * a = -1 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    exact bernsteinNode_pow hn ha
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  apply inv_eq_of_mul_eq_one_right
  field_simp [hn0]
  linear_combination -hpow

/-- The interpolation weight of the Bernstein functional. -/
theorem bernsteinFunctional_basis {n : ℕ} (hn : 0 < n) {a : ℂ}
    (ha : a ∈ bernsteinNodes n) :
    bernsteinFunctional n (Lagrange.basis (bernsteinNodes n) id a) =
      a / ((n : ℂ) * (1 - a) ^ 2) := by
  let B := Lagrange.basis (bernsteinNodes n) id a
  let w := Lagrange.nodalWeight (bernsteinNodes n) id a
  have hb : (X - C a) * B = C w * ((X : ℂ[X]) ^ (2 * n) + 1) := by
    dsimp [B, w]
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div ha,
      ← Lagrange.nodal_erase_eq_nodal_div ha]
    calc
      _ = C (Lagrange.nodalWeight (bernsteinNodes n) id a) *
          ((X - C a) * Lagrange.nodal ((bernsteinNodes n).erase a) id) := by ring
      _ = _ := by
        congr 1
        exact (Lagrange.nodal_eq_mul_nodal_erase (v := id) ha).symm.trans
          (bernsteinNodes_nodal hn)
  have he := congrArg (fun P : ℂ[X] => P.eval 1) hb
  have hd := congrArg (fun P : ℂ[X] => P.derivative.eval 1) hb
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_add, eval_pow, one_pow,
    eval_one] at he
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
    derivative_add, derivative_pow, derivative_one, add_zero, mul_one, zero_mul,
    zero_add, eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_pow,
    one_pow, one_mul] at hd
  push_cast at hd
  have hw : w = -a / (2 * n : ℂ) := bernsteinNode_weight hn ha
  have hnn : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have han : 1 - a ≠ 0 := sub_ne_zero.mpr (bernsteinNode_ne_one hn ha).symm
  change B.derivative.eval 1 - (n : ℂ) * B.eval 1 = _
  field_simp [hnn, han] at hw ⊢
  linear_combination (n : ℂ) * (1 - a) * hd -
    (n : ℂ) * (1 + (n : ℂ) * (1 - a)) * he - hw

theorem bernsteinFunctional_add (n : ℕ) (P Q : ℂ[X]) :
    bernsteinFunctional n (P + Q) = bernsteinFunctional n P + bernsteinFunctional n Q := by
  simp only [bernsteinFunctional, derivative_add, eval_add]
  ring

theorem bernsteinFunctional_sub (n : ℕ) (P Q : ℂ[X]) :
    bernsteinFunctional n (P - Q) = bernsteinFunctional n P - bernsteinFunctional n Q := by
  simp only [bernsteinFunctional, derivative_sub, eval_sub]
  ring

theorem bernsteinFunctional_C_mul (n : ℕ) (c : ℂ) (P : ℂ[X]) :
    bernsteinFunctional n (C c * P) = c * bernsteinFunctional n P := by
  simp only [bernsteinFunctional, derivative_mul, derivative_C, zero_mul, zero_add,
    eval_mul, eval_C]
  ring

theorem bernsteinFunctional_sum {ι : Type*} (n : ℕ) (s : Finset ι) (P : ι → ℂ[X]) :
    bernsteinFunctional n (∑ i ∈ s, P i) = ∑ i ∈ s, bernsteinFunctional n (P i) := by
  classical
  simp only [bernsteinFunctional, derivative_sum, eval_finsetSum, Finset.mul_sum,
    Finset.sum_sub_distrib]

private theorem bernsteinFunctional_modulus (n : ℕ) :
    bernsteinFunctional n ((X : ℂ[X]) ^ (2 * n) + 1) = 0 := by
  simp [bernsteinFunctional, derivative_pow]
  ring

private theorem bernstein_interpolation_lt {n : ℕ} (hn : 0 < n) (P : ℂ[X])
    (hP : P.degree < (2 * n : ℕ)) :
    bernsteinFunctional n P =
      ∑ a ∈ bernsteinNodes n, a / ((n : ℂ) * (1 - a) ^ 2) * P.eval a := by
  have hp : P.degree < (bernsteinNodes n).card := by rwa [bernsteinNodes_card hn]
  nth_rw 1 [Lagrange.eq_interpolate (v := id) Function.injective_id.injOn hp]
  rw [Lagrange.interpolate_apply, bernsteinFunctional_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [bernsteinFunctional_C_mul, bernsteinFunctional_basis hn ha]
  exact mul_comm _ _

/-- Finite Riesz interpolation, including the limiting highest degree.
The missing interpolation multiple of `X^(2*n)+1` is killed by the functional. -/
theorem bernstein_interpolation {n : ℕ} (hn : 0 < n) (P : ℂ[X])
    (hP : P.degree ≤ (2 * n : ℕ)) :
    bernsteinFunctional n P =
      ∑ a ∈ bernsteinNodes n, a / ((n : ℂ) * (1 - a) ^ 2) * P.eval a := by
  let F := (X : ℂ[X]) ^ (2 * n) + 1
  let Q := P - C (P.coeff (2 * n)) * F
  have hQ : Q.degree < (2 * n : ℕ) := by
    apply (degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    have hk0 : k ≠ 0 := by omega
    by_cases hkm : k = 2 * n
    · simp [Q, F, hkm, coeff_C_mul, coeff_one, (show 2 * n ≠ 0 by omega)]
    · have hpk : P.coeff k = 0 := coeff_eq_zero_of_degree_lt
        (hP.trans_lt (by exact_mod_cast (by omega : 2 * n < k)))
      simp [Q, F, coeff_C_mul, coeff_one, hpk, hkm, hk0]
  have hfun : bernsteinFunctional n Q = bernsteinFunctional n P := by
    dsimp [Q, F]
    rw [bernsteinFunctional_sub, bernsteinFunctional_C_mul,
      bernsteinFunctional_modulus, mul_zero, sub_zero]
  have heval {a : ℂ} (ha : a ∈ bernsteinNodes n) : Q.eval a = P.eval a := by
    simp [Q, F, bernsteinNode_pow hn ha]
  rw [← hfun, bernstein_interpolation_lt hn Q hQ]
  exact Finset.sum_congr rfl fun a ha => by rw [heval ha]

/-- Absolute value of a Riesz weight. -/
def bernsteinWeight (n : ℕ) (a : ℂ) : ℝ :=
  1 / ((n : ℝ) * ‖1 - a‖ ^ 2)

theorem bernsteinWeight_nonneg (n : ℕ) (a : ℂ) : 0 ≤ bernsteinWeight n a := by
  unfold bernsteinWeight
  positivity

theorem bernstein_weight_eq_neg {n : ℕ} (hn : 0 < n) {a : ℂ}
    (ha : a ∈ bernsteinNodes n) :
    a / ((n : ℂ) * (1 - a) ^ 2) = -(bernsteinWeight n a : ℂ) := by
  have hnorm := bernsteinNode_norm hn ha
  have hmul : a * conj a = 1 := by rw [Complex.mul_conj', hnorm]; norm_num
  have hsq : (1 - a) ^ 2 = -a * (‖1 - a‖ ^ 2 : ℝ) := by
    push_cast
    rw [← Complex.mul_conj' (1 - a)]
    simp only [map_sub, map_one]
    linear_combination -(1 - a) * hmul
  have han : 1 - a ≠ 0 := sub_ne_zero.mpr (bernsteinNode_ne_one hn ha).symm
  have ha0 : a ≠ 0 := by intro h; norm_num [h] at hnorm
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnorm0 : (‖1 - a‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr han)
  rw [hsq]
  simp only [bernsteinWeight, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow]
  field_simp

/-- The absolute interpolation weights have total mass exactly the degree. -/
theorem bernsteinWeight_sum {n : ℕ} (hn : 0 < n) :
    ∑ a ∈ bernsteinNodes n, bernsteinWeight n a = (n : ℝ) := by
  have he := bernstein_interpolation hn (1 : ℂ[X]) (by simp)
  simp only [bernsteinFunctional, derivative_one, eval_zero, eval_one, mul_one,
    zero_sub] at he
  have hneg : (-(n : ℂ)) = ∑ a ∈ bernsteinNodes n, -(bernsteinWeight n a : ℂ) := by
    exact he.trans (Finset.sum_congr rfl fun a ha => bernstein_weight_eq_neg hn ha)
  have hr := congrArg Complex.re hneg
  simpa using hr.symm

/-- Sharp polynomial form of Bernstein's inequality. Only values at the
`2*n` interpolation nodes need to be bounded. -/
theorem bernstein_polynomial_bound {n : ℕ} (hn : 0 < n) (P : ℂ[X])
    (hP : P.degree ≤ (2 * n : ℕ)) {M : ℝ}
    (hM : ∀ a ∈ bernsteinNodes n, ‖P.eval a‖ ≤ M) :
    ‖P.derivative.eval 1 - (n : ℂ) * P.eval 1‖ ≤ (n : ℝ) * M := by
  change ‖bernsteinFunctional n P‖ ≤ _
  rw [bernstein_interpolation hn P hP]
  calc
    _ ≤ ∑ a ∈ bernsteinNodes n,
        ‖a / ((n : ℂ) * (1 - a) ^ 2) * P.eval a‖ := norm_sum_le _ _
    _ = ∑ a ∈ bernsteinNodes n, bernsteinWeight n a * ‖P.eval a‖ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [norm_mul, bernstein_weight_eq_neg hn ha, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (bernsteinWeight_nonneg n a)]
    _ ≤ ∑ a ∈ bernsteinNodes n, bernsteinWeight n a * M :=
      Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hM a ha)
        (bernsteinWeight_nonneg n a)
    _ = (n : ℝ) * M := by rw [← Finset.sum_mul, bernsteinWeight_sum hn]

/-- The rotated polynomial inequality on the whole unit circle. -/
theorem bernstein_polynomial_circle_bound (n : ℕ) (P : ℂ[X])
    (hP : P.degree ≤ (2 * n : ℕ)) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ M) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖z * P.derivative.eval z - (n : ℂ) * P.eval z‖ ≤ (n : ℝ) * M := by
  by_cases hn : n = 0
  · subst n
    have hp : P = C (P.coeff 0) := eq_C_of_degree_le_zero (by simpa using hP)
    rw [hp]
    simp
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz
  let Q := P.comp (C z * X)
  have hQ : Q.degree ≤ (2 * n : ℕ) := by
    apply natDegree_le_iff_degree_le.mp
    have hp := natDegree_le_iff_degree_le.mpr hP
    exact (natDegree_comp_le.trans (by simpa [natDegree_C_mul_X z hz0] using hp))
  have hbound : ∀ a ∈ bernsteinNodes n, ‖Q.eval a‖ ≤ M := by
    intro a ha
    simp only [Q, eval_comp, eval_mul, eval_C, eval_X]
    apply hM
    rw [norm_mul, hz, bernsteinNode_norm hn' ha, one_mul]
  have he := bernstein_polynomial_bound hn' Q hQ hbound
  simpa only [Q, derivative_comp, derivative_mul, derivative_C, derivative_X,
    zero_mul, zero_add, mul_one, eval_mul, eval_comp, eval_C, eval_X,
    mul_comm (P.derivative.eval z) z] using he

/-- A degree-`n` Laurent polynomial, evaluated on the unit circle. -/
def laurentTrig (n : ℕ) (P : ℂ[X]) (θ : ℝ) : ℂ :=
  Complex.exp (-(n : ℂ) * (θ : ℂ) * Complex.I) *
    P.eval (Complex.exp ((θ : ℂ) * Complex.I))

theorem laurentTrig_norm (n : ℕ) (P : ℂ[X]) (θ : ℝ) :
    ‖laurentTrig n P θ‖ = ‖P.eval (Complex.exp ((θ : ℂ) * Complex.I))‖ := by
  simp [laurentTrig, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem laurentTrig_hasDerivAt (n : ℕ) (P : ℂ[X]) (θ : ℝ) :
    HasDerivAt (laurentTrig n P)
      (Complex.exp (-(n : ℂ) * (θ : ℂ) * Complex.I) * Complex.I *
        (Complex.exp ((θ : ℂ) * Complex.I) *
          P.derivative.eval (Complex.exp ((θ : ℂ) * Complex.I)) -
          (n : ℂ) * P.eval (Complex.exp ((θ : ℂ) * Complex.I)))) θ := by
  have hphase := (((hasDerivAt_id (θ : ℂ)).const_mul (-(n : ℂ))).mul_const Complex.I).cexp
  have harg := ((hasDerivAt_id (θ : ℂ)).mul_const Complex.I).cexp
  have hp := (P.hasDerivAt _).comp (θ : ℂ) harg
  have h := (hphase.mul hp).comp_ofReal
  convert h using 1
  · rfl
  · simp only [id_eq, mul_one, one_mul, Function.comp_apply]
    ring

/-- Sharp Bernstein inequality for arbitrary complex trigonometric polynomials,
in their exact Laurent representation. -/
theorem bernstein_laurent (n : ℕ) (P : ℂ[X]) (hP : P.degree ≤ (2 * n : ℕ))
    {M : ℝ} (hM : ∀ θ : ℝ, ‖laurentTrig n P θ‖ ≤ M) (θ : ℝ) :
    ‖deriv (laurentTrig n P) θ‖ ≤ (n : ℝ) * M := by
  rw [(laurentTrig_hasDerivAt n P θ).deriv, norm_mul, norm_mul]
  have he : ‖Complex.exp (-(n : ℂ) * (θ : ℂ) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  rw [he, Complex.norm_I, one_mul, one_mul]
  apply bernstein_polynomial_circle_bound n P hP
  · intro z hz
    obtain ⟨t, rfl⟩ := (Complex.norm_eq_one_iff z).mp hz
    simpa only [laurentTrig_norm] using hM t
  · simp

/-- Exact Laurent representation of a real trigonometric polynomial of degree
at most `n`. The equality includes the vanishing of the imaginary part. -/
def HasTrigDegree (n : ℕ) (T : ℝ → ℝ) : Prop :=
  ∃ P : ℂ[X], P.degree ≤ (2 * n : ℕ) ∧ ∀ θ : ℝ, (T θ : ℂ) = laurentTrig n P θ

/-- Sharp Bernstein inequality for real trigonometric polynomials. Stating the
supremum as an arbitrary uniform bound avoids any boundedness side condition
on a conditionally complete supremum. -/
theorem bernstein_real {n : ℕ} {T : ℝ → ℝ} (hT : HasTrigDegree n T)
    {M : ℝ} (hM : ∀ θ : ℝ, |T θ| ≤ M) (θ : ℝ) :
    |deriv T θ| ≤ (n : ℝ) * M := by
  obtain ⟨P, hP, hrepr⟩ := hT
  have hd := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt θ
    (laurentTrig_hasDerivAt n P θ)
  have heq : Complex.reCLM ∘ laurentTrig n P = T := by
    funext t
    rw [Function.comp_apply, ← hrepr t]
    rfl
  rw [heq] at hd
  rw [hd.deriv]
  apply (Complex.abs_re_le_norm _).trans
  have hb := bernstein_laurent n P hP
    (fun t => by simpa only [← hrepr t, Complex.norm_real, Real.norm_eq_abs] using hM t) θ
  rwa [(laurentTrig_hasDerivAt n P θ).deriv] at hb

/-- Polynomial corresponding to angular differentiation. -/
def laurentTrigDerivative (n : ℕ) (P : ℂ[X]) : ℂ[X] :=
  C Complex.I * (X * P.derivative - C (n : ℂ) * P)

theorem laurentTrigDerivative_degree {n : ℕ} {P : ℂ[X]}
    (hP : P.degree ≤ (2 * n : ℕ)) :
    (laurentTrigDerivative n P).degree ≤ (2 * n : ℕ) := by
  apply (degree_le_iff_coeff_zero _ _).mpr
  intro k hk
  have hkNat : 2 * n < k := by exact_mod_cast hk
  cases k with
  | zero => omega
  | succ k =>
    have hpk : P.coeff (k + 1) = 0 := coeff_eq_zero_of_degree_lt (hP.trans_lt hk)
    simp [laurentTrigDerivative, coeff_C_mul, coeff_X_mul, coeff_derivative, hpk]

theorem deriv_laurentTrig (n : ℕ) (P : ℂ[X]) :
    deriv (laurentTrig n P) = laurentTrig n (laurentTrigDerivative n P) := by
  funext θ
  rw [(laurentTrig_hasDerivAt n P θ).deriv]
  simp only [laurentTrig, laurentTrigDerivative, eval_mul, eval_C, eval_sub, eval_X]
  ring

theorem HasTrigDegree.deriv {n : ℕ} {T : ℝ → ℝ} (hT : HasTrigDegree n T) :
    HasTrigDegree n (deriv T) := by
  obtain ⟨P, hP, hrepr⟩ := hT
  refine ⟨laurentTrigDerivative n P, laurentTrigDerivative_degree hP, fun θ => ?_⟩
  have hd := laurentTrig_hasDerivAt n P θ
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ hd
  have heq : Complex.reCLM ∘ laurentTrig n P = T := by
    funext t
    rw [Function.comp_apply, ← hrepr t]
    rfl
  rw [heq] at hr
  have hc := hr.ofReal_comp
  have heqc : (fun t => (T t : ℂ)) = laurentTrig n P := funext hrepr
  rw [heqc] at hc
  rw [hr.deriv]
  have hh := hc.unique hd
  rw [← deriv_laurentTrig, hd.deriv]
  exact hh

theorem HasTrigDegree.iterate_deriv {n : ℕ} {T : ℝ → ℝ} (hT : HasTrigDegree n T)
    (r : ℕ) : HasTrigDegree n (_root_.deriv^[r] T) := by
  induction r with
  | zero => exact hT
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact ih.deriv

/-- Every derivative order has the sharp degree-to-that-order uniform bound. -/
theorem bernstein_real_iterate {n : ℕ} {T : ℝ → ℝ} (hT : HasTrigDegree n T)
    {M : ℝ} (hM : ∀ θ : ℝ, |T θ| ≤ M) (r : ℕ) (θ : ℝ) :
    |(deriv^[r] T) θ| ≤ (n : ℝ) ^ r * M := by
  induction r generalizing θ with
  | zero => simpa using hM θ
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ (n : ℝ) * ((n : ℝ) ^ r * M) :=
        bernstein_real (hT.iterate_deriv r) ih θ
      _ = (n : ℝ) ^ (r + 1) * M := by ring

end Power2ModuleSVP
