module

public import Power2ModuleSVP.Coset.Norm.NewtonSums

/-!
# Root Products

Root products for `lem:reciprocal-resultant`.  Conjugation is used to align
the diagonal factors with radial gaps.  Multiset indices preserve repeated
roots, so no separability premise is needed.

Paper: `paper/power2svp.pdf`, Section 3.2 (Lemmas 2–4, algebraic norm separation).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Power2ModuleSVP

open Polynomial
open scoped BigOperators

noncomputable section

/-- Conjugation preserves the entire root multiset of an integer polynomial. -/
theorem complexPolynomial_roots_conj (p : ℤ[X]) :
    (complexPolynomial p).roots.map (starRingEnd ℂ) =
      (complexPolynomial p).roots := by
  have hm : (complexPolynomial p).map (starRingEnd ℂ) = complexPolynomial p := by
    simp only [complexPolynomial, Polynomial.map_map]
    congr 1
    ext n
    simp
  rw [← (IsAlgClosed.splits (complexPolynomial p)).roots_map, hm]

/-- The normalized reciprocal roots may be indexed by inverse conjugates. -/
theorem roots_normalizedReciprocal_conj {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) :
    (complexPolynomial (normalizedReciprocal p)).roots =
      (complexPolynomial p).roots.map (fun z => ((starRingEnd ℂ) z)⁻¹) := by
  rw [roots_normalizedReciprocal hp hu]
  conv_lhs => rw [← complexPolynomial_roots_conj p]
  rw [Multiset.map_map]
  rfl

/-- The diagonal distance to the inverse conjugate is exactly the radial gap. -/
theorem norm_sub_inv_conj (z : ℂ) (hz : z ≠ 0) :
    ‖z - ((starRingEnd ℂ) z)⁻¹‖ = |‖z‖ - ‖z‖⁻¹| := by
  have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hc : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
  have he : (z - ((starRingEnd ℂ) z)⁻¹) * (starRingEnd ℂ) z =
      ((‖z‖ ^ 2 - 1 : ℝ) : ℂ) := by
    rw [sub_mul, inv_mul_cancel₀ hc, Complex.mul_conj']
    push_cast
    rfl
  have hn := congrArg norm he
  simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs] at hn
  apply (mul_right_cancel₀ hr)
  calc
    _ = |‖z‖ ^ 2 - 1| := hn
    _ = |(‖z‖ - ‖z‖⁻¹) * ‖z‖| := by
      congr 1
      rw [sub_mul, inv_mul_cancel₀ hr, pow_two]
    _ = _ := by rw [abs_mul, abs_of_nonneg (norm_nonneg z)]

/-- A triangle bound for the factors outside the diagonal. -/
theorem norm_sub_inv_conj_le (z w : ℂ) :
    ‖z - ((starRingEnd ℂ) w)⁻¹‖ ≤
      2 * max 1 ‖z‖ * max 1 ‖w‖⁻¹ := by
  have htriangle : ‖z - ((starRingEnd ℂ) w)⁻¹‖ ≤ ‖z‖ + ‖w‖⁻¹ := by
    simpa only [norm_inv, Complex.norm_conj] using norm_sub_le z (((starRingEnd ℂ) w)⁻¹)
  have ha := le_max_right (1 : ℝ) ‖z‖
  have hb := le_max_right (1 : ℝ) ‖w‖⁻¹
  have ha1 := le_max_left (1 : ℝ) ‖z‖
  have hb1 := le_max_left (1 : ℝ) ‖w‖⁻¹
  have h1 := mul_le_mul_of_nonneg_left hb1 (show 0 ≤ max 1 ‖z‖ by positivity)
  have h2 := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ max 1 ‖w‖⁻¹ by positivity)
  nlinarith

private theorem prod_erase_eq_ite {ι M : Type*} [Fintype ι]
    [DecidableEq ι] [CommMonoid M] (b : ι → M) (i : ι) :
    (∏ j ∈ Finset.univ.erase i, b j) = ∏ j, if j = i then 1 else b j := by
  rw [← Finset.prod_erase (f := fun j => if j = i then 1 else b j)
    Finset.univ (a := i) (by simp)]
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

/-- Every index occurs in exactly `card - 1` of the complementary products. -/
theorem prod_prod_erase {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [CommMonoid M] (b : ι → M) :
    (∏ i, ∏ j ∈ Finset.univ.erase i, b j) =
      (∏ j, b j) ^ (Fintype.card ι - 1) := by
  simp_rw [prod_erase_eq_ite]
  rw [Finset.prod_comm, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  calc
    _ = ∏ i ∈ Finset.univ.erase j, b j := by
      rw [prod_erase_eq_ite]
      apply Finset.prod_congr rfl
      intro i _
      simp only [eq_comm]
    _ = _ := by simp

/-- The full product bound with exact radial diagonal factors. -/
theorem prod_norm_sub_inv_conj_le {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (hz : ∀ i, z i ≠ 0) :
    (∏ i, ∏ j, ‖z i - ((starRingEnd ℂ) (z j))⁻¹‖) ≤
      (2 : ℝ) ^ (Fintype.card ι * (Fintype.card ι - 1)) *
        ((∏ i, max 1 ‖z i‖) * (∏ i, max 1 ‖z i‖⁻¹)) ^
          (Fintype.card ι - 1) * ∏ i, |‖z i‖ - ‖z i‖⁻¹| := by
  classical
  have hrow (i : ι) :
      (∏ j, ‖z i - ((starRingEnd ℂ) (z j))⁻¹‖) ≤
        |‖z i‖ - ‖z i‖⁻¹| *
          ((2 * max 1 ‖z i‖) ^ (Fintype.card ι - 1) *
            ∏ j ∈ Finset.univ.erase i, max 1 ‖z j‖⁻¹) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => ‖z i - ((starRingEnd ℂ) (z j))⁻¹‖) (Finset.mem_univ i),
      norm_sub_inv_conj _ (hz i)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      _ ≤ ∏ j ∈ Finset.univ.erase i, 2 * max 1 ‖z i‖ * max 1 ‖z j‖⁻¹ := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro j _
        exact norm_sub_inv_conj_le _ _
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have h := Finset.prod_le_prod₀
    (fun i (_ : i ∈ Finset.univ) => Finset.prod_nonneg (fun j _ => norm_nonneg _))
    (fun i _ => hrow i)
  simp only [Finset.prod_mul_distrib, prod_prod_erase, Finset.prod_pow,
    Finset.prod_const, Finset.card_univ, mul_pow] at h
  rw [← pow_mul] at h
  simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using h

/-- A reciprocal root-evaluation product, indexed by inverse conjugate roots. -/
theorem rootEvaluationProduct_normalizedReciprocal {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) :
    rootEvaluationProduct p (normalizedReciprocal p) =
      ∏ z : (complexPolynomial p).roots, ∏ w : (complexPolynomial p).roots,
        ((z : ℂ) - ((starRingEnd ℂ) (w : ℂ))⁻¹) := by
  let s := (complexPolynomial p).roots
  have he (z : ℂ) :
      (complexPolynomial (normalizedReciprocal p)).eval z =
        ∏ w : s, (z - ((starRingEnd ℂ) (w : ℂ))⁻¹) := by
    have h := (IsAlgClosed.splits
      (complexPolynomial (normalizedReciprocal p))).eval_eq_prod_roots z
    rw [(complexPolynomial_monic (normalizedReciprocal_monic hu)).leadingCoeff,
      one_mul, roots_normalizedReciprocal_conj hp hu, Multiset.map_map] at h
    rw [h]
    simpa only [Function.comp_apply, sub_eq_add_neg, s,
      Finset.prod_eq_multiset_prod] using
      (congrArg Multiset.prod (Multiset.map_univ s
        (fun w : ℂ => z - ((starRingEnd ℂ) w)⁻¹))).symm
  calc
    _ = ∏ z : s, (complexPolynomial (normalizedReciprocal p)).eval (z : ℂ) :=
      (congrArg Multiset.prod
        (Multiset.map_univ s (complexPolynomial (normalizedReciprocal p)).eval)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro z _
      exact he (z : ℂ)

/-- Root disjointness makes the integer reciprocal resultant nonzero. -/
theorem rootEvaluationProduct_normalizedReciprocal_ne_zero {p : ℤ[X]}
    (hp : p.Monic) (hu : HasUnitConstant p) (hroot : NoCommonReciprocalRoot p) :
    rootEvaluationProduct p (normalizedReciprocal p) ≠ 0 := by
  apply Multiset.prod_ne_zero
  intro hzero
  obtain ⟨z, hz, he⟩ := Multiset.mem_map.mp hzero
  have hzroot : (complexPolynomial p).eval z = 0 :=
    (mem_roots (complexPolynomial_monic hp).ne_zero).mp hz
  have hc : (p.coeff 0 : ℂ) ≠ 0 := by
    rcases hu with h | h <;> simp [h]
  apply mul_ne_zero hc (hroot z hzroot)
  simpa only [normalizedReciprocal, complexPolynomial, Polynomial.map_mul,
    Polynomial.map_C, eval_mul, eval_C, Int.coe_castRingHom] using he

/-- For a unit constant coefficient, the inverse-root maximum product is
the same Mahler measure as the forward-root maximum product. -/
theorem prod_max_inv_norm_eq_mahler {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) :
    ((complexPolynomial p).roots.map (fun z => max 1 ‖z‖⁻¹)).prod =
      integerMahlerMeasure p := by
  have hpoint (z : ℂ) (hz : z ∈ (complexPolynomial p).roots) :
      max 1 ‖z‖⁻¹ * ‖z‖ = max 1 ‖z‖ := by
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr (root_ne_zero_of_unitConstant hu hz)
    rcases le_total 1 ‖z‖ with h | h
    · rw [max_eq_left ((inv_le_one₀ hr).mpr h), max_eq_right h, one_mul]
    · rw [max_eq_right ((one_le_inv₀ hr).mpr h), max_eq_left h,
        inv_mul_cancel₀ hr.ne']
  have h := congrArg Multiset.prod (Multiset.map_congr rfl hpoint)
  rw [Multiset.prod_map_mul, prod_norm_roots_eq_one hp hu, mul_one] at h
  rw [h, integerMahlerMeasure, mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    (complexPolynomial_monic hp).leadingCoeff, norm_one, one_mul]

end

end Power2ModuleSVP
