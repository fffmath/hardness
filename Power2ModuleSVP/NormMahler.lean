module

public import Power2ModuleSVP.NormMahlerAux

/-!
# The elementary Mahler estimate

This file discharges `ElementaryMahlerHypothesis` using the integral Newton
witness from `NormMahlerAux` and real logarithms of the root moduli.  All root
multiplicities are retained.

The inverse power sum is conjugated before estimating its individual terms:
the resulting rootwise comparison depends only on the moduli.  This is the
conjugation step needed in `lem:elementary-mahler`; no irreducibility or
squarefreeness assumption is used.  No mathematical gap was found here.
-/

@[expose] public section

namespace Power2ModuleSVP

open Polynomial
open scoped BigOperators

noncomputable section

private theorem abs_log_eq_two_log_max_sub_log {r : ℝ} (hr : 0 < r) :
    |Real.log r| = 2 * Real.log (max 1 r) - Real.log r := by
  rcases le_total 1 r with h | h
  · rw [max_eq_right h, abs_of_nonneg (Real.log_nonneg h)]
    ring
  · rw [max_eq_left h, Real.log_one, abs_of_nonpos (Real.log_nonpos hr.le h)]
    ring

/-- The logarithms of the root moduli sum to zero for a unit constant term. -/
theorem sum_log_norm_roots_eq_zero {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) :
    ((complexPolynomial p).roots.map (fun z => Real.log ‖z‖)).sum = 0 := by
  have h := Real.log_multiset_prod (s := (complexPolynomial p).roots.map norm)
    (by
      intro r hr
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hr
      exact (norm_pos_iff.mpr (root_ne_zero_of_unitConstant hu hz)).ne')
  rw [prod_norm_roots_eq_one hp hu, Real.log_one] at h
  simpa only [Multiset.map_map, Function.comp_def] using h.symm

/-- The sum of absolute radial logarithms is twice the logarithmic Mahler
measure. -/
theorem sum_abs_log_norm_roots {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) :
    ((complexPolynomial p).roots.map (fun z => |Real.log ‖z‖|)).sum =
      2 * Real.log (integerMahlerMeasure p) := by
  have hM : ((complexPolynomial p).roots.map (fun z => Real.log (max 1 ‖z‖))).sum =
      Real.log (integerMahlerMeasure p) := by
    rw [integerMahlerMeasure, mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
      (complexPolynomial_monic hp).leadingCoeff, norm_one, one_mul,
      Real.log_multiset_prod (by
        intro r hr
        obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hr
        exact (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖z‖)).ne')]
    simp only [Multiset.map_map, Function.comp_def]
  have hpoint := Multiset.map_congr rfl (fun z hz =>
    abs_log_eq_two_log_max_sub_log
      (norm_pos_iff.mpr (root_ne_zero_of_unitConstant hu hz)))
  rw [hpoint, Multiset.sum_map_sub, Multiset.sum_map_mul_left,
    hM, sum_log_norm_roots_eq_zero hp hu, sub_zero]

private theorem abs_le_half_sum_abs_of_sum_eq_zero {s : Multiset ℝ}
    (hs : s.sum = 0) {u : ℝ} (hu : u ∈ s) :
    2 * |u| ≤ (s.map abs).sum := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hu
  simp only [Multiset.sum_cons] at hs
  have ht : t.sum = -u := by linarith
  have hb := Multiset.abs_sum_le_sum_abs (s := t)
  rw [ht, abs_neg] at hb
  simpa only [Multiset.map_cons, Multiset.sum_cons] using
    (show 2 * |u| ≤ |u| + (t.map abs).sum by linarith)

/-- Each individual radial logarithm is bounded by the logarithmic Mahler
measure; the product-one constraint controls roots inside the circle too. -/
theorem abs_log_norm_root_le {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) {z : ℂ} (hz : z ∈ (complexPolynomial p).roots) :
    |Real.log ‖z‖| ≤ Real.log (integerMahlerMeasure p) := by
  have hb := abs_le_half_sum_abs_of_sum_eq_zero
    (sum_log_norm_roots_eq_zero hp hu) (Multiset.mem_map_of_mem _ hz)
  simp only [Multiset.map_map, Function.comp_def] at hb
  rw [sum_abs_log_norm_roots hp hu] at hb
  linarith

private theorem abs_exp_sub_exp_neg_le (t : ℝ) :
    |Real.exp t - Real.exp (-t)| ≤ 2 * Real.exp |t| * |t| := by
  have hpos (a : ℝ) (ha : 0 ≤ a) :
      Real.exp a - Real.exp (-a) ≤ 2 * Real.exp a * a := by
    have he := Real.add_one_le_exp (-2 * a)
    have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos a).le
    have hmul : Real.exp a * Real.exp (-2 * a) = Real.exp (-a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hmul] at hm
    nlinarith
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, abs_of_nonneg (by
      apply sub_nonneg.mpr
      exact Real.exp_le_exp.mpr (by linarith))]
    exact hpos t ht
  · have htn : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos htn, abs_of_nonpos (by
      apply sub_nonpos.mpr
      exact Real.exp_le_exp.mpr (by linarith))]
    simpa only [neg_neg, neg_sub] using hpos (-t) (neg_nonneg.mpr htn)

/-- The norm of the difference between a complex number and its inverse
conjugate depends only on its modulus. -/
theorem norm_sub_conj_inv {w : ℂ} (hw : w ≠ 0) :
    ‖w - (starRingEnd ℂ) w⁻¹‖ = |‖w‖ - ‖w‖⁻¹| := by
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hi : (starRingEnd ℂ) w⁻¹ = w * (((‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [RCLike.inv_def w, map_mul]
    simp
  have he : w - w * (((‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) =
      w * ((1 - (‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hi, he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ = |‖w‖ * (1 - (‖w‖ ^ 2)⁻¹)| := by rw [abs_mul, abs_of_pos hr]
    _ = _ := by congr 1; field_simp

/-- A rootwise radial power estimate. -/
theorem norm_pow_sub_conj_inv_pow_le {z : ℂ} (hz : z ≠ 0) (m : ℕ)
    {T : ℝ} (hT : |Real.log ‖z‖| ≤ T) :
    ‖z ^ m - (starRingEnd ℂ) (z⁻¹ ^ m)‖ ≤
      2 * (m : ℝ) * Real.exp ((m : ℝ) * T) * |Real.log ‖z‖| := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnorm : ‖z ^ m - (starRingEnd ℂ) (z⁻¹ ^ m)‖ =
      |Real.exp ((m : ℝ) * Real.log ‖z‖) -
        Real.exp (-((m : ℝ) * Real.log ‖z‖))| := by
    rw [inv_pow, norm_sub_conj_inv (pow_ne_zero _ hz), norm_pow,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log hr]
  rw [hnorm]
  have habs : |(m : ℝ) * Real.log ‖z‖| = (m : ℝ) * |Real.log ‖z‖| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
  calc
    _ ≤ 2 * Real.exp |(m : ℝ) * Real.log ‖z‖| *
        |(m : ℝ) * Real.log ‖z‖| := abs_exp_sub_exp_neg_le _
    _ ≤ 2 * Real.exp ((m : ℝ) * T) * ((m : ℝ) * |Real.log ‖z‖|) := by
      rw [habs]
      gcongr
    _ = _ := by ring

/-- The difference of a positive and inverse power sum is bounded by Mahler
measure when the inverse power sum is an integer. -/
theorem norm_power_sum_sub_inverse_le {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) (m : ℕ) (b : ℤ)
    (hb : ((complexPolynomial p).roots.map (fun z => z⁻¹ ^ m)).sum = (b : ℂ)) :
    ‖((complexPolynomial p).roots.map (fun z => z ^ m)).sum -
        ((complexPolynomial p).roots.map (fun z => z⁻¹ ^ m)).sum‖ ≤
      4 * (m : ℝ) * Real.exp ((m : ℝ) * Real.log (integerMahlerMeasure p)) *
        Real.log (integerMahlerMeasure p) := by
  have hc : ((complexPolynomial p).roots.map (fun z => z⁻¹ ^ m)).sum =
      ((complexPolynomial p).roots.map
        (fun z => (starRingEnd ℂ) (z⁻¹ ^ m))).sum := by
    have he := (starRingEnd ℂ).toAddMonoidHom.map_multiset_sum
      ((complexPolynomial p).roots.map (fun z => z⁻¹ ^ m))
    rw [hb] at he
    rw [hb]
    simpa using he
  rw [hc, ← Multiset.sum_map_sub]
  calc
    _ ≤ (((complexPolynomial p).roots.map
        (fun z => z ^ m - (starRingEnd ℂ) (z⁻¹ ^ m))).map norm).sum :=
      norm_multiset_sum_le _
    _ ≤ ((complexPolynomial p).roots.map (fun z =>
        2 * (m : ℝ) * Real.exp ((m : ℝ) * Real.log (integerMahlerMeasure p)) *
          |Real.log ‖z‖|)).sum := by
      rw [Multiset.map_map]
      apply Multiset.sum_map_le_sum_map
      intro z hz
      exact norm_pow_sub_conj_inv_pow_le (root_ne_zero_of_unitConstant hu hz) m
        (abs_log_norm_root_le hp hu hz)
    _ = _ := by
      rw [Multiset.sum_map_mul_left, sum_abs_log_norm_roots hp hu]
      ring

/-- Distinct integer power sums give the numerical witness used by the
elementary Mahler hypothesis. -/
theorem mahler_power_sum_witness_bound {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) (m : ℕ) (a b : ℤ) (hab : a ≠ b)
    (ha : ((complexPolynomial p).roots.map (fun z => z ^ m)).sum = (a : ℂ))
    (hb : ((complexPolynomial p).roots.map (fun z => z⁻¹ ^ m)).sum = (b : ℂ)) :
    1 ≤ 4 * (m : ℝ) *
      Real.exp ((m : ℝ) * Real.log (integerMahlerMeasure p)) *
        Real.log (integerMahlerMeasure p) := by
  have hab0 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have habs : (1 : ℤ) ≤ |a - b| := by
    have := abs_pos.mpr hab0
    omega
  have hlo : (1 : ℝ) ≤ ‖(a : ℂ) - (b : ℂ)‖ := by
    rw [← Int.cast_sub, Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast habs
  have hhi := norm_power_sum_sub_inverse_le hp hu m b hb
  rw [ha, hb] at hhi
  exact hlo.trans hhi

/-- The Newton witness and the radial power estimate discharge the elementary
Mahler hypothesis without any additional mathematical assumption. -/
theorem elementaryMahlerHypothesis_holds : ElementaryMahlerHypothesis := by
  constructor
  intro p hp hu hne
  obtain ⟨m, hm, hmd, a, b, hab, ha, hb⟩ :=
    nonreciprocal_power_sum_witness hp hu hne
  exact ⟨m, hm, hmd, mahler_power_sum_witness_bound hp hu m a b hab ha hb⟩

/-- The elementary Mahler lower bound for every monic, nonreciprocal integer
polynomial with constant coefficient `±1`. -/
theorem elementary_mahler_unconditional {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) (hne : p ≠ normalizedReciprocal p) :
    1 / (12 * (p.natDegree : ℝ)) ≤ Real.log (integerMahlerMeasure p) :=
  elementary_mahler elementaryMahlerHypothesis_holds hp hu hne

end

end Power2ModuleSVP
