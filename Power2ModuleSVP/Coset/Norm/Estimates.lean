module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

/-!
# Estimates

Elementary tools for the norm argument.  The mathematical specifications in this
file refer to `lem:elementary-mahler`, `lem:reciprocal-resultant`, and
`lem:elementary-separation` of the private source.  All explanatory text here is
independently written.

Paper: `paper/power2svp.pdf`, Section 3.2 (Lemmas 2–4, algebraic norm separation).
-/

@[expose] public section

namespace Power2ModuleSVP

open Polynomial
open scoped BigOperators

noncomputable section

/-- Integer coefficients viewed as complex coefficients. -/
def complexPolynomial (p : ℤ[X]) : ℂ[X] := p.map (Int.castRingHom ℂ)

/-- The constant coefficient is a unit, expressed without choosing its sign. -/
def HasUnitConstant (p : ℤ[X]) : Prop := p.coeff 0 = 1 ∨ p.coeff 0 = -1

/-- On unit-constant polynomials this is the monic, normalized reciprocal. -/
def normalizedReciprocal (p : ℤ[X]) : ℤ[X] := C (p.coeff 0) * p.reverse

/-- The root formulation produced by the prime-exponent construction.
The unnormalized reciprocal has exactly the same roots as the normalized one
when the constant coefficient is a unit. -/
def NoCommonReciprocalRoot (p : ℤ[X]) : Prop :=
  ∀ z : ℂ, (complexPolynomial p).eval z = 0 →
    (complexPolynomial p.reverse).eval z ≠ 0

/-- Coefficient height bounded by the natural number `H`. -/
def CoefficientBound (p : ℤ[X]) (H : ℕ) : Prop :=
  ∀ n : ℕ, |p.coeff n| ≤ (H : ℤ)

/-- The binomial whose principal ideal occurs in the auxiliary quotient. -/
def separationBinomial (D : ℕ) : ℤ[X] := 1 + X ^ D

/-- An integer-polynomial lift of membership in `(1+X^D)` modulo `w`. -/
def SeparationCongruence (w e : ℤ[X]) (D : ℕ) : Prop :=
  ∃ q u : ℤ[X], e = separationBinomial D * q + w * u

/-- Mahler measure, using Mathlib's definition rather than an extra formal
parameter for a root product. -/
def integerMahlerMeasure (p : ℤ[X]) : ℝ := (complexPolynomial p).mahlerMeasure

/-- Product of evaluations at all complex roots, with their multiplicities. -/
def rootEvaluationProduct (p a : ℤ[X]) : ℂ :=
  ((complexPolynomial p).roots.map (complexPolynomial a).eval).prod

/-- Product of radial gaps, with the multiplicities of the complex roots. -/
def radialGapProduct (p : ℤ[X]) : ℝ :=
  ((complexPolynomial p).roots.map (fun z => |‖z‖ - ‖z‖⁻¹|)).prod

theorem complexPolynomial_monic {p : ℤ[X]} (hp : p.Monic) :
    (complexPolynomial p).Monic := hp.map _

theorem complexPolynomial_natDegree {p : ℤ[X]} (hp : p.Monic) :
    (complexPolynomial p).natDegree = p.natDegree := hp.natDegree_map _

theorem one_le_integerMahlerMeasure {p : ℤ[X]} (hp : p.Monic) :
    1 ≤ integerMahlerMeasure p := by
  apply one_le_mahlerMeasure_of_one_le_norm_leadingCoeff
  simp [(complexPolynomial_monic hp).leadingCoeff]

theorem integerMahlerMeasure_pos {p : ℤ[X]} (hp : p.Monic) :
    0 < integerMahlerMeasure p := lt_of_lt_of_le zero_lt_one
      (one_le_integerMahlerMeasure hp)

theorem log_integerMahlerMeasure_nonneg {p : ℤ[X]} (hp : p.Monic) :
    0 ≤ Real.log (integerMahlerMeasure p) :=
  Real.log_nonneg (one_le_integerMahlerMeasure hp)

theorem noCommonReciprocalRoot_of_dvd {p w : ℤ[X]}
    (hw : NoCommonReciprocalRoot w) (hpw : p ∣ w) :
    NoCommonReciprocalRoot p := by
  obtain ⟨v, rfl⟩ := hpw
  intro z hz hzrev
  unfold complexPolynomial at hz hzrev
  apply hw z
  · simp [complexPolynomial, hz]
  · simp [reverse_mul_of_domain, complexPolynomial, hzrev]

/-- Positive-degree monic polynomials have complex roots; hence the root
disjointness promise implies failure of normalized reciprocity. -/
theorem ne_normalizedReciprocal {p : ℤ[X]} (hp : p.Monic)
    (hd : 0 < p.natDegree) (hu : HasUnitConstant p)
    (hroot : NoCommonReciprocalRoot p) : p ≠ normalizedReciprocal p := by
  intro heq
  have hd' : 0 < (complexPolynomial p).degree := by
    rw [← natDegree_pos_iff_degree_pos, complexPolynomial_natDegree hp]
    exact hd
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (complexPolynomial p) (ne_of_gt hd')
  have hz' : (complexPolynomial p).eval z = 0 := hz
  have hc : (p.coeff 0 : ℂ) ≠ 0 := by rcases hu with hu | hu <;> simp [hu]
  have he := congrArg (fun a : ℤ[X] => (complexPolynomial a).eval z) heq
  rw [hz'] at he
  have : (complexPolynomial p.reverse).eval z = 0 := by
    apply (mul_eq_zero.mp _).resolve_left hc
    simpa [normalizedReciprocal, complexPolynomial] using he.symm
  exact hroot z hz' this

theorem root_ne_zero_of_unitConstant {p : ℤ[X]} (hu : HasUnitConstant p)
    {z : ℂ} (hz : z ∈ (complexPolynomial p).roots) : z ≠ 0 := by
  intro hz0
  subst z
  have h := (mem_roots (by
    intro hp0
    have : (p.coeff 0 : ℂ) = 0 := by
      simpa [complexPolynomial] using congrArg (fun a : ℂ[X] => a.coeff 0) hp0
    rcases hu with hu | hu <;> simp [hu] at this)).mp hz
  have : (p.coeff 0 : ℂ) = 0 := by
    simpa [IsRoot, complexPolynomial, ← coeff_zero_eq_eval_zero] using h
  rcases hu with hu | hu <;> simp [hu] at this

theorem complexPolynomial_eval_conj (p : ℤ[X]) (z : ℂ) :
    (complexPolynomial p).eval ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((complexPolynomial p).eval z) := by
  have h := Polynomial.aeval_conj (K := ℂ) (p.map (Int.castRingHom ℝ)) z
  have he : (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by
    ext n
    simp
  simpa only [complexPolynomial, eval_map, aeval_def, eval₂_map, he] using h

/-- The root-disjointness formulation also excludes all unit-circle roots. -/
theorem norm_root_ne_one {p : ℤ[X]} (hp : p.Monic) (hu : HasUnitConstant p)
    (hdis : NoCommonReciprocalRoot p) {z : ℂ}
    (hz : z ∈ (complexPolynomial p).roots) : ‖z‖ ≠ 1 := by
  intro hnorm
  have hz0 : z ≠ 0 := root_ne_zero_of_unitConstant hu hz
  have hpz := (mem_roots (complexPolynomial_monic hp).ne_zero).mp hz
  have hinv : (complexPolynomial p).eval z⁻¹ = 0 := by
    rw [Complex.inv_eq_conj hnorm, complexPolynomial_eval_conj,
      show (complexPolynomial p).eval z = 0 from hpz, map_zero]
  let _ : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
  have hr := (eval₂_reverse_eq_zero_iff (Int.castRingHom ℂ) z⁻¹ p).mpr
    (show p.eval₂ (Int.castRingHom ℂ) z⁻¹ = 0 by
      simpa only [complexPolynomial, eval_map] using hinv)
  exact hdis z hpz (by simpa only [complexPolynomial, eval_map, invOf_eq_inv,
    inv_inv] using hr)

theorem separationBinomial_eval_ne_zero {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) (hdis : NoCommonReciprocalRoot p)
    {z : ℂ} (hz : z ∈ (complexPolynomial p).roots) {D : ℕ} (hD : 1 ≤ D) :
    (complexPolynomial (separationBinomial D)).eval z ≠ 0 := by
  intro hzero
  have hpow : z ^ D = -1 := by
    have he : 1 + z ^ D = 0 := by simpa [complexPolynomial, separationBinomial] using hzero
    linear_combination he
  have hn : ‖z‖ ^ D = 1 := by
    simpa only [norm_pow, norm_neg, norm_one] using congrArg norm hpow
  have hr : ‖z‖ = 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : ‖z‖ ^ D < 1 := pow_lt_one₀ (norm_nonneg _) h (by omega)
      linarith
    · have : 1 < ‖z‖ ^ D := one_lt_pow₀ h (by omega)
      linarith
  exact norm_root_ne_one hp hu hdis hz hr

/-- The product of the root moduli is one, including repeated roots. -/
theorem prod_norm_roots_eq_one {p : ℤ[X]} (hp : p.Monic) (hu : HasUnitConstant p) :
    ((complexPolynomial p).roots.map norm).prod = 1 := by
  have h := congrArg norm ((IsAlgClosed.splits (complexPolynomial p)).eval_eq_prod_roots 0)
  rw [(complexPolynomial_monic hp).leadingCoeff, one_mul,
    Multiset.norm_prod_map] at h
  simp only [zero_sub, norm_neg] at h
  rw [← h]
  rcases hu with hu | hu <;>
    simp [complexPolynomial, ← coeff_zero_eq_eval_zero, hu]

/-- A one-root estimate underlying the reciprocal-resultant argument.
It is written after clearing the positive denominator. -/
theorem radial_gap_mul_mahler_factor_le {z : ℂ} (hz : z ≠ 0)
    {D : ℕ} (hD : 1 ≤ D) :
    (max 1 ‖z‖) ^ D * |‖z‖ - ‖z‖⁻¹| ≤
      2 * max ‖z‖ ‖z‖⁻¹ * ‖1 + z ^ D‖ := by
  let r := ‖z‖
  have hr : 0 < r := norm_pos_iff.mpr hz
  have hi : 0 < r⁻¹ := inv_pos.mpr hr
  have hri : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  have hn : |1 - r ^ D| ≤ ‖1 + z ^ D‖ := by
    simpa [r] using abs_norm_sub_norm_le (1 : ℂ) (-z ^ D)
  change (max 1 r) ^ D * |r - r⁻¹| ≤ 2 * max r r⁻¹ * ‖1 + z ^ D‖
  rcases le_total 1 r with hr1 | hr1
  · have hi1 : r⁻¹ ≤ 1 := (inv_le_one₀ hr).mpr hr1
    have hpow : r ≤ r ^ D := by simpa using pow_le_pow_right₀ hr1 hD
    have habs : |r - r⁻¹| = r - r⁻¹ := abs_of_nonneg (by linarith)
    have hnorm : r ^ D - 1 ≤ ‖1 + z ^ D‖ :=
      (neg_le_abs (1 - r ^ D)).trans hn |>.trans' (by linarith)
    rw [max_eq_right hr1, max_eq_left (by linarith), habs]
    have hprod := mul_le_mul_of_nonneg_right hpow (show 0 ≤ r + r⁻¹ by positivity)
    have hprod' := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * r by positivity)
    nlinarith [sq_nonneg (r - 1)]
  · have hi1 : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
    have hpow : r ^ D ≤ r := by simpa using pow_le_pow_of_le_one hr.le hr1 hD
    have habs : |r - r⁻¹| = r⁻¹ - r := by rw [abs_of_nonpos (by linarith)]; ring
    have hnorm : 1 - r ^ D ≤ ‖1 + z ^ D‖ := (le_abs_self _).trans hn
    rw [max_eq_left hr1, one_pow, one_mul, max_eq_right (by linarith), habs]
    have hprod := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * r⁻¹ by positivity)
    have hprod' := mul_le_mul_of_nonneg_left hpow hi.le
    have hsym : 2 ≤ r + r⁻¹ := by
      have hh := mul_nonneg (sub_nonneg.mpr hi1) (sub_nonneg.mpr hr1)
      nlinarith
    nlinarith

/-- Unit constant coefficient identifies the product of the two-sided
radial maxima with the square of the Mahler measure. -/
theorem prod_max_norm_inv_eq_mahler_sq {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) :
    ((complexPolynomial p).roots.map (fun z => max ‖z‖ ‖z‖⁻¹)).prod =
      integerMahlerMeasure p ^ 2 := by
  have hpoint (z : ℂ) (hz : z ∈ (complexPolynomial p).roots) :
      max ‖z‖ ‖z‖⁻¹ * ‖z‖ = (max 1 ‖z‖) ^ 2 := by
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr (root_ne_zero_of_unitConstant hu hz)
    rcases le_total 1 ‖z‖ with h | h
    · have hi : ‖z‖⁻¹ ≤ 1 := (inv_le_one₀ hr).mpr h
      rw [max_eq_left (by linarith), max_eq_right h, pow_two]
    · have hi : 1 ≤ ‖z‖⁻¹ := (one_le_inv₀ hr).mpr h
      rw [max_eq_right (by linarith), max_eq_left h, inv_mul_cancel₀ hr.ne']
      norm_num
  have hprod := congrArg Multiset.prod (Multiset.map_congr rfl hpoint)
  rw [Multiset.prod_map_mul, prod_norm_roots_eq_one hp hu, mul_one,
    Multiset.prod_map_pow] at hprod
  rw [integerMahlerMeasure, mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    (complexPolynomial_monic hp).leadingCoeff, norm_one, one_mul]
  exact hprod

/-- Multiplication of the one-root estimates.  The factor `M(p)^2` comes
from the unit constant term, rather than an individual root bound. -/
theorem binomial_radial_product_bound {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) {D : ℕ} (hD : 1 ≤ D) :
    integerMahlerMeasure p ^ D * radialGapProduct p ≤
      (2 : ℝ) ^ p.natDegree * integerMahlerMeasure p ^ 2 *
        ‖rootEvaluationProduct p (separationBinomial D)‖ := by
  have h := Multiset.prod_map_le_prod_map₀
    (fun z : ℂ => (max 1 ‖z‖) ^ D * |‖z‖ - ‖z‖⁻¹|)
    (fun z : ℂ => 2 * max ‖z‖ ‖z‖⁻¹ * ‖1 + z ^ D‖)
    (s := (complexPolynomial p).roots) (by intros; positivity)
    (fun z hz => radial_gap_mul_mahler_factor_le
      (root_ne_zero_of_unitConstant hu hz) hD)
  simp only [Multiset.prod_map_mul, Multiset.prod_map_pow,
    Multiset.map_const', Multiset.prod_replicate] at h
  have hcard : (complexPolynomial p).roots.card = p.natDegree :=
    (IsAlgClosed.splits _).natDegree_eq_card_roots.symm.trans (complexPolynomial_natDegree hp)
  rw [hcard, prod_max_norm_inv_eq_mahler_sq hp hu] at h
  have hmahler : ((complexPolynomial p).roots.map (fun z => max 1 ‖z‖)).prod =
      integerMahlerMeasure p := by
    rw [integerMahlerMeasure, mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
      (complexPolynomial_monic hp).leadingCoeff, norm_one, one_mul]
  rw [hmahler] at h
  simpa [radialGapProduct, rootEvaluationProduct, separationBinomial,
    complexPolynomial, Multiset.norm_prod_map] using h

/-- Monicity identifies the root product with the image of an integer
resultant.  This avoids selecting a number field or a particular root. -/
theorem rootEvaluationProduct_eq_resultant {p : ℤ[X]} (hp : p.Monic)
    (a : ℤ[X]) :
    rootEvaluationProduct p a = (Polynomial.resultant p a : ℤ) := by
  have hdeg : (complexPolynomial a).natDegree = a.natDegree :=
    natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int a
  have h := Polynomial.resultant_eq_prod_eval (complexPolynomial p)
    (complexPolynomial a) a.natDegree (le_of_eq hdeg)
    (IsAlgClosed.splits _)
  rw [(complexPolynomial_monic hp).leadingCoeff, one_pow, one_mul,
    complexPolynomial_natDegree hp] at h
  rw [rootEvaluationProduct, ← h]
  exact resultant_map_map _ _ _ _ _

/-- The reciprocal-resultant estimate follows from its radial-gap input.
All root geometry, powers, and constants in this implication are proved. -/
theorem reciprocal_resultant_lower_bound_of_radial_gap_bound
    {p : ℤ[X]} (hp : p.Monic) (hu : HasUnitConstant p)
    (hgap : 1 ≤ (2 : ℝ) ^ (p.natDegree * (p.natDegree - 1)) *
      integerMahlerMeasure p ^ (2 * (p.natDegree - 1)) * radialGapProduct p)
    {D : ℕ} (hD : 1 ≤ D) :
    (2 : ℝ) ^ (-((p.natDegree : ℝ) ^ 2)) *
      integerMahlerMeasure p ^ ((D : ℝ) - 2 * p.natDegree) ≤
        ‖rootEvaluationProduct p (separationBinomial D)‖ := by
  by_cases hd : p.natDegree = 0
  · have hp1 : p = 1 := eq_one_of_monic_natDegree_zero hp hd
    subst p
    simp [integerMahlerMeasure, rootEvaluationProduct, complexPolynomial]
  have hd1 : 1 ≤ p.natDegree := by omega
  let d := p.natDegree
  let M := integerMahlerMeasure p
  let N := ‖rootEvaluationProduct p (separationBinomial D)‖
  have hM : 0 < M := integerMahlerMeasure_pos hp
  have hC : 0 < (2 : ℝ) ^ (d * (d - 1)) * M ^ (2 * (d - 1)) := by positivity
  have hgeom := binomial_radial_product_bound hp hu hD
  change M ^ D * radialGapProduct p ≤ (2 : ℝ) ^ d * M ^ 2 * N at hgeom
  have h1 := mul_le_mul_of_nonneg_left hgap (show 0 ≤ M ^ D by positivity)
  have h2 := mul_le_mul_of_nonneg_left hgeom hC.le
  have hexp2 : d * (d - 1) + d = d ^ 2 := by
    have hs : d - 1 + 1 = d := Nat.sub_add_cancel hd1
    nlinarith
  have hexpM : 2 * (d - 1) + 2 = 2 * d := by omega
  have hbound : M ^ D ≤ (2 : ℝ) ^ (d ^ 2) * M ^ (2 * d) * N := by
    calc
      M ^ D ≤ ((2 : ℝ) ^ (d * (d - 1)) * M ^ (2 * (d - 1))) *
          (M ^ D * radialGapProduct p) := by
        change M ^ D * 1 ≤ _ at h1
        nlinarith only [h1]
      _ ≤ ((2 : ℝ) ^ (d * (d - 1)) * M ^ (2 * (d - 1))) *
          ((2 : ℝ) ^ d * M ^ 2 * N) := h2
      _ = _ := by
        calc
          _ = ((2 : ℝ) ^ (d * (d - 1)) * 2 ^ d) *
              (M ^ (2 * (d - 1)) * M ^ 2) * N := by ring
          _ = _ := by rw [← pow_add, ← pow_add, hexp2, hexpM]
  have htwo : (2 : ℝ) ^ (-((d : ℝ) ^ 2)) = ((2 : ℝ) ^ (d ^ 2))⁻¹ := by
    rw [Real.rpow_neg (by norm_num), ← Nat.cast_pow, Real.rpow_natCast]
  have hmexp : M ^ ((D : ℝ) - 2 * d) = M ^ D / M ^ (2 * d) := by
    rw [show (2 : ℝ) * d = ((2 * d : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_sub hM, Real.rpow_natCast, Real.rpow_natCast]
  change (2 : ℝ) ^ (-((d : ℝ) ^ 2)) * M ^ ((D : ℝ) - 2 * d) ≤ N
  rw [htwo, hmexp]
  have hden : 0 < (2 : ℝ) ^ (d ^ 2) * M ^ (2 * d) := by positivity
  have hquot : M ^ D / ((2 : ℝ) ^ (d ^ 2) * M ^ (2 * d)) ≤ N :=
    (div_le_iff₀ hden).mpr (by simpa [mul_comm] using hbound)
  calc
    _ = M ^ D / ((2 : ℝ) ^ (d ^ 2) * M ^ (2 * d)) := by ring
    _ ≤ N := hquot

theorem rootEvaluationProduct_mul (p a b : ℤ[X]) :
    rootEvaluationProduct p (a * b) =
      rootEvaluationProduct p a * rootEvaluationProduct p b := by
  simp [rootEvaluationProduct, complexPolynomial, Polynomial.map_mul,
    Multiset.prod_map_mul]

/-- A nonzero product is a nonzero integer, so its absolute value is at
least one.  This is the integrality step in the norm comparison. -/
theorem one_le_norm_rootEvaluationProduct {p : ℤ[X]} (hp : p.Monic)
    (a : ℤ[X]) (ha : rootEvaluationProduct p a ≠ 0) :
    1 ≤ ‖rootEvaluationProduct p a‖ := by
  rw [rootEvaluationProduct_eq_resultant hp] at ha ⊢
  have hz : Polynomial.resultant p a ≠ 0 := by exact_mod_cast ha
  rw [Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hz

/-- Rootwise congruences multiply to the same identity on root products. -/
theorem rootEvaluationProduct_eq_mul {p a b c : ℤ[X]}
    (h : ∀ z ∈ (complexPolynomial p).roots,
      (complexPolynomial a).eval z =
        (complexPolynomial b).eval z * (complexPolynomial c).eval z) :
    rootEvaluationProduct p a = rootEvaluationProduct p b *
      rootEvaluationProduct p c := by
  rw [← rootEvaluationProduct_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro z hz
  simpa [complexPolynomial] using h z hz

/-- Leibniz's rule at a root where the lower divided derivatives of the
right factor vanish. -/
theorem hasseDeriv_mul_eval_of_vanishing_right (a b : ℂ[X]) (z : ℂ) (j : ℕ)
    (hb : ∀ k < j, (hasseDeriv k b).eval z = 0) :
    (hasseDeriv j (a * b)).eval z = a.eval z * (hasseDeriv j b).eval z := by
  rw [hasseDeriv_mul]
  change (evalRingHom z) (∑ ij ∈ Finset.antidiagonal j,
    hasseDeriv ij.1 a * hasseDeriv ij.2 b) = _
  rw [map_sum, Finset.sum_eq_single (0, j)]
  · simp
  · intro ij hij hne
    have hsum := Finset.mem_antidiagonal.mp hij
    have hk : ij.2 < j := by
      by_contra hk
      have hi : ij.1 = 0 := by omega
      have hi' : ij.2 = j := by omega
      exact hne (Prod.ext hi hi')
    simp [hb _ hk]
  · simp

theorem hasseDeriv_mul_eval_eq_zero_of_vanishing_left (a b : ℂ[X])
    (z : ℂ) (j : ℕ) (ha : ∀ k ≤ j, (hasseDeriv k a).eval z = 0) :
    (hasseDeriv j (a * b)).eval z = 0 := by
  rw [hasseDeriv_mul]
  change (evalRingHom z) (∑ ij ∈ Finset.antidiagonal j,
    hasseDeriv ij.1 a * hasseDeriv ij.2 b) = _
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro ij hij
  have hk : ij.1 ≤ j := by have := Finset.mem_antidiagonal.mp hij; omega
  simp [ha _ hk]

/-- Cancellation through the first nonzero divided derivative.  The
multiplier's lower derivatives are deduced by induction, rather than
assumed as a separate multiplicity statement. -/
theorem first_hasseDeriv_lift {e t q w u : ℂ[X]}
    (hlift : e = t * q + w * u) (z : ℂ) (j : ℕ)
    (ht : t.eval z ≠ 0) (he : (hasseDeriv j e).eval z ≠ 0)
    (helow : ∀ k < j, (hasseDeriv k e).eval z = 0)
    (hw : ∀ k ≤ j, (hasseDeriv k w).eval z = 0) :
    (hasseDeriv j e).eval z = t.eval z * (hasseDeriv j q).eval z ∧
      (hasseDeriv j q).eval z ≠ 0 := by
  have hq : ∀ k < j, (hasseDeriv k q).eval z = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hprod := hasseDeriv_mul_eval_of_vanishing_right t q z k
        (fun i hi => ih i hi (by omega))
      have hwprod := hasseDeriv_mul_eval_eq_zero_of_vanishing_left w u z k
        (fun i hi => hw i (by omega))
      have heq : (hasseDeriv k e).eval z = t.eval z * (hasseDeriv k q).eval z := by
        rw [hlift, map_add, eval_add, hprod, hwprod, add_zero]
      rw [helow k hk] at heq
      exact (mul_eq_zero.mp heq.symm).resolve_left ht
  have hprod := hasseDeriv_mul_eval_of_vanishing_right t q z j hq
  have hwprod := hasseDeriv_mul_eval_eq_zero_of_vanishing_left w u z j hw
  have heq : (hasseDeriv j e).eval z = t.eval z * (hasseDeriv j q).eval z := by
    rw [hlift, map_add, eval_add, hprod, hwprod, add_zero]
  refine ⟨heq, ?_⟩
  intro hzero
  exact he (by rw [heq, hzero, mul_zero])

/-- Divided derivatives preserve the strict degree cutoff. -/
theorem hasseDeriv_degree_lt {e : ℤ[X]} {L : ℕ}
    (he : e.degree < L) (j : ℕ) : (hasseDeriv j e).degree < L := by
  rw [degree_lt_iff_coeff_zero] at he ⊢
  intro n hn
  rw [hasseDeriv_coeff, he (n + j) (by omega), mul_zero]

/-- Polynomial rather than exponential coefficient growth is enough, since
the derivative order and the factor degree share a degree budget. -/
theorem hasseDeriv_coefficientBound {e : ℤ[X]} {L : ℕ}
    (he : e.degree < L) (hH : CoefficientBound e (L ^ 2)) (j : ℕ) :
    CoefficientBound (hasseDeriv j e) (L ^ (j + 2)) := by
  intro n
  rw [hasseDeriv_coeff]
  by_cases hn : L ≤ n + j
  · rw [(degree_lt_iff_coeff_zero e L).mp he (n + j) hn, mul_zero, abs_zero]
    positivity
  have hc : ((n + j).choose j : ℤ) ≤ (L : ℤ) ^ j := by
    exact_mod_cast (Nat.choose_le_pow (n + j) j).trans
      (Nat.pow_le_pow_left (by omega : n + j ≤ L) j)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (n + j).choose j)]
  calc
    _ ≤ (L : ℤ) ^ j * (L ^ 2 : ℕ) :=
      mul_le_mul hc (hH (n + j)) (abs_nonneg _) (by positivity)
    _ = (L ^ (j + 2) : ℕ) := by push_cast; rw [pow_add]

/-- A height and degree bound control evaluation even outside the unit disk. -/
theorem norm_eval_le_of_coefficientBound {a : ℤ[X]} {L H : ℕ}
    (hL : 0 < L) (ha : a.degree < L) (hH : CoefficientBound a H) (z : ℂ) :
    ‖(complexPolynomial a).eval z‖ ≤
      (L : ℝ) * H * (max 1 ‖z‖) ^ (L - 1) := by
  have hcoeff (n : ℕ) : ‖(a.coeff n : ℂ)‖ ≤ (H : ℝ) := by
    rw [Complex.norm_intCast]
    exact_mod_cast hH n
  by_cases ha0 : a = 0
  · simp only [ha0, complexPolynomial, Polynomial.map_zero, Polynomial.eval_zero, norm_zero]
    positivity
  have hn : a.natDegree < L := (natDegree_lt_iff_degree_lt ha0).mpr ha
  rw [complexPolynomial, eval_map, eval₂_eq_sum_range' _ hn]
  calc
    _ ≤ ∑ n ∈ Finset.range L, ‖(a.coeff n : ℂ) * z ^ n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range L, (H : ℝ) * (max 1 ‖z‖) ^ (L - 1) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_pow]
      apply mul_le_mul (hcoeff n) _ (by positivity) (by positivity)
      calc
        ‖z‖ ^ n ≤ (max 1 ‖z‖) ^ n := by gcongr; exact le_max_right _ _
        _ ≤ (max 1 ‖z‖) ^ (L - 1) := by
          apply pow_le_pow_right₀ (le_max_left _ _)
          have := Finset.mem_range.mp hn
          omega
    _ = _ := by simp [mul_assoc]

/-- A finite-product version of the evaluation bound, retaining repeated
roots.  No squarefreeness assumption is used. -/
theorem norm_rootEvaluationProduct_le {p a : ℤ[X]} {L H : ℕ}
    (hp : p.Monic) (hL : 0 < L) (ha : a.degree < L)
    (hH : CoefficientBound a H) :
    ‖rootEvaluationProduct p a‖ ≤
      ((L : ℝ) * H) ^ p.natDegree * integerMahlerMeasure p ^ (L - 1) := by
  have hb (s : Multiset ℂ) :
      ‖(s.map (complexPolynomial a).eval).prod‖ ≤
        ((L : ℝ) * H) ^ s.card *
          (s.map (fun z => max 1 ‖z‖)).prod ^ (L - 1) := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons z s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, norm_mul]
      calc
        _ ≤ ((L : ℝ) * H * (max 1 ‖z‖) ^ (L - 1)) *
            (((L : ℝ) * H) ^ s.card *
              (s.map (fun z => max 1 ‖z‖)).prod ^ (L - 1)) :=
          mul_le_mul (norm_eval_le_of_coefficientBound hL ha hH z) ih
            (norm_nonneg _) (by positivity)
        _ = _ := by rw [pow_succ, mul_pow]; ring
  have hm : integerMahlerMeasure p =
      ((complexPolynomial p).roots.map (fun z => max 1 ‖z‖)).prod := by
    rw [integerMahlerMeasure, mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
      (complexPolynomial_monic hp).leadingCoeff, norm_one, one_mul]
  rw [hm, ← complexPolynomial_natDegree hp,
    (IsAlgClosed.splits (complexPolynomial p)).natDegree_eq_card_roots]
  exact hb _

/-- The precise degree budget turns the divided-derivative estimate into
the uniform `L^(3L)` bound used by the separation argument. -/
theorem norm_hasseDeriv_rootEvaluationProduct_le {p e : ℤ[X]} {L j : ℕ}
    (hp : p.Monic) (hL : 1 ≤ L) (he : e.degree < L)
    (hH : CoefficientBound e (L ^ 2)) (hbudget : (j + 1) * p.natDegree ≤ L) :
    ‖rootEvaluationProduct p (hasseDeriv j e)‖ ≤
      (L : ℝ) ^ (3 * L) * integerMahlerMeasure p ^ (L - 1) := by
  have hb := norm_rootEvaluationProduct_le hp (by omega : 0 < L)
    (hasseDeriv_degree_lt he j) (hasseDeriv_coefficientBound he hH j)
  have hexp : (j + 3) * p.natDegree ≤ 3 * L := by nlinarith
  have hpow : ((L : ℝ) * (L ^ (j + 2) : ℕ)) ^ p.natDegree ≤
      (L : ℝ) ^ (3 * L) := by
    push_cast
    rw [← pow_succ', ← pow_mul]
    apply pow_le_pow_right₀ (by exact_mod_cast hL)
    exact hexp
  exact hb.trans (mul_le_mul_of_nonneg_right hpow
    (pow_nonneg (integerMahlerMeasure_pos hp).le _))

/-- The real-variable conclusion of the integer power-sum argument.  Its
premise isolates the single power sum that differs from its reciprocal. -/
theorem mahler_log_lower_bound_of_power_sum_witness
    (d : ℕ) (T : ℝ) (hd : 0 < d) (hT : 0 ≤ T)
    (hw : ∃ m : ℕ, 1 ≤ m ∧ m ≤ d ∧
      1 ≤ 4 * (m : ℝ) * Real.exp ((m : ℝ) * T) * T) :
    1 / (12 * (d : ℝ)) ≤ T := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨m, hm, hmd, hw⟩ := hw
  have hm' : (0 : ℝ) ≤ m := by positivity
  have hmd' : (m : ℝ) ≤ d := by exact_mod_cast hmd
  by_cases hlarge : 1 / (d : ℝ) ≤ T
  · exact (one_div_le_one_div_of_le hd' (by linarith)).trans hlarge
  have hsmall : (m : ℝ) * T < 1 := by
    have : (d : ℝ) * T < 1 := (lt_div_iff₀' hd').mp (lt_of_not_ge hlarge)
    exact (mul_le_mul_of_nonneg_right hmd' hT).trans_lt this
  have he : Real.exp ((m : ℝ) * T) ≤ 3 :=
    (Real.exp_le_exp.mpr hsmall.le).trans Real.exp_one_lt_three.le
  have hbound : 1 ≤ 12 * (d : ℝ) * T := by
    calc
      1 ≤ 4 * (m : ℝ) * Real.exp ((m : ℝ) * T) * T := hw
      _ ≤ 4 * (m : ℝ) * 3 * T := by gcongr
      _ ≤ 12 * (d : ℝ) * T := by nlinarith [mul_le_mul_of_nonneg_right hmd' hT]
  exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)

/-- The logarithmic estimate used at the endpoint `L = 64` and above. -/
theorem three_log_le_quarter (x : ℝ) (hx : 64 ≤ x) :
    3 * Real.log x ≤ x / 4 := by
  have hx0 : 0 < x := by linarith
  have ht := Real.log_le_sub_one_of_pos (by positivity : 0 < x / 64)
  rw [Real.log_div (ne_of_gt hx0) (by norm_num)] at ht
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [h64] at ht
  have h2 := Real.log_two_lt_d9
  linarith

/-- The complete numerical contradiction, including the exact constant
`16` and the endpoint `64`.  All differences in this statement are real
differences, so there is no truncated subtraction. -/
theorem separation_logarithmic_gap (L d D : ℕ)
    (hL : 64 ≤ L) (hd : 0 < d) (hdL : d ≤ L) (hD : 16 * L ^ 3 ≤ D) :
    (d : ℝ) ^ 2 * Real.log 2 + 3 * (L : ℝ) * Real.log L <
      ((D : ℝ) - 2 * d - L + 1) / (12 * d) := by
  have hL' : (64 : ℝ) ≤ L := by exact_mod_cast hL
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdL' : (d : ℝ) ≤ L := by exact_mod_cast hdL
  have hD' : 16 * (L : ℝ) ^ 3 ≤ D := by exact_mod_cast hD
  have hlog := three_log_le_quarter (L : ℝ) hL'
  have h2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hs : (d : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 := by nlinarith
  have hu : (d : ℝ) ^ 2 * Real.log 2 + 3 * (L : ℝ) * Real.log L <
      5 / 4 * (L : ℝ) ^ 2 := by
    have hstrict : (d : ℝ) ^ 2 * Real.log 2 < (d : ℝ) ^ 2 := by
      nlinarith [mul_pos (sq_pos_of_pos hd') (sub_pos.mpr h2)]
    have hmul := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ L by positivity)
    nlinarith
  have hl : 4 / 3 * (L : ℝ) ^ 2 - 1 / 4 ≤
      ((D : ℝ) - 2 * d - L + 1) / (12 * d) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hm := mul_nonneg (sub_nonneg.mpr hdL')
      (show 0 ≤ 16 * (L : ℝ) ^ 2 - 1 by nlinarith)
    nlinarith
  have hsq : 5 / 4 * (L : ℝ) ^ 2 < 4 / 3 * (L : ℝ) ^ 2 - 1 / 4 := by
    nlinarith
  exact hu.trans (hsq.trans_le hl)

end

end Power2ModuleSVP
