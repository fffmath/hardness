import Rank2ModuleSVP.PrimeCyclotomic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! Quadratic Gauss sums in the integral coefficient quotient. -/
namespace Rank2ModuleSVP
open scoped BigOperators
noncomputable section
variable {q : ℕ} [Fact q.Prime]

abbrev quadraticCoeffs : Coeff ℤ q := quadraticChar (ZMod q)
def theta : IntegerRing q := classOf quadraticCoeffs

private theorem quadratic_neg_one (hq : q % 4 = 3) : quadraticChar (ZMod q) (-1) = -1 := by
  apply quadraticChar_neg_one_iff_not_isSquare.mpr
  rw [FiniteField.isSquare_neg_one_iff, ZMod.card]
  simp [hq]

private theorem quadratic_correlation (hq : q % 4 = 3) (d : ZMod q) :
    (∑ b : ZMod q, quadraticCoeffs b * quadraticCoeffs (b-d)) =
      if d = 0 then (q : ℤ)-1 else -1 := by
  classical
  let χ := quadraticChar (ZMod q)
  have hchar : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    intro he
    subst q
    norm_num at hq
  by_cases hd : d = 0
  · subst d
    simp only [sub_zero]
    have hh (b : ZMod q) : quadraticCoeffs b * quadraticCoeffs b = 1 - if b = 0 then 1 else 0 := by
      by_cases hb : b = 0
      · simp [hb, quadraticCoeffs]
      · simpa only [pow_two, ite_eq_right hb, sub_zero] using quadraticChar_sq_one hb
    simp_rw [hh]
    simp [Finset.sum_sub_distrib, ZMod.card, Finset.card_univ]
  · rw [ite_eq_right hd]
    have hJ : (∑ b : ZMod q, χ b * χ (1-b)) = -χ (-1) := by
      have := jacobiSum_nontrivial_inv (quadraticChar_ne_one hchar)
      rw [(quadraticChar_isQuadratic (ZMod q)).inv] at this
      exact this
    have he : (∑ b : ZMod q, χ b * χ (b-d)) =
        ∑ b : ZMod q, χ (d*b) * χ (d*b-d) :=
      (Equiv.sum_comp (Equiv.mulLeft₀ d hd) (fun b => χ b * χ (b-d))).symm
    change (∑ b : ZMod q, χ b * χ (b-d)) = -1
    rw [he]
    have hh (b : ZMod q) : χ (d*b) * χ (d*b-d) = χ b * χ (b-1) := by
      calc
        χ (d*b) * χ (d*b-d) = χ d ^ 2 * (χ b * χ (b-1)) := by
          rw [show d*b-d = d*(b-1) by ring, map_mul, map_mul]
          ring
        _ = χ b * χ (b-1) := by rw [quadraticChar_sq_one hd, one_mul]
    simp_rw [hh, show ∀ b : ZMod q, b-1 = (-1)*(1-b) by intro; ring, map_mul]
    simp_rw [show ∀ b : ZMod q, χ b * (χ (-1) * χ (1-b)) =
      χ (-1) * (χ b * χ (1-b)) by intro; ring]
    rw [← Finset.mul_sum, hJ]
    have := quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero : (1 : ZMod q) ≠ 0))
    change χ (-1) ^ 2 = 1 at this
    nlinarith

/-- Paper `gauss-sum`: conjugation negates the quadratic Gauss sum. -/
theorem conjugate_theta (hq : q % 4 = 3) : conjugate (theta (q := q)) = -theta := by
  rw [theta, conjugate_classOf, ← classOf_neg]
  congr 1
  funext a
  change quadraticChar (ZMod q) (-a) = -quadraticChar (ZMod q) a
  rw [neg_eq_neg_one_mul, map_mul, quadratic_neg_one hq, neg_one_mul]

/-- The product of the Gauss sum with its conjugate is q. -/
theorem theta_mul_conjugate (hq : q % 4 = 3) :
    theta (q := q) * conjugate theta = (q : IntegerRing q) := by
  rw [theta, conjugate_classOf, classOf_mul]
  have hqclass : classOf (fun a : ZMod q => if a = 0 then (q : ℤ) else 0) =
      (q : IntegerRing q) := by simpa only [Int.cast_natCast] using classOf_single_zero (q : ℤ)
  rw [← hqclass]
  apply (classOf_eq_iff _ _).mpr
  refine ⟨-1, fun a => ?_⟩
  have he : (∑ b : ZMod q, quadraticCoeffs b * conjugateCoeff quadraticCoeffs (a-b)) =
      ∑ b : ZMod q, quadraticCoeffs b * quadraticCoeffs (b-a) := by
    congr 1
    funext b
    simp only [conjugateCoeff, neg_sub]
  rw [he, quadratic_correlation hq]
  split_ifs <;> ring

/-- The square of the quadratic Gauss sum is -q. -/
theorem theta_sq (hq : q % 4 = 3) : theta (q := q)^2 = -(q : IntegerRing q) := by
  have h := theta_mul_conjugate hq
  rw [conjugate_theta hq] at h
  calc
    theta ^ 2 = -(theta * -theta) := by ring
    _ = -(q : IntegerRing q) := congrArg Neg.neg h

end
end Rank2ModuleSVP
