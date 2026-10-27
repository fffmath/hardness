import Power2ModuleSVPSubsetSum.Rigidity.Filter
import Power2ModuleSVPSubsetSum.Algebra.Adjoint

/-! # Skew-adjointness of the rigidity filter

The base-five filter contributes zero to the coefficient inner product.

Paper: `paper/power2svp-subsetsum.pdf`, Section 3, Lemma 3.1.
-/
namespace Power2ModuleSVPSubsetSum.Rigidity
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- Each skew shift is negated by substitution of the inverse variable. -/
theorem star_S {m d : ℕ} (hd : 0 < d) (hdm : d < m) : star (S m d) = -S m d := by
  ext i
  simp only [star, S, Pi.add_apply, Pi.neg_apply, atom]
  split_ifs <;> omega

/-- The full base-five filter is skew-adjoint. -/
theorem star_K (m : ℕ) : star (K m) = -K m := by
  simp only [K, star_sum, star_smul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [star_S (by omega) (by have := d.isLt; omega)]
  simp

/-- The filter contributes no energy, also after applying `D`. -/
theorem D_K_inner_zero {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m)) :
    coeffInner (mul (D m) b) (mul (D m) (mul (K m) b)) = 0 := by
  have he : mul (D m) (mul (K m) b) = mul (K m) (mul (D m) b) := by
    rw [← coeff_mul_assoc (by omega), IdealCVP.Cyclotomic.mul_comm (D m) (K m),
      coeff_mul_assoc (by omega)]
  rw [he]
  exact coeffInner_mul_self_eq_zero (by omega) (star_K m) _

/-- The adjoint parity filter is `1 - X^m`. -/
theorem star_D (m : ℕ) : star (D m) = atom (2 * m) 0 - atom (2 * m) m := by
  ext i
  simp only [star, D, atom, Pi.add_apply, Pi.sub_apply]
  split_ifs <;> omega

/-- Multiplying the parity filter by its adjoint gives the scalar two. -/
theorem star_D_mul_D {m : ℕ} (hm : 0 < m) :
    mul (star (D m)) (D m) = (2 : ℤ) • coeffOne (by omega) := by
  rw [IdealCVP.Cyclotomic.mul_comm]
  ext i
  by_cases hi : i.val < m
  · have he : (⟨i.val, by omega⟩ : Fin (2 * m)) = i := Fin.ext rfl
    have h := D_mul_low hm (star (D m)) ⟨i.val, hi⟩
    dsimp only at h
    rw [he] at h
    rw [h, star_D]
    by_cases hz : i.val = 0
    · simp [atom, hz, coeffOne, monomial, Fin.ext_iff,
        show (0 : ℕ) ≠ m by omega, show m ≠ 0 by omega]
    · simp [atom, hz, coeffOne, monomial, Fin.ext_iff,
        show i.val ≠ m by omega]
  · have he : (⟨i.val - m + m, by omega⟩ : Fin (2 * m)) = i := by
      apply Fin.ext
      dsimp
      omega
    have h := D_mul_high hm (star (D m)) ⟨i.val - m, by omega⟩
    dsimp only at h
    rw [he] at h
    rw [h, star_D]
    by_cases hz : i.val = m
    · simp [atom, hz, coeffOne, monomial, Fin.ext_iff,
        show (0 : ℕ) ≠ m by omega, show m ≠ 0 by omega]
    · simp [atom, hz, coeffOne, monomial, Fin.ext_iff,
        show i.val ≠ 0 by omega, show i.val - m ≠ 0 by omega,
        show i.val - m ≠ m by omega]

end Power2ModuleSVPSubsetSum.Rigidity
