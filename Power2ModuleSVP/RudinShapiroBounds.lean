module

public import Power2ModuleSVP.RudinShapiroAux
import Mathlib.Tactic

/-! Block identities and the even-part estimates needed by the seed. -/

@[expose] public section
namespace Power2ModuleSVP
open Polynomial
noncomputable section

/-- An isolated high binary digit, separated from the low word by a zero,
copies the first Rudin--Shapiro word without changing its signs. -/
theorem rudinShapiroCoefficient_isolated_bit {k h j : ℕ}
    (hkh : k ≤ h) (hj : j < 2 ^ k) :
    rudinShapiroCoefficient (2 ^ (h + 1) + j) = (rudinShapiroP k).coeff j := by
  have hjh : j < 2 ^ h := hj.trans_le (Nat.pow_le_pow_right (by omega) hkh)
  have hjh' : j < 2 ^ (h + 1) := hjh.trans_le
    (Nat.pow_le_pow_right (by omega) (by omega))
  have hidx : 2 ^ (h + 1) + j < 2 ^ (h + 1 + 1) := by
    rw [pow_succ]
    omega
  rw [rudinShapiroCoefficient_eq hidx]
  have htail := (rudinShapiro_coefficients (h + 1)).2 (2 ^ (h + 1) + j) (by omega)
  rw [rudinShapiroP_succ, coeff_add, coeff_X_pow_mul',
    ite_eq_left (by omega), Nat.add_sub_cancel_left, htail.1, zero_add]
  rw [rudinShapiroQ_succ, coeff_sub, coeff_X_pow_mul',
    ite_eq_right (by omega : ¬ 2 ^ h ≤ j), sub_zero]
  exact rudinShapiroP_stable hkh hj

/-- Both removed blocks in the even sine part really are first words. -/
theorem rudinShapiro_seed_blocks {k j : ℕ} (hj : j < 2 ^ k) :
    rudinShapiroCoefficient (2 ^ (k + 10) + j) = (rudinShapiroP k).coeff j ∧
    rudinShapiroCoefficient (2 * 2 ^ (k + 10) + j) = (rudinShapiroP k).coeff j := by
  constructor
  · simpa only [show k + 9 + 1 = k + 10 by omega] using
      rudinShapiroCoefficient_isolated_bit (h := k + 9) (by omega) hj
  · have he : 2 * 2 ^ (k + 10) = 2 ^ (k + 10 + 1) := (pow_succ' 2 (k + 10)).symm
    rw [he]
    exact rudinShapiroCoefficient_isolated_bit (h := k + 10) (by omega) hj

/-- The cosine contribution before substituting a circle parameter. -/
def rudinShapiroCosinePart (k T : ℕ) (z : ℂ) : ℝ :=
  (z ^ T * rsEval (rudinShapiroP k) z +
    z ^ (2 * T) * rsEval (rudinShapiroQ k) z).re

theorem rudinShapiroCosinePart_bound {k T N : ℕ} {z : ℂ} (hz : ‖z‖ = 1)
    (hN : 2 ^ (k + 2) ≤ N) :
    |rudinShapiroCosinePart k T z| ≤ Real.sqrt N :=
  rudinShapiro_real_part_bound k T (2 * T) hz hN

/-- Stable even sine part after deleting the two copies of the first word.
Its constant coefficient has zero imaginary part automatically. -/
def rudinShapiroEvenSinePart (k T N : ℕ) (z : ℂ) : ℝ :=
  (rudinShapiroPrefix (N + 1) z - z ^ T * rsEval (rudinShapiroP k) z -
    z ^ (2 * T) * rsEval (rudinShapiroP k) z).im

theorem rudinShapiroEvenSinePart_bound {k T N : ℕ} {z : ℂ} (hz : ‖z‖ = 1)
    (hN : 4 ≤ N) (hsmall : 64 * 2 ^ (k + 1) ≤ N) :
    |rudinShapiroEvenSinePart k T N z| < 6 * Real.sqrt N := by
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ) < N := by linarith
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hnp
  have hprefix := rudinShapiroPrefix_bound (m := N + 1) (by omega) hz
  have hp := (rudinShapiro_norm_bounds k hz).1
  have hsmallr : 64 * (2 : ℝ) ^ (k + 1) ≤ N := by exact_mod_cast hsmall
  have hblock : Real.sqrt ((2 : ℝ) ^ (k + 1)) ≤ Real.sqrt N / 8 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hnp.le]
  have hprefixscale : Real.sqrt ((N + 1 : ℕ) : ℝ) ≤ 9 / 8 * Real.sqrt N := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · push_cast
      nlinarith [Real.sq_sqrt hnp.le]
  have hnormT : ‖z ^ T * rsEval (rudinShapiroP k) z‖ =
      ‖rsEval (rudinShapiroP k) z‖ := by simp [norm_pow, hz]
  have hnorm2T : ‖z ^ (2 * T) * rsEval (rudinShapiroP k) z‖ =
      ‖rsEval (rudinShapiroP k) z‖ := by simp [norm_pow, hz]
  apply (Complex.abs_im_le_norm _).trans_lt
  have htri := norm_sub_le
    (rudinShapiroPrefix (N + 1) z - z ^ T * rsEval (rudinShapiroP k) z)
    (z ^ (2 * T) * rsEval (rudinShapiroP k) z)
  have htri' := norm_sub_le (rudinShapiroPrefix (N + 1) z)
    (z ^ T * rsEval (rudinShapiroP k) z)
  rw [hnorm2T] at htri
  rw [hnormT] at htri'
  exact htri.trans_lt (by nlinarith)

end
end Power2ModuleSVP
