import Power2ModuleSVPSubsetSum.Reduction.ExactNorm
import Power2ModuleSVPSubsetSum.Reduction.Validity

/-! # Exact norm of the Boolean module vector

Relate Lemma 4.1's polynomial formula to the stored columns of the reduction.

Paper: `paper/power2svp-subsetsum.pdf`, Lemma 4.1 and equation (4.5).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Power2ModuleSVPSubsetSum.Reduction
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- The output degree contains all weight positions. -/
theorem length_le_outputDegree (s : ℕ) : s ≤ degree s := by
  have := length_le_halfDegree s
  change s ≤ 2 * halfDegree s
  omega

/-- Lemma 4.1 in the exact coefficient-model module interface. -/
theorem boolean_vector_norm (w : List ℕ) (B : ℕ) (ξ : Fin w.length → Bool) :
    pairSup (moduleVector (gadgetA w B) (gadgetB w B)
      (booleanWord (length_le_outputDegree w.length) ξ)
      (coeffOne (degree_dyadic w.length).pos)) =
      (gadget w B).M + 2 * ((∑ j : Fin w.length,
        (w.get j : ℤ) * (if ξ j then 1 else 0)) - (B : ℤ)).natAbs := by
  unfold gadgetA gadgetB
  rw [model_vector, mul_coeffOne_right, mul_coeffOne_right]
  have hU : gadgetU w B =
      IdealCVP.ofList (d := degree w.length) (mask (degree w.length) w.length) := rfl
  have hQ : Rigidity.Q (gadgetH w B) (gadgetV w B) =
      IdealCVP.ofList (d := degree w.length) (gadget w B).Q := (gadget_Q w B).symm
  rw [hU, hQ, sub_add_eq_sub_sub]
  exact gadget_exactNorm w B ξ

/-- Every Boolean module vector is nonzero because its norm is at least `M > 0`. -/
theorem boolean_vector_ne_zero (w : List ℕ) (B : ℕ) (ξ : Fin w.length → Bool) :
    moduleVector (gadgetA w B) (gadgetB w B)
      (booleanWord (length_le_outputDegree w.length) ξ)
      (coeffOne (degree_dyadic w.length).pos) ≠ 0 := by
  intro hzero
  have hnorm := boolean_vector_norm w B ξ
  rw [hzero] at hnorm
  have hM := gadget_M_pos w B
  simp only [pairSup, Prod.fst_zero, Prod.snd_zero, coeffSup_zero, max_self] at hnorm
  omega

/-- A Boolean module vector lies inside radius `M` exactly for a satisfying source word. -/
theorem boolean_vector_short_iff (w : List ℕ) (B : ℕ) (ξ : Fin w.length → Bool) :
    pairSup (moduleVector (gadgetA w B) (gadgetB w B)
      (booleanWord (length_le_outputDegree w.length) ξ)
      (coeffOne (degree_dyadic w.length).pos)) ≤ (gadget w B).M ↔
      (∑ j : Fin w.length, (w.get j : ℤ) * (if ξ j then 1 else 0)) = (B : ℤ) := by
  rw [boolean_vector_norm]
  constructor
  · intro h
    have ha : ((∑ j : Fin w.length,
        (w.get j : ℤ) * (if ξ j then 1 else 0)) - (B : ℤ)).natAbs = 0 := by omega
    exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp ha)
  · intro h
    rw [h, sub_self]
    simp

end Power2ModuleSVPSubsetSum.Reduction
