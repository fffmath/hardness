import Power2ModuleSVP.FlatFrontend3Grid
import Power2ModuleSVP.SeedGeometryComponents

/-! Degree and sampling data for the implemented cosine polynomial. -/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators
noncomputable section

theorem cosineCoefficient_abs (N j : ℕ) : |(cosineCoefficient N j : ℝ)| ≤ 1 := by
  cases h : cosineSelected N j with
  | false => simp [cosineCoefficient_unselected h]
  | true => rcases cosineCoefficient_sign h with h | h <;> simp [h]

def implementedCosineData (N : ℕ) : SeedCosineData N where
  support := (Finset.range N).image (fun j => 2 * (j + 1))
  coeff := fun k => cosineCoefficient N (k / 2)
  card_le := by exact (Finset.card_image_le).trans (by simp)
  frequency_le := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have := Finset.mem_range.mp hj
    omega
  coeff_le := fun _ _ => cosineCoefficient_abs _ _

theorem implementedCosineData_polynomial (N : ℕ) :
    (implementedCosineData N).realPolynomial =
      (cosinePolynomial N).map (Int.castRingHom ℝ) := by
  simp only [implementedCosineData, SeedCosineData.realPolynomial,
    Power2ModuleSVP.cosinePolynomial, cosinePolynomial, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.Chebyshev.map_T,
    Int.coe_castRingHom]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j _
    rw [Nat.mul_div_cancel_left _ (by omega)]
    push_cast
    rfl
  · intro a _ b _ hab
    dsimp only at hab
    omega

theorem implementedCosineData_angle {d : ℕ} (hd : d = 4 * seedN d + 4) (θ : ℝ) :
    (implementedCosineData (seedN d)).realPolynomial.eval (Real.cos θ) = cosine d θ := by
  rw [implementedCosineData_polynomial, ← cosine_eq_polynomial hd]

/-- The reduced polynomial has degree bounded by the last selected
frequency, rather than by twice that frequency. -/
theorem reducedCosinePolynomial_degree (N : ℕ) :
    (reducedCosinePolynomial N).natDegree ≤ stageWidth (stage N) := by
  unfold reducedCosinePolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  by_cases hj : j + 1 ≤ stageWidth (stage N)
  · exact Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_C, Polynomial.Chebyshev.natDegree_T,
        ← Int.natCast_one, ← Int.natCast_add, Int.natAbs_natCast, Nat.zero_add] using hj)
  · have hz : cosineCoefficient N (j + 1) = 0 := by
      apply cosineCoefficient_unselected (N := N)
      have hp := block_parameters N
      have hw := stageWidth_block N
      have hh : ¬ cosineSelected N (j + 1) = true := by
        rw [cosineSelected_iff]
        omega
      exact Bool.eq_false_iff.mpr hh
    simp only [hz, Polynomial.C_0, zero_mul, Polynomial.natDegree_zero, Nat.zero_le]

theorem reducedCosinePolynomial_real_degree (N : ℕ) :
    ((reducedCosinePolynomial N).map (Int.castRingHom ℝ)).natDegree ≤ stageWidth (stage N) :=
  (Polynomial.natDegree_map_le).trans (reducedCosinePolynomial_degree N)

end
end FlatFrontend
end Power2ModuleSVP
