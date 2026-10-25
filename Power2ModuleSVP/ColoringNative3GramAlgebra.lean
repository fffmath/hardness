import Power2ModuleSVP.ColoringNative3Gram
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Adjugate arithmetic for the Gram formula. The remaining local algebraic
premise selects a spanning independent row sublist and identifies the
canonical orthogonal projector with its usual Gram formula. -/
namespace Power2ModuleSVP.ColoringRuntime

open PartialColoringAlg ColoringNative
open scoped BigOperators Matrix
set_option maxHeartbeats 700000

/-- Uniqueness of an orthogonal decomposition, using only the already
proved list-projector interface. This avoids introducing a second projector. -/
theorem project_eq_of_orthogonal_remainder {r : ℕ} (C : List (Vec r))
    (v y : Vec r) (hy : OrthogonalTo C y)
    (hrem : ∀ z : Vec r, OrthogonalTo C z → dot z (v - y) = 0) :
    project C v = y := by
  let e := project C v - y
  have heorth : OrthogonalTo C e := by
    intro a ha
    change dot a (project C v - y) = 0
    rw [dot_sub_right, project_orthogonal C v a ha, hy a ha, sub_self]
  have h := hrem e heorth
  have hp := dot_project_of_orthogonal C e v heorth
  have hezero : dot e e = 0 := by
    change dot e (project C v - y) = 0
    rw [dot_sub_right, hp]
    simpa only [dot_sub_right] using h
  exact sub_eq_zero.mp ((dot_self_eq_zero e).mp hezero)

/-- Padding/truncation of the exact integer-scaled constraints. -/
def integerConstraintMatrix (p : ProjectorBatchInput) :
    Matrix (Fin p.2.length) (Fin p.1) ℤ := fun i j =>
  (scaledIntegerRow (p.2.get i)).getD j 0

theorem integerGramMatrix_eq_mul_transpose (p : ProjectorBatchInput) :
    integerGramMatrix p = integerConstraintMatrix p * (integerConstraintMatrix p)ᵀ := by
  ext i j
  rfl

/-- Entrywise integer casting commutes with matrix inversion via the
adjugate formula. No nonsingularity hypothesis is needed for this identity. -/
theorem inverse_intMatrix (n : ℕ) (G : Matrix (Fin n) (Fin n) ℤ) :
    (G.map (Int.castRingHom ℚ))⁻¹ =
      (G.det : ℚ)⁻¹ • G.adjugate.map (Int.castRingHom ℚ) := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  have hd : (G.map (Int.castRingHom ℚ)).det = (G.det : ℚ) :=
    (Int.cast_det G).symm
  have ha : (G.map (Int.castRingHom ℚ)).adjugate =
      G.adjugate.map (Int.castRingHom ℚ) :=
    ((Int.castRingHom ℚ).map_adjugate G).symm
  rw [hd, ha]

/-- Every inverse entry has denominator dividing the integer determinant,
including the singular case (where the inverse is zero). -/
theorem inverse_intMatrix_den_dvd (n : ℕ) (G : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) :
    ((G.map (Int.castRingHom ℚ))⁻¹ i j).den ∣ G.det.natAbs := by
  apply den_dvd_of_eq_int_div (n := G.adjugate i j) (d := G.det)
  rw [inverse_intMatrix]
  change (G.det : ℚ)⁻¹ * (G.adjugate i j : ℚ) = _
  ring

/-- Usual complement projector associated to an integer row matrix and an
integer Gram matrix. It is only used below when the Gram determinant is nonzero. -/
noncomputable def gramComplement {n r : ℕ} (G : Matrix (Fin n) (Fin n) ℤ)
    (A : Matrix (Fin n) (Fin r) ℤ) : Matrix (Fin r) (Fin r) ℚ :=
  1 - (A.map (Int.castRingHom ℚ))ᵀ *
    (G.map (Int.castRingHom ℚ))⁻¹ * A.map (Int.castRingHom ℚ)

theorem gram_correction_eq_adjugate {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℤ) (A : Matrix (Fin n) (Fin r) ℤ) :
    (A.map (Int.castRingHom ℚ))ᵀ * (G.map (Int.castRingHom ℚ))⁻¹ *
      A.map (Int.castRingHom ℚ) =
    (G.det : ℚ)⁻¹ • (Aᵀ * G.adjugate * A).map (Int.castRingHom ℚ) := by
  rw [inverse_intMatrix, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Matrix.map_mul]
  rfl

/-- The complete Gram projector has one integral numerator matrix over the
single determinant; no product of entrywise denominators is introduced. -/
theorem gramComplement_eq_int_div {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℤ) (A : Matrix (Fin n) (Fin r) ℤ)
    (hG : G.det ≠ 0) (j k : Fin r) :
    gramComplement G A j k =
      (((G.det • (1 : Matrix (Fin r) (Fin r) ℤ) - Aᵀ * G.adjugate * A) j k : ℤ) : ℚ) /
        (G.det : ℚ) := by
  have hd : (G.det : ℚ) ≠ 0 := by exact_mod_cast hG
  unfold gramComplement
  rw [gram_correction_eq_adjugate]
  change (1 : Matrix (Fin r) (Fin r) ℚ) j k -
    (G.det : ℚ)⁻¹ * ((Aᵀ * G.adjugate * A) j k : ℚ) = _
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul]
  by_cases hjk : j = k
  · subst k
    simp only [Matrix.one_apply_eq, Int.cast_one, mul_one]
    field_simp
  · simp only [Matrix.one_apply_ne hjk, Int.cast_zero, mul_zero]
    ring

theorem gramComplement_den_dvd {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℤ) (A : Matrix (Fin n) (Fin r) ℤ)
    (hG : G.det ≠ 0) (j k : Fin r) :
    (gramComplement G A j k).den ∣ G.det.natAbs :=
  den_dvd_of_eq_int_div (gramComplement_eq_int_div G A hG j k)

/-- Algebraic identification only: choose a spanning independent sublist
and identify the canonical projector with the inverse-Gram formula. The
adjugate, divisibility, determinant bit and machine arguments are proved
separately and do not occur as fields. -/
structure GramProjectorFormulaHypothesis : Prop where
  projector_formula : ∀ (p : ProjectorBatchInput),
    ∃ rows : List (List ℚ), rows.Sublist p.2 ∧
      (integerGramMatrix (p.1, rows)).det ≠ 0 ∧
      ∀ j k : Fin p.1,
        tableEntry (projectorTable (readConstraints p.1 p.2)) j k =
          gramComplement (integerGramMatrix (p.1, rows))
            (integerConstraintMatrix (p.1, rows)) j k

theorem gramProjectorDivisibility_of_formula (h : GramProjectorFormulaHypothesis) :
    GramProjectorDivisibilityHypothesis := by
  constructor
  intro p
  obtain ⟨rows, hs, hd, hformula⟩ := h.projector_formula p
  refine ⟨rows, hs, ?_, fun j k => ?_⟩
  · rwa [integerGramDet_eq_gramDet]
  · rw [hformula j k, integerGramDet_eq_gramDet]
    exact gramComplement_den_dvd _ _ hd j k

theorem canonicalProjectorDenominator_of_gramFormula
    (h : GramProjectorFormulaHypothesis) : CanonicalProjectorDenominatorHypothesis :=
  canonicalProjectorDenominator_of_gram (gramProjectorDivisibility_of_formula h)

end Power2ModuleSVP.ColoringRuntime
