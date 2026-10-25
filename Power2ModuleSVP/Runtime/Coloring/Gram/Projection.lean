import Power2ModuleSVP.Runtime.Coloring.Gram.RowInduction

/-!
# Projection

Generic rational Gram projection identities. These use the existing
canonical list projector through uniqueness of orthogonal decomposition.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open PartialColoringAlg
open scoped BigOperators Matrix

/-- Orthogonal-complement projector given by the rational Gram inverse formula. -/
noncomputable def rationalGramComplement {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) ℚ) : Matrix (Fin r) (Fin r) ℚ :=
  1 - Aᵀ * (A * Aᵀ)⁻¹ * A

theorem rationalGramComplement_annihilate {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) ℚ) (hG : (A * Aᵀ).det ≠ 0) :
    A * rationalGramComplement A = 0 := by
  unfold rationalGramComplement
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), Matrix.one_mul, sub_self]

theorem rationalGramComplement_fix {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) ℚ) (x : Vec r) (hx : A *ᵥ x = 0) :
    rationalGramComplement A *ᵥ x = x := by
  simp only [rationalGramComplement, Matrix.sub_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero]

theorem rationalGramComplement_symmetric {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) ℚ) :
    (rationalGramComplement A)ᵀ = rationalGramComplement A := by
  simp only [rationalGramComplement, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv,
    Matrix.mul_assoc]

/-- Any nonsingular rational Gram formula gives exactly the canonical
projector whenever the row nullspaces agree. -/
theorem project_eq_rationalGramComplement {n r : ℕ}
    (C : List (Vec r)) (A : Matrix (Fin n) (Fin r) ℚ)
    (hG : (A * Aᵀ).det ≠ 0)
    (horth : ∀ x : Vec r, OrthogonalTo C x ↔ A *ᵥ x = 0) (v : Vec r) :
    project C v = rationalGramComplement A *ᵥ v := by
  apply project_eq_of_orthogonal_remainder C v _
  · apply (horth _).mpr
    rw [Matrix.mulVec_mulVec, rationalGramComplement_annihilate A hG, Matrix.zero_mulVec]
  · intro z hz
    have hz' := (horth z).mp hz
    simp only [rationalGramComplement, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [sub_sub_cancel]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change z ⬝ᵥ (Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ (A *ᵥ v))) = 0
    rw [Matrix.dotProduct_transpose_mulVec, hz', dotProduct_zero]

/-- Row clearing is exact even at truncated or missing coordinates. -/
theorem scaledIntegerRow_getD (row : List ℚ) (j : ℕ) :
    ((scaledIntegerRow row).getD j 0 : ℚ) =
      (rowDenominator row : ℚ) * row.getD j 0 := by
  by_cases hj : j < row.length
  · simpa [scaledIntegerRow, List.getD_eq_getElem?_getD, hj] using
      scaledIntegerRow_entry row row[j] (List.getElem_mem hj)
  · simp [scaledIntegerRow, List.getD_eq_getElem?_getD, hj]

theorem integerConstraintMatrix_mulVec (p : ProjectorBatchInput) (x : Vec p.1)
    (i : Fin p.2.length) :
    (integerConstraintMatrix p |>.map (Int.castRingHom ℚ) |>.mulVec x) i =
      (rowDenominator (p.2.get i) : ℚ) * dot (fun j => (p.2.get i).getD j 0) x := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, integerConstraintMatrix,
    Int.coe_castRingHom, dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [scaledIntegerRow_getD]
  ring

theorem integerConstraintMatrix_orthogonal (p : ProjectorBatchInput) (x : Vec p.1) :
    OrthogonalTo (readConstraints p.1 p.2) x ↔
      (integerConstraintMatrix p |>.map (Int.castRingHom ℚ) |>.mulVec x) = 0 := by
  constructor
  · intro hx
    funext i
    rw [integerConstraintMatrix_mulVec]
    have hm : (fun j : Fin p.1 => (p.2.get i).getD j 0) ∈ readConstraints p.1 p.2 :=
      List.mem_map.mpr ⟨_, List.get_mem p.2 i, rfl⟩
    rw [hx _ hm, mul_zero]
    rfl
  · intro hx a ha
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrow
    have he := congrFun hx i
    rw [integerConstraintMatrix_mulVec] at he
    have hd : (rowDenominator (p.2.get i) : ℚ) ≠ 0 := by
      exact_mod_cast (rowDenominator_pos (p.2.get i)).ne'
    have hz := (mul_eq_zero.mp he).resolve_left hd
    simpa only [hi] using hz

end Power2ModuleSVP.ColoringRuntime
