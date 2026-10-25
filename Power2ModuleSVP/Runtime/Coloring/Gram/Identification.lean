import Power2ModuleSVP.Runtime.Coloring.Gram.Kernel

/-!
# Identification

Complete canonical-projector Gram identification. Row clearing preserves
nullspaces, and the rational Gram kernel argument handles independent row
extensions. Zero residuals are handled by the proved row-selection induction.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open PartialColoringAlg
open scoped BigOperators Matrix

/-- Cast the denominator-cleared integral constraint matrix to rational coefficients. -/
def rationalConstraintMatrix (p : ProjectorBatchInput) :
    Matrix (Fin p.2.length) (Fin p.1) ℚ :=
  (integerConstraintMatrix p).map (Int.castRingHom ℚ)

theorem rationalConstraint_gram (p : ProjectorBatchInput) :
    (integerGramMatrix p).map (Int.castRingHom ℚ) =
      rationalConstraintMatrix p * (rationalConstraintMatrix p)ᵀ := by
  rw [integerGramMatrix_eq_mul_transpose, Matrix.map_mul]
  rfl

theorem rationalComplement_eq_int (p : ProjectorBatchInput) :
    rationalGramComplement (rationalConstraintMatrix p) =
      gramComplement (integerGramMatrix p) (integerConstraintMatrix p) := by
  unfold rationalGramComplement gramComplement
  rw [rationalConstraint_gram]
  rfl

theorem rationalConstraint_det_ne_zero (p : ProjectorBatchInput)
    (hd : (integerGramMatrix p).det ≠ 0) :
    (rationalConstraintMatrix p * (rationalConstraintMatrix p)ᵀ).det ≠ 0 := by
  rw [← rationalConstraint_gram]
  simp only [Int.coe_castRingHom]
  rw [← Int.cast_det]
  exact_mod_cast hd

theorem canonical_table_of_gram_det (p : ProjectorBatchInput)
    (hd : (integerGramMatrix p).det ≠ 0) (j k : Fin p.1) :
    tableEntry (projectorTable (readConstraints p.1 p.2)) j k =
      gramComplement (integerGramMatrix p) (integerConstraintMatrix p) j k := by
  let A := rationalConstraintMatrix p
  have hp := project_eq_rationalGramComplement (readConstraints p.1 p.2) A
    (rationalConstraint_det_ne_zero p hd) (integerConstraintMatrix_orthogonal p)
    (coordinate j)
  have hs := congrArg (fun T : Matrix (Fin p.1) (Fin p.1) ℚ => T j k)
    (rationalGramComplement_symmetric A)
  calc
    _ = project (readConstraints p.1 p.2) (coordinate j) k := projectorTable_spec _ j k
    _ = (rationalGramComplement A *ᵥ coordinate j) k := congrFun hp k
    _ = rationalGramComplement A k j := by simp [Matrix.mulVec, dotProduct, coordinate]
    _ = rationalGramComplement A j k := hs
    _ = _ := congrArg (fun T : Matrix (Fin p.1) (Fin p.1) ℚ => T j k)
      (rationalComplement_eq_int p)

theorem rationalConstraint_cons (r : ℕ) (rows : List (List ℚ)) (a : List ℚ) :
    rationalConstraintMatrix (r, a :: rows) =
      consRows (rationalConstraintMatrix (r, rows))
        (fun j : Fin r => ((scaledIntegerRow a).getD j 0 : ℚ)) := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [rationalConstraintMatrix, integerConstraintMatrix, consRows]
  · simp [rationalConstraintMatrix, integerConstraintMatrix, consRows]

theorem rationalComplement_raw_residual (r : ℕ) (rows : List (List ℚ)) (a : List ℚ) :
    rationalGramComplement (rationalConstraintMatrix (r, rows)) *ᵥ
      (fun j : Fin r => a.getD j 0) = gramResidual r rows a := by
  rw [rationalComplement_eq_int]
  rfl

theorem integerGram_cons_det_ne_zero (r : ℕ) (rows : List (List ℚ)) (a : List ℚ)
    (hd : (integerGramMatrix (r, rows)).det ≠ 0)
    (hq : gramResidual r rows a ≠ 0) :
    (integerGramMatrix (r, a :: rows)).det ≠ 0 := by
  let A := rationalConstraintMatrix (r, rows)
  let a' : Vec r := fun j => ((scaledIntegerRow a).getD j 0 : ℚ)
  have ha : a' = (rowDenominator a : ℚ) • (fun j : Fin r => a.getD j 0) := by
    funext j
    exact scaledIntegerRow_getD a j
  have hscale : (rowDenominator a : ℚ) ≠ 0 := by
    exact_mod_cast (rowDenominator_pos a).ne'
  have hq' : rationalGramComplement A *ᵥ a' ≠ 0 := by
    rw [ha, Matrix.mulVec_smul, rationalComplement_raw_residual]
    exact smul_ne_zero hscale hq
  have hn := gram_cons_det_ne_zero A a' (rationalConstraint_det_ne_zero _ hd) hq'
  have hn' :
      (rationalConstraintMatrix (r, a :: rows) *
        (rationalConstraintMatrix (r, a :: rows))ᵀ).det ≠ 0 := by
    rw [rationalConstraint_cons]
    exact hn
  intro hz
  apply hn'
  rw [← rationalConstraint_gram]
  simp only [Int.coe_castRingHom]
  rw [← Int.cast_det, hz, Int.cast_zero]

private theorem projectorTable_prepend_entry {r : ℕ} (a : Vec r) (C : List (Vec r))
    (j k : Fin r) :
    tableEntry (projectorTable (a :: C)) j k = tableEntry (projectorTable C) j k -
      tableApply (projectorTable C) a j * tableApply (projectorTable C) a k /
        dot (tableApply (projectorTable C) a) (tableApply (projectorTable C) a) := by
  simp [projectorTable, tableEntry, List.getD_eq_getElem?_getD]

/-- The local Schur identity follows from the generic Gram projector and
kernel arguments; no unproved algebraic premise remains. -/
theorem gramSchurUpdate : GramSchurUpdateHypothesis := by
  constructor
  intro r rows a hd hq
  have hd' := integerGram_cons_det_ne_zero r rows a hd hq
  refine ⟨hd', fun j k => ?_⟩
  have htable := canonical_table_of_gram_det (r, rows) hd
  have hnew := canonical_table_of_gram_det (r, a :: rows) hd'
  have happ : tableApply (projectorTable (readConstraints r rows))
      (fun j : Fin r => a.getD j 0) = gramResidual r rows a := by
    funext j
    unfold tableApply gramResidual
    apply Finset.sum_congr rfl
    intro k _
    rw [htable j k]
  rw [← hnew j k]
  change tableEntry (projectorTable ((fun j : Fin r => a.getD j 0) ::
    readConstraints r rows)) j k = _
  rw [projectorTable_prepend_entry, happ, htable j k]

/-- Unconditional polynomial canonical-projector denominator bound. -/
theorem canonicalProjectorDenominator : CanonicalProjectorDenominatorHypothesis :=
  canonicalProjectorDenominator_of_schur gramSchurUpdate

end Power2ModuleSVP.ColoringRuntime
