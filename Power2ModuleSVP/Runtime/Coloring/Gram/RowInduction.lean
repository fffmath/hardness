import Power2ModuleSVP.Runtime.Coloring.Gram.Adjugate

/-!
# Row Induction

Row-by-row reduction of the Gram identification to one local Schur
complement identity. Dependent and zero constraints are removed by their
zero residual, with no separate spanning-basis selection premise.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open PartialColoringAlg
open scoped BigOperators
set_option maxHeartbeats 500000

noncomputable def gramResidual (r : ℕ) (rows : List (List ℚ)) (a : List ℚ) : Vec r :=
  fun j => ∑ k : Fin r,
    gramComplement (integerGramMatrix (r, rows)) (integerConstraintMatrix (r, rows)) j k *
      a.getD k 0

/-- Single-row Schur complement identity. This is independent of the
canonical list projector, encoding lengths, and machine models. A nonzero
residual makes the enlarged Gram matrix nonsingular, and its complementary
projector is the usual rank-one update. -/
structure GramSchurUpdateHypothesis : Prop where
  prepend_update : ∀ (r : ℕ) (rows : List (List ℚ)) (a : List ℚ),
    (integerGramMatrix (r, rows)).det ≠ 0 → gramResidual r rows a ≠ 0 →
      (integerGramMatrix (r, a :: rows)).det ≠ 0 ∧
      ∀ j k : Fin r,
        gramComplement (integerGramMatrix (r, a :: rows))
          (integerConstraintMatrix (r, a :: rows)) j k =
        gramComplement (integerGramMatrix (r, rows)) (integerConstraintMatrix (r, rows)) j k -
          gramResidual r rows a j * gramResidual r rows a k /
            dot (gramResidual r rows a) (gramResidual r rows a)

private theorem projectorTable_cons_entry {r : ℕ} (a : Vec r) (C : List (Vec r))
    (j k : Fin r) :
    tableEntry (projectorTable (a :: C)) j k = tableEntry (projectorTable C) j k -
      tableApply (projectorTable C) a j * tableApply (projectorTable C) a k /
        dot (tableApply (projectorTable C) a) (tableApply (projectorTable C) a) := by
  simp [projectorTable, tableEntry, List.getD_eq_getElem?_getD]

/-- The entire basis-selection and dependent-row problem follows by
induction from the single-row block identity. -/
theorem gramProjectorFormula_of_schur (h : GramSchurUpdateHypothesis) :
    GramProjectorFormulaHypothesis := by
  constructor
  rintro ⟨r, inputRows⟩
  induction inputRows with
  | nil =>
    refine ⟨[], .refl _, ?_, fun j k => ?_⟩
    · simp
    · simp [readConstraints, projectorTable, tableEntry, gramComplement,
        coordinate, Matrix.one_apply, List.getD_eq_getElem?_getD,
        eq_comm]
  | cons a inputRows ih =>
    obtain ⟨rows, hs, hd, hformula⟩ := ih
    have happ : tableApply (projectorTable (readConstraints r inputRows))
        (fun j : Fin r => a.getD j 0) = gramResidual r rows a := by
      funext j
      unfold tableApply gramResidual
      apply Finset.sum_congr rfl
      intro k _
      rw [hformula j k]
    by_cases hz : gramResidual r rows a = 0
    · refine ⟨rows, hs.cons a, hd, fun j k => ?_⟩
      change tableEntry (projectorTable ((fun j : Fin r => a.getD j 0) ::
        readConstraints r inputRows)) j k = _
      rw [projectorTable_cons_entry, happ, hz]
      simp only [Pi.zero_apply, zero_mul, zero_div, sub_zero]
      exact hformula j k
    · obtain ⟨hd', hupdate⟩ := h.prepend_update r rows a hd hz
      refine ⟨a :: rows, hs.cons_cons a, hd', fun j k => ?_⟩
      change tableEntry (projectorTable ((fun j : Fin r => a.getD j 0) ::
        readConstraints r inputRows)) j k = _
      rw [projectorTable_cons_entry, happ, hformula j k]
      exact (hupdate j k).symm

theorem canonicalProjectorDenominator_of_schur
    (h : GramSchurUpdateHypothesis) : CanonicalProjectorDenominatorHypothesis :=
  canonicalProjectorDenominator_of_gramFormula (gramProjectorFormula_of_schur h)

end Power2ModuleSVP.ColoringRuntime
