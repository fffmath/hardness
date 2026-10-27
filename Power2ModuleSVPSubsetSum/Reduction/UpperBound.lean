import Power2ModuleSVPSubsetSum.Reduction.Validity
import Power2ModuleSVPSubsetSum.Reduction.UnitAction

/-! # The explicit upper bound on the first minimum

The first basis column is a nonzero module vector of maximum norm exactly `2M`.
This supplies the upper half of Proposition 4.2's NO-instance bounds.

Paper: `paper/power2svp-subsetsum.pdf`, Proposition 4.2.
-/
namespace Power2ModuleSVPSubsetSum.Reduction
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- The constant polynomial one has coefficient maximum norm one. -/
theorem coeffSup_coeffOne {n : ℕ} (hn : 0 < n) : coeffSup (coeffOne hn) = 1 := by
  apply Nat.le_antisymm
  · apply (coeffSup_le_iff _ _).mpr
    intro i
    simp only [coeffOne, monomial]
    split_ifs <;> norm_num
  · simpa [coeffOne] using natAbs_le_coeffSup (coeffOne hn) ⟨0, hn⟩

/-- The scalar coordinate determines the first column's norm once it dominates `H`. -/
theorem leftColumn_norm {n : ℕ} (hn : 0 < n) (H : Coeff n) (M : ℕ)
    (hH : coeffSup H ≤ M) : pairSup (leftColumn hn H M) = 2 * M := by
  have he : pairSup (leftColumn hn H M) = max (2 * coeffSup H) (2 * M) := by
    simp only [pairSup, leftColumn, coeffSup_smul, coeffSup_coeffOne,
      Int.natAbs_mul, Int.natAbs_natCast]
    norm_num
  rw [he]
  exact max_eq_right (Nat.mul_le_mul_left 2 hH)

/-- The gadget's first column is obtained with constant first multiplier and zero second
multiplier. -/
theorem gadget_firstColumn_vector (w : List ℕ) (B : ℕ) :
    moduleVector (gadgetA w B) (gadgetB w B)
      (coeffOne (degree_dyadic w.length).pos) 0 = gadgetA w B := by
  simp only [moduleVector, mul_zero, add_zero]
  apply Prod.ext
  · exact mul_coeffOne_right (degree_dyadic w.length).pos _
  · exact mul_coeffOne_right (degree_dyadic w.length).pos _

/-- The gadget's first column has maximum norm exactly `2M`. -/
theorem gadget_firstColumn_norm (w : List ℕ) (B : ℕ) :
    pairSup (moduleVector (gadgetA w B) (gadgetB w B)
      (coeffOne (degree_dyadic w.length).pos) 0) = 2 * (gadget w B).M := by
  rw [gadget_firstColumn_vector]
  apply leftColumn_norm
  apply (coeffSup_le_coeffL1 (gadgetH w B)).trans
  rw [gadget_M]
  change Rigidity.F (gadgetH w B) ≤ Rigidity.M (gadgetH w B) (gadgetV w B)
  unfold Rigidity.M
  omega

/-- The first column is nonzero for every source input. -/
theorem gadget_firstColumn_ne_zero (w : List ℕ) (B : ℕ) :
    moduleVector (gadgetA w B) (gadgetB w B)
      (coeffOne (degree_dyadic w.length).pos) 0 ≠ 0 := by
  intro hzero
  have hn := gadget_firstColumn_norm w B
  rw [hzero] at hn
  have hz : pairSup (0 : Coeff (2 * halfDegree w.length) ×
      Coeff (2 * halfDegree w.length)) = 0 := (pairSup_eq_zero_iff _).mpr rfl
  rw [hz] at hn
  have := gadget_M_pos w B
  omega

/-- An explicit nonzero vector realizes norm `2M` in every constructed module. -/
theorem gadget_has_vector_norm_two_M (w : List ℕ) (B : ℕ) :
    ∃ a b : Coeff (2 * halfDegree w.length),
      moduleVector (gadgetA w B) (gadgetB w B) a b ≠ 0 ∧
      pairSup (moduleVector (gadgetA w B) (gadgetB w B) a b) = 2 * (gadget w B).M :=
  ⟨coeffOne (degree_dyadic w.length).pos, 0,
    gadget_firstColumn_ne_zero w B, gadget_firstColumn_norm w B⟩

/-- Any first minimum of the constructed module is at most `2M`. -/
theorem gadget_firstMinimum_le_two_M (w : List ℕ) (B r : ℕ)
    (hr : FirstMinimum (gadgetA w B) (gadgetB w B) r) :
    r ≤ 2 * (gadget w B).M := by
  obtain ⟨a, b, hne, hn⟩ := gadget_has_vector_norm_two_M w B
  exact hn ▸ hr.2 a b hne

/-- An integral coefficient module containing a nonzero vector has an attained first minimum.
Natural-number well ordering suffices; no analytic lattice minimum theorem is needed. -/
theorem firstMinimum_exists_of_nonzero_vector {d : ℕ} (a b : Coeff d × Coeff d)
    (u v : Coeff d) (hne : moduleVector a b u v ≠ 0) :
    ∃ r : ℕ, FirstMinimum a b r := by
  classical
  let P : ℕ → Prop := fun r =>
    ∃ s t : Coeff d, moduleVector a b s t ≠ 0 ∧ pairSup (moduleVector a b s t) = r
  have hp : ∃ r, P r := ⟨_, u, v, hne, rfl⟩
  refine ⟨Nat.find hp, Nat.find_spec hp, ?_⟩
  intro s t hst
  exact Nat.find_min' hp ⟨s, t, hst, rfl⟩

/-- Every constructed module has an attained first minimum bounded above by `2M`. -/
theorem gadget_firstMinimum_exists_le_two_M (w : List ℕ) (B : ℕ) :
    ∃ r : ℕ, FirstMinimum (gadgetA w B) (gadgetB w B) r ∧ r ≤ 2 * (gadget w B).M := by
  obtain ⟨a, b, hne, _⟩ := gadget_has_vector_norm_two_M w B
  obtain ⟨r, hr⟩ := firstMinimum_exists_of_nonzero_vector _ _ a b hne
  exact ⟨r, hr, gadget_firstMinimum_le_two_M w B r hr⟩

end Power2ModuleSVPSubsetSum.Reduction
