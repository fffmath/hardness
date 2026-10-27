import Power2ModuleSVPSubsetSum.Reduction.Bridge
import Power2ModuleSVPSubsetSum.Reduction.Model

/-!
# Validity of the constructed basis

The computed arrays form a full-rank rank-two module. The proof identifies their ring
determinant and uses the existing field-independence theorem to justify `listIndependent`.

Paper: `paper/power2svp-subsetsum.pdf`, Proposition 4.2.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Power2ModuleSVPSubsetSum.Reduction
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- The coefficient polynomial `H` computed by the executable gadget. -/
abbrev gadgetH (w : List ℕ) (B : ℕ) : Coeff (2 * halfDegree w.length) :=
  IdealCVP.ofList (gadget w B).H

/-- The coefficient error polynomial `V`. -/
abbrev gadgetV (w : List ℕ) (B : ℕ) : Coeff (2 * halfDegree w.length) :=
  IdealCVP.ofList (gadget w B).V

/-- The Boolean mask in the output ring. -/
abbrev gadgetU (w : List ℕ) (B : ℕ) : Coeff (2 * halfDegree w.length) :=
  IdealCVP.ofList (gadget w B).u

/-- The first output column, in the coefficient model. -/
def gadgetA (w : List ℕ) (B : ℕ) :
    Coeff (2 * halfDegree w.length) × Coeff (2 * halfDegree w.length) :=
  leftColumn (degree_dyadic w.length).pos (gadgetH w B) (gadget w B).M

/-- The second output column, in the coefficient model. -/
def gadgetB (w : List ℕ) (B : ℕ) :
    Coeff (2 * halfDegree w.length) × Coeff (2 * halfDegree w.length) :=
  rightColumn (gadgetH w B) (gadgetU w B)
    (Rigidity.Q (gadgetH w B) (gadgetV w B) + gadgetV w B) (gadget w B).M

/-- Both stored columns agree with their coefficient-model formulas. -/
theorem positiveReduce_interpretation (w : List ℕ) (B : ℕ) :
    let x := positiveReduce w B
    (IdealCVP.ofList (d := degree w.length) x.1.2.1.1,
      IdealCVP.ofList (d := degree w.length) x.1.2.1.2) = gadgetA w B ∧
    (IdealCVP.ofList (d := degree w.length) x.1.2.2.1,
      IdealCVP.ofList (d := degree w.length) x.1.2.2.2) = gadgetB w B := by
  obtain ⟨hA, hB⟩ := positiveReduce_columns w B
  constructor
  · exact hA
  · rw [hB]
    unfold gadgetB rightColumn
    rw [gadget_Q]
    apply Prod.ext
    · dsimp only [gadgetH, gadgetV, gadgetU]
      ext i
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
      ring
    · rfl

/-- Shape and a nonzero coefficient determinant imply the fixed validity predicate. -/
theorem wellFormed_of_shape_det (x : SVPInput)
    (hd : Dyadic x.1.1)
    (hl : x.1.2.1.1.length = x.1.1 ∧ x.1.2.1.2.length = x.1.1 ∧
      x.1.2.2.1.length = x.1.1 ∧ x.1.2.2.2.length = x.1.1)
    (hdet : determinant
      (IdealCVP.ofList (d := x.1.1) x.1.2.1.1, IdealCVP.ofList x.1.2.1.2)
      (IdealCVP.ofList x.1.2.2.1, IdealCVP.ofList x.1.2.2.2) ≠ 0) :
    x.WellFormed := by
  let : Fact (∃ k, x.1.1 = 2 ^ k) := ⟨hd⟩
  refine ⟨hd, hl.1, hl.2.1, hl.2.2.1, hl.2.2.2, ?_⟩
  rw [IdealCVP.listIndependent_iff, IdealCVP.ModuleSIVP.independent_iff]
  intro h
  apply hdet
  apply (toQuot_bijective hd.pos).injective
  rw [toQuot_zero]
  have he : toQuot (determinant
      (IdealCVP.ofList (d := x.1.1) x.1.2.1.1, IdealCVP.ofList x.1.2.1.2)
      (IdealCVP.ofList x.1.2.2.1, IdealCVP.ofList x.1.2.2.2)) =
      toQuot (IdealCVP.ofList (d := x.1.1) x.1.2.1.1) *
        toQuot (IdealCVP.ofList (d := x.1.1) x.1.2.2.2) -
      toQuot (IdealCVP.ofList (d := x.1.1) x.1.2.1.2) *
        toQuot (IdealCVP.ofList (d := x.1.1) x.1.2.2.1) := by
    rw [determinant, ← quotEquiv_apply hd.pos, map_sub]
    simp only [quotEquiv_apply, toQuot_mul hd.pos]
  rw [he]
  exact h

/-- The basis has the paper's explicit nonzero determinant. -/
theorem gadget_determinant_ne_zero (w : List ℕ) (B : ℕ) :
    determinant (gadgetA w B) (gadgetB w B) ≠ 0 := by
  apply model_determinant_ne_zero
  · exact gadget_M_pos w B
  · exact Rigidity.Q_add_V_ne_zero
      (show 0 < halfDegree w.length from lt_of_lt_of_le (by omega)
        (two_le_halfDegree w.length)) _ _

/-- Proposition 4.2: every constructed basis is a well-formed target instance. -/
theorem positiveReduce_wellFormed (w : List ℕ) (B : ℕ) :
    (positiveReduce w B).WellFormed := by
  apply wellFormed_of_shape_det _ (positiveReduce_dyadic w B) (positiveReduce_lengths w B)
  obtain ⟨hA, hB⟩ := positiveReduce_interpretation w B
  rw [hA, hB]
  exact gadget_determinant_ne_zero w B

/-- Target-language membership reduces to the coefficient-model short-vector predicate. -/
theorem positiveReduce_mem_iff (w : List ℕ) (B : ℕ) :
    positiveReduce w B ∈ ModuleSVPLang ↔
      ModuleYes (gadgetA w B) (gadgetB w B) (gadget w B).M := by
  change (positiveReduce w B).WellFormed ∧ _ ↔ _
  rw [and_iff_right (positiveReduce_wellFormed w B)]
  obtain ⟨hA, hB⟩ := positiveReduce_interpretation w B
  rw [hA, hB]
  rfl

end Power2ModuleSVPSubsetSum.Reduction
