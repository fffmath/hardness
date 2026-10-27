import Power2ModuleSVPSubsetSum.Reduction.Map
import Power2ModuleSVPSubsetSum.Reduction.Soundness
import Power2ModuleSVPSubsetSum.Reduction.ExactVector
import Power2ModuleSVPSubsetSum.Reduction.Gap
import Power2ModuleSVPSubsetSum.Reduction.UpperBound

/-!
# Correctness of the total Subset Sum reduction

The executable map is correct for complexitylib's full multiset Subset Sum language.
All outputs are well formed. YES instances attain their radius as the exact first minimum;
NO instances have an additive unit gap for every nonzero vector.

Paper: `paper/power2svp-subsetsum.pdf`, Sections 4.1–4.2, Proposition 4.2.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Power2ModuleSVPSubsetSum.Reduction
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- Every nonzero vector inside the gadget's radius lies on its boundary. -/
theorem short_norm_eq_M (w : List ℕ) (B : ℕ)
    (a b : Coeff (2 * halfDegree w.length))
    (hne : moduleVector (gadgetA w B) (gadgetB w B) a b ≠ 0)
    (hshort : pairSup (moduleVector (gadgetA w B) (gadgetB w B) a b) ≤
      (gadget w B).M) :
    pairSup (moduleVector (gadgetA w B) (gadgetB w B) a b) = (gadget w B).M := by
  obtain ⟨ξ, he⟩ := short_normalizes_to_boolean w B a b hne hshort
  have hsat := (boolean_vector_short_iff w B ξ).mp (he.le.trans hshort)
  rw [boolean_vector_norm, hsat, sub_self, Int.natAbs_zero, Nat.mul_zero, Nat.add_zero] at he
  exact he.symm

/-- The paper's gadget has a short vector exactly when its weights have a subset sum. -/
theorem gadget_correct (w : List ℕ) (B : ℕ) :
    (w, B) ∈ Cslib.Complexity.SubsetSum ↔
      ModuleYes (gadgetA w B) (gadgetB w B) (gadget w B).M := by
  rw [subsetSum_iff_bool]
  constructor
  · rintro ⟨ξ, hξ⟩
    have hξ' : (∑ j : Fin w.length,
        (w.get j : ℤ) * (if ξ j then 1 else 0)) = (B : ℤ) := by
      exact_mod_cast hξ
    exact ⟨booleanWord (length_le_outputDegree w.length) ξ,
      coeffOne (degree_dyadic w.length).pos, boolean_vector_ne_zero w B ξ,
      (boolean_vector_short_iff w B ξ).mpr hξ'⟩
  · rintro ⟨a, b, hne, hshort⟩
    obtain ⟨ξ, he⟩ := short_normalizes_to_boolean w B a b hne hshort
    refine ⟨ξ, ?_⟩
    have hξ := (boolean_vector_short_iff w B ξ).mp (he.le.trans hshort)
    exact_mod_cast hξ

/-- Correctness of the array program before the total map's zero/empty preprocessing. -/
theorem positiveReduce_correct (w : List ℕ) (B : ℕ) :
    (w, B) ∈ Cslib.Complexity.SubsetSum ↔ positiveReduce w B ∈ ModuleSVPLang := by
  rw [positiveReduce_mem_iff]
  exact gadget_correct w B

/-- YES sources have exact first minimum `M`. -/
theorem gadget_yes_gap (w : List ℕ) (B : ℕ)
    (hy : (w, B) ∈ Cslib.Complexity.SubsetSum) :
    FirstMinimum (gadgetA w B) (gadgetB w B) (gadget w B).M := by
  exact firstMinimum_of_ModuleYes_of_short_eq _ _ _ ((gadget_correct w B).mp hy)
    (short_norm_eq_M w B)

/-- NO sources force every nonzero gadget vector to have norm at least `M+1`. -/
theorem gadget_no_gap (w : List ℕ) (B : ℕ)
    (hn : (w, B) ∉ Cslib.Complexity.SubsetSum)
    (a b : Coeff (2 * halfDegree w.length))
    (hne : moduleVector (gadgetA w B) (gadgetB w B) a b ≠ 0) :
    (gadget w B).M + 1 ≤ pairSup (moduleVector (gadgetA w B) (gadgetB w B) a b) := by
  exact gap_of_not_ModuleYes _ _ _ (fun h => hn ((gadget_correct w B).mpr h)) a b hne

/-- The paper's full NO separation, with an attained first minimum between `M+1` and `2M`. -/
theorem gadget_no_minimum_bounds (w : List ℕ) (B : ℕ)
    (hn : (w, B) ∉ Cslib.Complexity.SubsetSum) :
    ∃ r : ℕ, FirstMinimum (gadgetA w B) (gadgetB w B) r ∧
      (gadget w B).M + 1 ≤ r ∧ r ≤ 2 * (gadget w B).M := by
  obtain ⟨r, hr, hu⟩ := gadget_firstMinimum_exists_le_two_M w B
  obtain ⟨a, b, hne, he⟩ := hr.1
  refine ⟨r, hr, ?_, hu⟩
  rw [← he]
  exact gadget_no_gap w B hn a b hne

end Power2ModuleSVPSubsetSum.Reduction

namespace Power2ModuleSVPSubsetSum
open Power2ModuleSVP IdealCVP.Cyclotomic Reduction

/-- Interpret the first stored column of an input. -/
def inputA (x : SVPInput) : Coeff x.1.1 × Coeff x.1.1 :=
  (IdealCVP.ofList x.1.2.1.1, IdealCVP.ofList x.1.2.1.2)

/-- Interpret the second stored column of an input. -/
def inputB (x : SVPInput) : Coeff x.1.1 × Coeff x.1.1 :=
  (IdealCVP.ofList x.1.2.2.1, IdealCVP.ofList x.1.2.2.2)

/-- Every output of the total map satisfies all fixed validity conditions. -/
theorem reduce_wellFormed (x : List ℕ × ℕ) : (reduce x).WellFormed := by
  by_cases hw : positiveWeights x.1 = []
  · by_cases hB : x.2 = 0
    · simpa [reduce, hw, hB] using yesInstance_wellFormed
    · simpa [reduce, hw, hB] using noInstance_wellFormed
  · rw [reduce_of_nonempty x hw]
    exact positiveReduce_wellFormed _ _

/-- Correctness for all lists of natural weights, with multiset semantics and no promises. -/
theorem reduce_correct : ∀ x : List ℕ × ℕ,
    x ∈ Cslib.Complexity.SubsetSum ↔ reduce x ∈ ModuleSVPLang := by
  intro x
  by_cases hw : positiveWeights x.1 = []
  · exact reduce_empty_correct x hw
  · rw [reduce_of_nonempty x hw]
    exact (positiveWeights_subsetSum_iff x.1 x.2).symm.trans
      (positiveReduce_correct _ _)

/-- Every short nonzero output vector has norm exactly the output radius. -/
theorem reduce_short_norm (x : List ℕ × ℕ)
    (a b : Coeff (reduce x).1.1)
    (hne : moduleVector (inputA (reduce x)) (inputB (reduce x)) a b ≠ 0)
    (hshort : pairSup (moduleVector (inputA (reduce x)) (inputB (reduce x)) a b) ≤
      (reduce x).2) :
    pairSup (moduleVector (inputA (reduce x)) (inputB (reduce x)) a b) =
      (reduce x).2 := by
  by_cases hw : positiveWeights x.1 = []
  · by_cases hB : x.2 = 0
    · have hr : (reduce x).2 = 1 := by simp [reduce, hw, hB, yesInstance]
      have hp := one_le_pairSup_of_ne_zero _ hne
      omega
    · have hr : (reduce x).2 = 0 := by simp [reduce, hw, hB, noInstance]
      have hp := one_le_pairSup_of_ne_zero _ hne
      omega
  · revert a b
    rw [reduce_of_nonempty x hw]
    intro a b hne hshort
    obtain ⟨hA, hB⟩ := positiveReduce_interpretation (positiveWeights x.1) x.2
    have hcA : inputA (positiveReduce (positiveWeights x.1) x.2) =
        gadgetA (positiveWeights x.1) x.2 := hA
    have hcB : inputB (positiveReduce (positiveWeights x.1) x.2) =
        gadgetB (positiveWeights x.1) x.2 := hB
    rw [hcA, hcB] at hne hshort ⊢
    exact short_norm_eq_M _ _ a b hne hshort

/-- YES instances have first minimum exactly equal to the stored radius, including constants. -/
theorem reduce_yes_gap (x : List ℕ × ℕ) (hy : x ∈ Cslib.Complexity.SubsetSum) :
    FirstMinimum (inputA (reduce x)) (inputB (reduce x)) (reduce x).2 := by
  have hyes := ((reduce_correct x).mp hy).2
  exact firstMinimum_of_ModuleYes_of_short_eq _ _ _ hyes (reduce_short_norm x)

/-- NO instances have an additive unit gap for every nonzero output vector. -/
theorem reduce_no_gap (x : List ℕ × ℕ) (hn : x ∉ Cslib.Complexity.SubsetSum)
    (a b : Coeff (reduce x).1.1)
    (hne : moduleVector (inputA (reduce x)) (inputB (reduce x)) a b ≠ 0) :
    (reduce x).2 + 1 ≤ pairSup (moduleVector (inputA (reduce x)) (inputB (reduce x)) a b) := by
  apply gap_of_not_ModuleYes _ _ _ _ a b hne
  intro h
  exact hn ((reduce_correct x).mpr ⟨reduce_wellFormed x, h⟩)

end Power2ModuleSVPSubsetSum
