import Complexity.Computability.Complexity.Problems.SubsetSum

/-! # Total source normalization

Remove zero weights before applying the positive-weight gadget. This preserves the source's
sub-multiset semantics, including repeated weights and the empty subset.

Paper: `paper/power2svp-subsetsum.pdf`, Section 4.1; `AUDIT_A.md`, edge cases.
-/

namespace Power2ModuleSVPSubsetSum

/-- Discard exactly the zero weights; the program only traverses the input list. -/
def positiveWeights (weights : List ℕ) : List ℕ := weights.filter (· != 0)

/-- Every retained weight is strictly positive. -/
theorem positiveWeights_pos (weights : List ℕ) :
    ∀ w ∈ positiveWeights weights, 0 < w := by
  intro w hw
  have hw' := (List.mem_filter.mp hw).2
  simp only [bne_iff_ne] at hw'
  omega

/-- Removing zero entries preserves the sum. -/
theorem sum_positiveWeights (weights : List ℕ) :
    (positiveWeights weights).sum = weights.sum := by
  simp [positiveWeights]

/-- Zero removal preserves Subset Sum, with no positivity or nonemptiness assumption. -/
theorem positiveWeights_subsetSum_iff (weights : List ℕ) (target : ℕ) :
    (positiveWeights weights, target) ∈ Cslib.Complexity.SubsetSum ↔
      (weights, target) ∈ Cslib.Complexity.SubsetSum := by
  rw [Cslib.Complexity.mem_SubsetSum_iff_sublist,
    Cslib.Complexity.mem_SubsetSum_iff_sublist]
  constructor
  · rintro ⟨s, hs, hsum⟩
    exact ⟨s, hs.trans List.filter_sublist, hsum⟩
  · rintro ⟨s, hs, hsum⟩
    exact ⟨positiveWeights s, hs.filter _, (sum_positiveWeights s).trans hsum⟩

/-- An empty source list has a solution precisely at target zero. -/
@[simp] theorem nil_subsetSum_iff (target : ℕ) :
    (([], target) : List ℕ × ℕ) ∈ Cslib.Complexity.SubsetSum ↔ target = 0 := by
  rw [Cslib.Complexity.mem_SubsetSum_iff_sublist]
  simp [eq_comm]

/-- If normalization empties the list, the only possible target is zero. -/
theorem subsetSum_iff_of_positiveWeights_eq_nil (weights : List ℕ) (target : ℕ)
    (h : positiveWeights weights = []) :
    (weights, target) ∈ Cslib.Complexity.SubsetSum ↔ target = 0 := by
  rw [← positiveWeights_subsetSum_iff, h, nil_subsetSum_iff]

/-- A position-indexed Boolean witness preserves multiplicities of equal weights. -/
theorem subsetSum_iff_bool (weights : List ℕ) (target : ℕ) :
    (weights, target) ∈ Cslib.Complexity.SubsetSum ↔
      ∃ ξ : Fin weights.length → Bool,
        ∑ j : Fin weights.length, weights.get j * (if ξ j then 1 else 0) = target := by
  classical
  have h := Cslib.Complexity.map_mem_SubsetSum_iff
    (List.nodup_finRange weights.length) weights.get target
  simp only [List.map_get_finRange] at h
  rw [h]
  constructor
  · rintro ⟨F, _, hsum⟩
    refine ⟨fun i => decide (i ∈ F), ?_⟩
    simpa only [decide_eq_true_eq, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_mem, Finset.univ_inter] using hsum
  · rintro ⟨ξ, hsum⟩
    refine ⟨Finset.univ.filter (fun i => ξ i = true), ?_, ?_⟩
    · intro i _
      simp
    · simpa only [Finset.sum_filter, mul_ite, mul_one, mul_zero] using hsum

end Power2ModuleSVPSubsetSum
