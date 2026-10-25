import Power2ModuleSVP.Runtime.Coloring.Recursion.Correct

/-!
# Static

Static data invariants across the actual recursive-input orbit.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open Turing.MultiTapeTM
open Coloring
set_option maxHeartbeats 600000

abbrev recursionInput (F : PartialColoringInput → List ℚ) (p : PartialColoringInput)
    (i : ℕ) : PartialColoringInput := ((descentStep F)^[i] (p, [])).1

 theorem descentStep_eq (F : PartialColoringInput → List ℚ) (s : RecursionStack) :
    descentStep F s = if recursionProgress F s.1 then
      (recursionNext F s.1, s.1 :: s.2) else s := rfl

 theorem descent_dimension_le (F : PartialColoringInput → List ℚ) (p : PartialColoringInput)
    (i : ℕ) : (recursionInput F p i).2.1.length ≤ p.2.1.length := by
  have hs (s : RecursionStack) : (descentStep F s).1.2.1.length ≤ s.1.2.1.length := by
    rw [descentStep_eq]
    split_ifs with h
    · exact (recursionNext_dimension_lt F s.1 h).le
    · exact le_rfl
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [recursionInput, Function.iterate_succ_apply']
    exact (hs _).trans ih

 theorem descent_matrix_length (F : PartialColoringInput → List ℚ) (p : PartialColoringInput)
    (i : ℕ) : (recursionInput F p i).1.length = p.1.length := by
  have hs (s : RecursionStack) : (descentStep F s).1.1.length = s.1.1.length := by
    rw [descentStep_eq]
    split_ifs <;> simp [recursionNext]
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [recursionInput, Function.iterate_succ_apply']
    exact (hs _).trans ih

theorem getD_mem_or_zero (l : List ℚ) (j : ℕ) : l.getD j 0 ∈ l ∨ l.getD j 0 = 0 := by
  by_cases hj : j < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hj]
  · right
    simp [List.getD_eq_getElem?_getD, Nat.not_lt.mp hj]

 theorem descent_matrix_entries (F : PartialColoringInput → List ℚ) (p : PartialColoringInput)
    (i : ℕ) : ∀ row ∈ (recursionInput F p i).1, ∀ q ∈ row,
      q = 0 ∨ ∃ original ∈ p.1, q ∈ original := by
  have hs (s : RecursionStack)
      (h : ∀ row ∈ s.1.1, ∀ q ∈ row, q = 0 ∨ ∃ original ∈ p.1, q ∈ original) :
      ∀ row ∈ (descentStep F s).1.1, ∀ q ∈ row,
        q = 0 ∨ ∃ original ∈ p.1, q ∈ original := by
    rw [descentStep_eq]
    split_ifs
    · intro row hrow q hq
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrow
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
      rcases getD_mem_or_zero old j with hm | hz
      · exact h old hold _ hm
      · exact Or.inl hz
    · exact h
  induction i with
  | zero => exact fun row hr q hq => Or.inr ⟨row, hr, hq⟩
  | succ i ih =>
    rw [recursionInput, Function.iterate_succ_apply']
    exact hs _ ih

 theorem descent_matrix_row_length (F : PartialColoringInput → List ℚ) (p : PartialColoringInput)
    (N : ℕ) (hr : p.2.1.length ≤ N) (hrow : ∀ row ∈ p.1, row.length ≤ N)
    (i : ℕ) : ∀ row ∈ (recursionInput F p i).1, row.length ≤ N := by
  induction i with
  | zero => exact hrow
  | succ i ih =>
    rw [recursionInput, Function.iterate_succ_apply']
    rw [descentStep_eq]
    split_ifs
    · intro row hmem
      obtain ⟨old, _, rfl⟩ := List.mem_map.mp hmem
      simp only [restrictList_length]
      exact (ExplicitRecursion.activeIndices_length_le _ _).trans
        ((descent_dimension_le F p i).trans hr)
    · exact ih

 theorem descent_threshold_coordinate (F : PartialColoringInput → List ℚ)
    (p : PartialColoringInput) (i j : ℕ) (hj : j < p.1.length) :
    (recursionInput F p i).2.2.getD j 0 =
      p.2.2.getD j 0 + 4 * (((descentStep F)^[i] (p, [])).2.length : ℚ) := by
  induction i with
  | zero => simp [recursionInput]
  | succ i ih =>
    rw [recursionInput, Function.iterate_succ_apply']
    have hm := descent_matrix_length F p i
    rw [descentStep_eq]
    split_ifs
    · have hj' : j < (recursionInput F p i).1.length := by rw [hm]; exact hj
      simp only [recursionNext, List.length_cons, Nat.cast_add, Nat.cast_one]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hj', Option.map_some, Option.getD_some]
      change (recursionInput F p i).2.2.getD j 0 + 4 = _
      rw [ih]
      simp only [List.getD_eq_getElem?_getD]
      ring
    · exact ih

/-- Every threshold keeps its original canonical denominator. -/
 theorem descent_threshold_den (F : PartialColoringInput → List ℚ)
    (p : PartialColoringInput) (i j : ℕ) (hj : j < p.1.length) :
    ((recursionInput F p i).2.2.getD j 0).den = (p.2.2.getD j 0).den := by
  rw [descent_threshold_coordinate F p i j hj]
  have he : (4 : ℚ) * (((descentStep F)^[i] (p, [])).2.length : ℚ) =
      ((4 * (((descentStep F)^[i] (p, [])).2.length : ℤ) : ℤ) : ℚ) := by push_cast; rfl
  rw [he, Rat.add_intCast_den]

end Power2ModuleSVP.ColoringRuntime

namespace Power2ModuleSVP.ColoringRuntime
open Turing.MultiTapeTM
set_option maxHeartbeats 600000

 theorem descent_threshold_entries (F : PartialColoringInput → List ℚ)
    (p : PartialColoringInput) (i : ℕ) :
    ∀ q ∈ (recursionInput F p i).2.2, ∃ original : ℚ,
      (original ∈ p.2.2 ∨ original = 0) ∧ ∃ k ≤ i, q = original + 4 * (k : ℚ) := by
  induction i with
  | zero => exact fun q hq => ⟨q, Or.inl hq, 0, by omega, by simp⟩
  | succ i ih =>
    rw [recursionInput, Function.iterate_succ_apply']
    rw [descentStep_eq]
    split_ifs
    · intro q hq
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
      rcases getD_mem_or_zero (recursionInput F p i).2.2 j with hm | hz
      · obtain ⟨original, ho, k, hk, he⟩ := ih _ hm
        refine ⟨original, ho, k + 1, by omega, ?_⟩
        rw [he]
        push_cast
        ring
      · refine ⟨0, Or.inr rfl, 1, by omega, ?_⟩
        rw [hz]
        norm_num
    · intro q hq
      obtain ⟨original, ho, k, hk, he⟩ := ih q hq
      exact ⟨original, ho, k, by omega, he⟩

 theorem descent_threshold_length (F : PartialColoringInput → List ℚ)
    (p : PartialColoringInput) (i : ℕ) :
    (recursionInput F p i).2.2.length ≤ max p.2.2.length p.1.length := by
  induction i with
  | zero => exact Nat.le_max_left _ _
  | succ i ih =>
    rw [recursionInput, Function.iterate_succ_apply']
    rw [descentStep_eq]
    split_ifs
    · simp only [recursionNext, List.length_map, List.length_range]
      rw [descent_matrix_length F p i]
      exact Nat.le_max_right _ _
    · exact ih

end Power2ModuleSVP.ColoringRuntime
