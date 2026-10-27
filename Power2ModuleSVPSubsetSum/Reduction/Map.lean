import Power2ModuleSVPSubsetSum.Reduction.Source
import Power2ModuleSVPSubsetSum.Reduction.Constants
import Power2ModuleSVPSubsetSum.Reduction.Construction

/-!
# Total executable reduction

The reduction first removes zero weights. If no weights remain, it returns the
fixed YES or NO instance according to whether the target is zero. Otherwise it
computes the explicit coefficient-list gadget (4.1)–(4.3).

Paper: `paper/power2svp-subsetsum.pdf`, Section 4.1; `AUDIT_A.md`, edge cases.
-/

namespace Power2ModuleSVPSubsetSum
open Power2ModuleSVP (Dyadic)

/-- Total list program from complexitylib's binary Subset Sum source to module SVP.
Only the output degree is unary. All coefficients and the radius use binary arithmetic. -/
def reduce (x : List ℕ × ℕ) : SVPInput :=
  let w := positiveWeights x.1
  if w = [] then
    if x.2 = 0 then yesInstance else noInstance
  else Reduction.positiveReduce w x.2

/-- For a nonempty normalized list, the total map is precisely the paper's gadget. -/
theorem reduce_of_nonempty (x : List ℕ × ℕ) (h : positiveWeights x.1 ≠ []) :
    reduce x = Reduction.positiveReduce (positiveWeights x.1) x.2 := by
  simp [reduce, h]

/-- Correctness on all sources whose weights vanish after normalization. -/
theorem reduce_empty_correct (x : List ℕ × ℕ) (h : positiveWeights x.1 = []) :
    x ∈ Cslib.Complexity.SubsetSum ↔ reduce x ∈ ModuleSVPLang := by
  rw [subsetSum_iff_of_positiveWeights_eq_nil x.1 x.2 h]
  by_cases hB : x.2 = 0
  · simp [reduce, h, hB, yesInstance_mem]
  · simp [reduce, h, hB, noInstance_not_mem]

/-- The total map always stores a dyadic degree and exact-length generator arrays. -/
theorem reduce_shape (x : List ℕ × ℕ) :
    Dyadic (reduce x).1.1 ∧
      (reduce x).1.2.1.1.length = (reduce x).1.1 ∧
      (reduce x).1.2.1.2.length = (reduce x).1.1 ∧
      (reduce x).1.2.2.1.length = (reduce x).1.1 ∧
      (reduce x).1.2.2.2.length = (reduce x).1.1 := by
  by_cases hw : positiveWeights x.1 = []
  · by_cases hB : x.2 = 0
    · simp only [reduce, hw, ↓reduceIte, hB]
      have h := yesInstance_wellFormed
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
    · simp only [reduce, hw, ↓reduceIte, hB]
      have h := noInstance_wellFormed
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  · rw [reduce_of_nonempty x hw]
    exact ⟨Reduction.positiveReduce_dyadic _ _,
      Reduction.positiveReduce_lengths _ _⟩

end Power2ModuleSVPSubsetSum
