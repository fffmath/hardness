import Power2ModuleSVPSubsetSum.Reduction.Construction

/-!
# Boolean coefficient encoding

The first assertion of Lemma 4.1, including uniqueness of the Boolean word.
This part is independent of the filter and of all scale parameters.

Paper: `paper/power2svp-subsetsum.pdf`, Lemma 4.1.
-/

namespace Power2ModuleSVPSubsetSum.Reduction
open Power2ModuleSVP

/-- The Boolean word as coefficients, with zeros outside the weight positions. -/
def booleanWord {n s : ℕ} (_hs : s ≤ n) (ξ : Fin s → Bool) : Coeff n :=
  fun i => if hi : i.val < s then if ξ ⟨i.val, hi⟩ then 1 else 0 else 0

/-- The coefficient version of the executable mask array. -/
theorem ofList_mask (n s : ℕ) :
    IdealCVP.ofList (d := n) (mask n s) = fun i => if i.val < s then 1 else 0 := by
  ext i
  simp [IdealCVP.ofList, mask, List.getD_eq_getElem?_getD, i.isLt]

/-- An integer is Boolean exactly when its centered double has absolute value at most one. -/
theorem abs_double_sub_one_le (a : ℤ) : |2 * a - 1| ≤ 1 ↔ a = 0 ∨ a = 1 := by
  rw [abs_le]
  omega

/-- Off the mask, the unit bound forces an even coefficient to vanish. -/
theorem abs_double_le (a : ℤ) : |2 * a| ≤ 1 ↔ a = 0 := by
  rw [abs_le]
  omega

/-- The unit-cube constraint is equivalent to Boolean coefficients on the mask. -/
theorem boolean_cube_iff {n s : ℕ} (a : Coeff n) :
    Cube ((2 : ℤ) • a - IdealCVP.ofList (mask n s)) ↔
      ∀ i : Fin n, if i.val < s then a i = 0 ∨ a i = 1 else a i = 0 := by
  rw [ofList_mask]
  constructor
  · intro h i
    have hi := h i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
    by_cases his : i.val < s
    · simp only [his, ↓reduceIte] at hi ⊢
      exact (abs_double_sub_one_le (a i)).mp hi
    · simp only [his, ↓reduceIte, sub_zero] at hi ⊢
      exact (abs_double_le (a i)).mp hi
  · intro h i
    have hi := h i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases his : i.val < s
    · simp only [his, ↓reduceIte] at hi ⊢
      exact (abs_double_sub_one_le (a i)).mpr hi
    · simp only [his, ↓reduceIte, sub_zero] at hi ⊢
      exact (abs_double_le (a i)).mpr hi

/-- Distinct Boolean words have distinct coefficient arrays. -/
theorem booleanWord_injective {n s : ℕ} (hs : s ≤ n) :
    Function.Injective (booleanWord hs) := by
  intro ξ η h
  funext i
  have hi := congrFun h ⟨i.val, lt_of_lt_of_le i.isLt hs⟩
  simp only [booleanWord, dite_eq_left i.isLt] at hi
  cases hξ : ξ i <;> cases hη : η i <;> simp_all

/-- Lemma 4.1's Boolean encoding, with the unique word explicitly exhibited. -/
theorem boolean_encoding {n s : ℕ} (hs : s ≤ n) (a : Coeff n) :
    coeffSup ((2 : ℤ) • a - IdealCVP.ofList (mask n s)) ≤ 1 ↔
      ∃! ξ : Fin s → Bool, a = booleanWord hs ξ := by
  rw [← cube_iff_coeffSup_le, boolean_cube_iff]
  constructor
  · intro h
    let ξ : Fin s → Bool := fun j => decide (a ⟨j.val, lt_of_lt_of_le j.isLt hs⟩ = 1)
    have ha : a = booleanWord hs ξ := by
      ext i
      have hi := h i
      by_cases his : i.val < s
      · simp only [his, ↓reduceIte] at hi
        rcases hi with hi | hi
        · simp [booleanWord, his, ξ, hi]
        · simp [booleanWord, his, ξ, hi]
      · simpa [booleanWord, his] using hi
    refine ⟨ξ, ha, ?_⟩
    intro η hη
    exact booleanWord_injective hs (hη.symm.trans ha)
  · rintro ⟨ξ, rfl, _⟩ i
    by_cases his : i.val < s
    · simp only [his, ↓reduceIte, booleanWord]
      cases ξ ⟨i.val, his⟩ <;> simp
    · simp [his, booleanWord]

end Power2ModuleSVPSubsetSum.Reduction
