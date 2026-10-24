import IdealCVP.Lattice

/-! # Integral rounding gap

The coefficient argument in Case 2 of Lemma `lem:admissible`, scaled by four
so that no fractions or real numbers occur. A noncanonical pair of integral
blocks has 4Φ≥ω+4.
-/
namespace IdealCVP

/-- Coordinate characterization of a Boolean encoding under a bit mask u. -/
def Rounded {ι : Type*} (u a b : ι → ℤ) : Prop :=
  b = 0 ∧ ∀ i, (u i = 0 → a i = 0) ∧ (u i = 1 → a i = 0 ∨ a i = 1)

theorem rounding_coordinate (u a : ℤ) (hu : u = 0 ∨ u = 1) :
    u ≤ (2 * a - u)^2 := by
  rcases hu with rfl | rfl
  · nlinarith [sq_nonneg (2 * a)]
  · have : a ≤ 0 ∨ 1 ≤ a := by omega
    rcases this with ha | ha <;> nlinarith

theorem rounding_coordinate_gap (u a : ℤ) (hu : u = 0 ∨ u = 1)
    (ha : ¬ ((u = 0 → a = 0) ∧ (u = 1 → a = 0 ∨ a = 1))) :
    u + 4 ≤ (2 * a - u)^2 := by
  rcases hu with rfl | rfl
  · have h : a ≤ -1 ∨ 1 ≤ a := by simp only [true_implies, zero_ne_one,
        false_implies, and_true, not_and] at ha; omega
    rcases h with h | h <;> nlinarith
  · have h : a ≤ -1 ∨ 2 ≤ a := by simp only [one_ne_zero, false_implies,
        true_implies, true_and] at ha; omega
    rcases h with h | h <;> nlinarith

/-- The discrete gap underlying the forbidden-multiplier argument. -/
theorem rounding_gap {ι : Type*} [Fintype ι] (u a b : ι → ℤ)
    (hu : ∀ i, u i = 0 ∨ u i = 1) (hbad : ¬ Rounded u a b) :
    (∑ i, u i) + 4 ≤ sqNorm (fun i => 2 * a i - u i) + 4 * sqNorm b := by
  classical
  have hnonneg (i : ι) : 0 ≤ (2 * a i - u i)^2 - u i := by
    have := rounding_coordinate (u i) (a i) (hu i); omega
  have hsum : (∑ i, u i) ≤ sqNorm (fun i => 2 * a i - u i) := by
    exact Finset.sum_le_sum (fun i _ => rounding_coordinate _ _ (hu i))
  by_cases hb : b = 0
  · have hbad' : ¬ ∀ i, (u i = 0 → a i = 0) ∧ (u i = 1 → a i = 0 ∨ a i = 1) := by
      intro hh; exact hbad ⟨hb, hh⟩
    obtain ⟨i, hi⟩ := not_forall.mp hbad'
    have hg := rounding_coordinate_gap _ _ (hu i) hi
    have hs := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
    rw [Finset.sum_sub_distrib] at hs
    change (2 * a i - u i)^2 - u i ≤
      sqNorm (fun i => 2 * a i - u i) - ∑ i, u i at hs
    have := sqNorm_nonneg b
    omega
  · have := sqNorm_pos hb
    omega

end IdealCVP
