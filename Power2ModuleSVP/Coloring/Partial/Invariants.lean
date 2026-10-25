module

public import Power2ModuleSVP.Coloring.Partial.Walk

/-!
# Cube and frozen-coordinate invariants

Prove cube preservation, frozen-coordinate stability, and small-row invariants for the exact
rational walk. Progress and terminal weight estimates are supplied by Coloring/Trajectory.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

open scoped BigOperators

theorem rationalCube_iff {r : ℕ} (x : Vec r) :
    RationalCube x ↔ ∀ j, |x j| ≤ 1 := by
  constructor <;> intro h j <;> exact_mod_cast h j

theorem stepSize_pos {r : ℕ} (hr : 0 < r) : 0 < stepSize r := by
  unfold stepSize
  positivity

private theorem minFold_bounds (l : List ℚ) (hl : ∀ a ∈ l, 0 ≤ a) :
    0 ≤ l.foldr min 1 ∧ l.foldr min 1 ≤ 1 ∧ ∀ a ∈ l, l.foldr min 1 ≤ a := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih (fun b hb => hl b (by simp [hb]))
    simp only [List.foldr_cons]
    refine ⟨le_min (hl a (by simp)) h₁, (min_le_right _ _).trans h₂, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (h₃ b hb)

theorem capacity_nonneg {r : ℕ} (hr : 0 < r) (x z : Vec r)
    (hx : RationalCube x) (j : Fin r) : 0 ≤ capacity x z j := by
  have hj := abs_le.mp ((rationalCube_iff x).mp hx j)
  unfold capacity
  split_ifs with hp hn
  · exact div_nonneg (by linarith) (mul_pos (stepSize_pos hr) hp).le
  · exact div_nonneg_of_nonpos (by linarith) (mul_neg_of_pos_of_neg (stepSize_pos hr) hn).le
  · norm_num

theorem stepFraction_bounds {r : ℕ} (hr : 0 < r) (x z : Vec r)
    (hx : RationalCube x) :
    0 ≤ stepFraction x z ∧ stepFraction x z ≤ 1 ∧
      ∀ j, stepFraction x z ≤ capacity x z j := by
  obtain ⟨h₁, h₂, h₃⟩ := minFold_bounds ((List.finRange r).map (capacity x z)) (by
    intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    exact capacity_nonneg hr x z hx j)
  exact ⟨h₁, h₂, fun j => h₃ _ (by simp)⟩

theorem cube_step {r : ℕ} (hr : 0 < r) (x z : Vec r)
    (hx : RationalCube x) :
    RationalCube (x + stepSize r • (stepFraction x z • z)) := by
  apply (rationalCube_iff _).mpr
  intro j
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp ((rationalCube_iff x).mp hx j)
  obtain ⟨hα, _, hcap⟩ := stepFraction_bounds hr x z hx
  have hΔ := stepSize_pos hr
  change |x j + stepSize r * (stepFraction x z * z j)| ≤ 1
  apply abs_le.mpr
  unfold capacity at hcap
  by_cases hp : 0 < z j
  · have hc : stepFraction x z * (stepSize r * z j) ≤ 1 - x j := by
      exact (le_div_iff₀ (mul_pos hΔ hp)).mp (by simpa [hp] using hcap j)
    have hstep := mul_nonneg hΔ.le (mul_nonneg hα hp.le)
    constructor <;> nlinarith
  · by_cases hn : z j < 0
    · have hc : -1 - x j ≤ stepFraction x z * (stepSize r * z j) := by
        exact (le_div_iff_of_neg (mul_neg_of_pos_of_neg hΔ hn)).mp
          (by simpa [hp, hn] using hcap j)
      have hstep := mul_nonpos_of_nonneg_of_nonpos hΔ.le
        (mul_nonpos_of_nonneg_of_nonpos hα hn.le)
      constructor <;> nlinarith
    · have hz : z j = 0 := by linarith
      simp only [hz, mul_zero, add_zero]
      exact ⟨hxlo, hxhi⟩

theorem nextState_cube {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r) (s : State r m)
    (hx : RationalCube s.x) : RationalCube (nextState a s).x :=
  cube_step hr s.x (direction a s) hx

theorem walk_cube {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r) (fuel : ℕ)
    (s : State r m) (hx : RationalCube s.x) : RationalCube (walk a fuel s).x := by
  induction fuel generalizing s with
  | zero => exact hx
  | succ fuel ih =>
    simp only [walk]
    split_ifs
    · exact hx
    · exact ih _ (nextState_cube hr a s hx)

theorem walk_fixed {r m : ℕ} (a : Fin m → Row r) (fuel : ℕ) (s : State r m)
    (j : Fin r) (hj : s.x j = -1 ∨ s.x j = 1) : (walk a fuel s).x j = s.x j := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [walk]
    split_ifs
    · rfl
    · have hn := nextState_fixed a s j hj
      rw [ih _ (by simpa only [hn] using hj), hn]

theorem walk_small_row {r m : ℕ} (a : Fin m → Row r) (fuel : ℕ) (s : State r m)
    (i : Fin m) (hi : (a i).threshold ≤ 1) :
    dot (a i).a (walk a fuel s).x = dot (a i).a s.x := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [walk]
    split_ifs
    · rfl
    · rw [ih, nextState_small_row a s i hi]

theorem signCoordinateCount_next_le {r m : ℕ} (a : Fin m → Row r) (s : State r m) :
    signCoordinateCount s.x ≤ signCoordinateCount (nextState a s).x := by
  apply Finset.card_le_card
  intro j hj
  have hj' := (Finset.mem_filter.mp hj).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [nextState_fixed a s j hj']; exact hj'⟩

end Power2ModuleSVP.PartialColoringAlg
