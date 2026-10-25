module

public import Power2ModuleSVP.Coloring.Trajectory.Geometry

/-!
# Progress

The walk's consumed-step count and half-coordinate termination. The stronger
count below is also used when accumulating the damping loss.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

open scoped BigOperators

def usedSteps {r m : ℕ} (a : Fin m → Row r) : ℕ → State r m → ℕ
  | 0, _ => 0
  | fuel + 1, s => if r ≤ 2 * signCoordinateCount s.x then 0
      else usedSteps a fuel (nextState a s) + 1

def progressMeasure {r m : ℕ} (s : State r m) : ℚ :=
  dot s.x s.x + stepSize r ^ 2 / 4 * signCoordinateCount s.x

theorem cube_dot_self_le {r : ℕ} (x : Vec r) (hx : RationalCube x) :
    dot x x ≤ r := by
  calc
    _ ≤ ∑ _j : Fin r, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro j _
      obtain ⟨h₁, h₂⟩ := abs_le.mp ((rationalCube_iff _).mp hx j)
      nlinarith
    _ = _ := by simp

theorem signCoordinateCount_le {r : ℕ} (x : Vec r) : signCoordinateCount x ≤ r := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem progressMeasure_nonneg {r m : ℕ} (s : State r m) : 0 ≤ progressMeasure s := by
  exact add_nonneg (dot_self_nonneg _) (mul_nonneg (by positivity) (by positivity))

theorem progressMeasure_le {r m : ℕ} (s : State r m) (hx : RationalCube s.x) :
    progressMeasure s ≤ (r : ℚ) + stepSize r ^ 2 / 4 * r := by
  have hc : (signCoordinateCount s.x : ℚ) ≤ r := by exact_mod_cast signCoordinateCount_le s.x
  exact add_le_add (cube_dot_self_le _ hx)
    (mul_le_mul_of_nonneg_left hc (by positivity))

theorem nextState_progress {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (s : State r m) (hx : RationalCube s.x)
    (hhalf : ¬r ≤ 2 * signCoordinateCount s.x) :
    progressMeasure s + stepSize r ^ 2 / 4 ≤ progressMeasure (nextState a s) := by
  have hr : 0 < r := by have := hp.dimension; omega
  have hm := nextState_norm_mono hr a s hx
  have hc : (signCoordinateCount s.x : ℚ) ≤ signCoordinateCount (nextState a s).x := by
    exact_mod_cast signCoordinateCount_next_le a s
  have hδ : 0 ≤ stepSize r ^ 2 / 4 := by positivity
  unfold progressMeasure
  by_cases hf : stepFraction s.x (direction a s) = 1
  · have he := full_step_norm_progress a x hp s hhalf hf
    have := mul_le_mul_of_nonneg_left hc hδ
    linarith
  · have htr : stepFraction s.x (direction a s) < 1 :=
      lt_of_le_of_ne (stepFraction_bounds hr s.x _ hx).2.1 hf
    have hcount : (signCoordinateCount s.x : ℚ) + 1 ≤
        signCoordinateCount (nextState a s).x := by
      exact_mod_cast truncated_step_count a s htr
    have := mul_le_mul_of_nonneg_left hcount hδ
    linarith

theorem usedSteps_le {r m : ℕ} (a : Fin m → Row r) (fuel : ℕ) (s : State r m) :
    usedSteps a fuel s ≤ fuel := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [usedSteps]
    split_ifs
    · omega
    · exact Nat.add_le_add_right (ih _) 1

theorem usedSteps_eq_or_half {r m : ℕ} (a : Fin m → Row r) (fuel : ℕ) (s : State r m) :
    usedSteps a fuel s = fuel ∨ r ≤ 2 * signCoordinateCount (walk a fuel s).x := by
  induction fuel generalizing s with
  | zero => exact Or.inl rfl
  | succ fuel ih =>
    simp only [usedSteps, walk]
    split_ifs with hhalf
    · exact Or.inr hhalf
    · rcases ih (nextState a s) with he | hh
      · exact Or.inl (by omega)
      · exact Or.inr hh

theorem walk_progress {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (fuel : ℕ) (s : State r m) (hx : RationalCube s.x) :
    progressMeasure s + (usedSteps a fuel s : ℚ) * (stepSize r ^ 2 / 4) ≤
      progressMeasure (walk a fuel s) := by
  have hr : 0 < r := by have := hp.dimension; omega
  induction fuel generalizing s with
  | zero => simp [walk, usedSteps]
  | succ fuel ih =>
    simp only [walk, usedSteps]
    split_ifs with hhalf
    · simp
    · have hi := ih (nextState a s) (nextState_cube hr a s hx)
      have hn := nextState_progress a x hp s hx hhalf
      push_cast
      linarith

theorem walk_step_count_bound {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (fuel : ℕ) (s : State r m) (hx : RationalCube s.x) :
    (usedSteps a fuel s : ℚ) * (stepSize r ^ 2 / 4) ≤
      (r : ℚ) + stepSize r ^ 2 / 4 * r := by
  have hr : 0 < r := by have := hp.dimension; omega
  have h := (walk_progress a x hp fuel s hx).trans
    (progressMeasure_le _ (walk_cube hr a fuel s hx))
  linarith [progressMeasure_nonneg s]

theorem run_terminal_half {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) : r ≤ 2 * signCoordinateCount (run a x).x := by
  have hr : 0 < r := by have := hp.dimension; omega
  rcases usedSteps_eq_or_half a (stepBudget r) (initialState a x) with hfull | hhalf
  · have h := walk_step_count_bound a x hp (stepBudget r) (initialState a x) hp.cube
    rw [hfull] at h
    have hr' : (0 : ℚ) < r := by exact_mod_cast hr
    have hr₁ : (1 : ℚ) ≤ r := by exact_mod_cast hr
    have hΔ : stepSize r = 1 / (16 * (r : ℚ)) := rfl
    rw [hΔ, stepBudget] at h
    push_cast at h
    field_simp at h
    nlinarith [sq_pos_of_pos hr', pow_pos hr' 3]
  · exact hhalf

end Power2ModuleSVP.PartialColoringAlg
