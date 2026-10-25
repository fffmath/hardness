module

public import Power2ModuleSVP.Coloring.Trajectory.Potential
public import Power2ModuleSVP.Coloring.Trajectory.Progress

/-!
# Lower

Accumulation of exponential lower weights with the consumed-step bound.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

open scoped BigOperators

/-- The real loss subtracted from one in a row damping factor. -/
noncomputable def dampingLoss {r m : ℕ} (a : Fin m → Row r) (i : Fin m) : ℝ :=
  4 * (stepSize r : ℝ) ^ 2 * ((a i).threshold : ℝ) ^ 2 / r

theorem damping_cast {r m : ℕ} (a : Fin m → Row r) (i : Fin m) :
    (damping a i : ℝ) = 1 - dampingLoss a i := by
  simp [damping, dampingLoss]

theorem dampingLoss_bounds {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ)) (i : Fin m) :
    0 ≤ dampingLoss a i ∧ dampingLoss a i ≤ 1 / 2 := by
  have h := damping_bounds hr a hl i
  have hlo : (1 : ℝ) / 2 ≤ (damping a i : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr h.1
  have hhi : (damping a i : ℝ) ≤ 1 := by exact_mod_cast h.2
  rw [damping_cast] at hlo hhi
  constructor <;> linarith

theorem rowIncrement_displacement {r m : ℕ} (a : Fin m → Row r) (s : State r m)
    (i : Fin m) : rowIncrement a s i =
      (a i).threshold * dot (a i).a ((nextState a s).x - s.x) := by
  simp only [rowIncrement, nextState, dot_sub_right, dot_add_right, dot_smul_right]
  ring

theorem nextState_weight_lower {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (s : State r m) (hx : RationalCube s.x)
    (hw : ∀ i, 0 ≤ s.w i) (hhalf : ¬r ≤ 2 * signCoordinateCount s.x) (i : Fin m) :
    (s.w i : ℝ) * Real.exp ((rowIncrement a s i : ℝ) - 2 * dampingLoss a i) ≤
      ((nextState a s).w i : ℝ) := by
  have hr : 0 < r := by have := hp.dimension; omega
  have ht : |(rowIncrement a s i : ℝ)| ≤ 1 := by
    exact_mod_cast rowIncrement_abs_le a x hp s hx hhalf i
  have hβ := dampingLoss_bounds hr a hp.threshold_sq_le i
  have hρ : 0 ≤ (damping a i : ℝ) := by
    rw [damping_cast]
    linarith [hβ.2]
  have he := coloring_damping_ge_exp hβ.1 hβ.2
  rw [← damping_cast] at he
  have hq := coloring_quadratic_ge_exp ht
  have hprod := mul_le_mul he hq (Real.exp_nonneg _) hρ
  have hsw : (0 : ℝ) ≤ s.w i := by exact_mod_cast hw i
  have hmul := mul_le_mul_of_nonneg_left hprod hsw
  have hround : ((s.w i * damping a i *
      (1 + rowIncrement a s i + rowIncrement a s i ^ 2) : ℚ) : ℝ) ≤
      ((nextState a s).w i : ℝ) := by
    rw [nextState_weight]
    exact (Rat.cast_le (K := ℝ)).mpr (roundUp_bounds (mesh_pos r m)
      (s.w i * damping a i * (1 + rowIncrement a s i + rowIncrement a s i ^ 2))).1
  push_cast at hround
  rw [← Real.exp_add] at hmul
  have hexp : -2 * dampingLoss a i + (rowIncrement a s i : ℝ) =
      (rowIncrement a s i : ℝ) - 2 * dampingLoss a i := by ring
  rw [hexp] at hmul
  nlinarith

theorem walk_weight_lower {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (fuel : ℕ) (s : State r m) (hx : RationalCube s.x)
    (hw : ∀ i, 0 ≤ s.w i) (i : Fin m) :
    (s.w i : ℝ) * Real.exp (
      ((a i).threshold : ℝ) * (dot (a i).a ((walk a fuel s).x - s.x) : ℝ) -
      2 * dampingLoss a i * usedSteps a fuel s) ≤ ((walk a fuel s).w i : ℝ) := by
  have hr : 0 < r := by have := hp.dimension; omega
  induction fuel generalizing s with
  | zero => simp [walk, usedSteps]
  | succ fuel ih =>
    simp only [walk, usedSteps]
    split_ifs with hhalf
    · simp
    · have hi := ih (nextState a s) (nextState_cube hr a s hx)
        (nextState_weight_nonneg hr a hp.threshold_sq_le s hw)
      have hn := nextState_weight_lower a x hp s hx hw hhalf i
      let E := ((a i).threshold : ℝ) *
        (dot (a i).a ((walk a fuel (nextState a s)).x - (nextState a s).x) : ℝ) -
          2 * dampingLoss a i * usedSteps a fuel (nextState a s)
      have hid : (a i).threshold * dot (a i).a
          ((walk a fuel (nextState a s)).x - s.x) =
          (a i).threshold * dot (a i).a
            ((walk a fuel (nextState a s)).x - (nextState a s).x) + rowIncrement a s i := by
        rw [rowIncrement_displacement]
        simp only [dot_sub_right]
        ring
      have he : ((a i).threshold : ℝ) *
          (dot (a i).a ((walk a fuel (nextState a s)).x - s.x) : ℝ) -
          2 * dampingLoss a i * (usedSteps a fuel (nextState a s) + 1 : ℕ) =
          ((rowIncrement a s i : ℝ) - 2 * dampingLoss a i) + E := by
        have hid' := congrArg (fun q : ℚ => (q : ℝ)) hid
        push_cast at hid' ⊢
        dsimp only [E]
        linarith
      rw [he, Real.exp_add, ← mul_assoc]
      exact (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg E)).trans hi

theorem run_damping_loss {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (i : Fin m) :
    2 * dampingLoss a i * usedSteps a (stepBudget r) (initialState a x) ≤
      (32 + 8 * (stepSize r : ℝ) ^ 2) * ((a i).threshold : ℝ) ^ 2 := by
  have hr : 0 < r := by have := hp.dimension; omega
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h := walk_step_count_bound a x hp (stepBudget r) (initialState a x) hp.cube
  have h' : (usedSteps a (stepBudget r) (initialState a x) : ℝ) *
      ((stepSize r : ℝ) ^ 2 / 4) ≤ (r : ℝ) + (stepSize r : ℝ) ^ 2 / 4 * r := by
    exact_mod_cast h
  have hmul := mul_le_mul_of_nonneg_left h'
    (by positivity : 0 ≤ 32 * ((a i).threshold : ℝ) ^ 2 / (r : ℝ))
  unfold dampingLoss
  calc
    _ = (32 * ((a i).threshold : ℝ) ^ 2 / (r : ℝ)) *
        ((usedSteps a (stepBudget r) (initialState a x) : ℝ) *
          ((stepSize r : ℝ) ^ 2 / 4)) := by ring
    _ ≤ _ := hmul
    _ = _ := by field_simp; ring

theorem run_terminal_weight_lower {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (i : Fin m) :
    Real.exp ((a i).threshold * (dot (a i).a ((run a x).x - x) : ℝ) -
      (33 + 8 * (stepSize r : ℝ) ^ 2) * ((a i).threshold : ℝ) ^ 2) ≤ ((run a x).w i : ℝ) := by
  have hr : 0 < r := by have := hp.dimension; omega
  have hinit := (initialWeight_enclosure (m := m) hr (a i).threshold
    (hp.threshold_sq_le i)).1
  have hwalk := walk_weight_lower a x hp (stepBudget r) (initialState a x) hp.cube
    (initialState_weights_nonneg a x hp) i
  have hloss := run_damping_loss a x hp i
  let E := ((a i).threshold : ℝ) * (dot (a i).a ((run a x).x - x) : ℝ) -
    2 * dampingLoss a i * usedSteps a (stepBudget r) (initialState a x)
  calc
    _ ≤ Real.exp (-((a i).threshold : ℝ) ^ 2 + E) := by
      apply Real.exp_le_exp.mpr
      dsimp only [E]
      nlinarith
    _ = Real.exp (-((a i).threshold : ℝ) ^ 2) * Real.exp E := Real.exp_add _ _
    _ ≤ (initialWeight r m (a i).threshold : ℝ) * Real.exp E :=
      mul_le_mul_of_nonneg_right hinit (Real.exp_nonneg _)
    _ ≤ _ := hwalk

end Power2ModuleSVP.PartialColoringAlg
