module

public import Power2ModuleSVP.Coloring.Trajectory.Geometry
public import Power2ModuleSVP.Coloring.Trajectory.Initial

/-!
# Potential

Local and accumulated rounded-potential estimates.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

open scoped BigOperators

theorem stepSize_mul_dim {r : ℕ} (hr : 0 < r) : stepSize r * r = 1 / 16 := by
  have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [stepSize]
  field_simp

theorem stepSize_le {r : ℕ} (hr : 0 < r) : stepSize r ≤ 1 / 16 := by
  have hr' : (1 : ℚ) ≤ r := by exact_mod_cast hr
  unfold stepSize
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

theorem damping_bounds {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ)) (i : Fin m) :
    (1 : ℚ) / 2 ≤ damping a i ∧ damping a i ≤ 1 := by
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have hΔ := stepSize_le hr
  have hΔ₀ := (stepSize_pos hr).le
  have hb : 0 ≤ 4 * stepSize r ^ 2 * (a i).threshold ^ 2 / (r : ℚ) := by positivity
  have hb' : 4 * stepSize r ^ 2 * (a i).threshold ^ 2 / (r : ℚ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hr').mpr
    have h := mul_le_mul_of_nonneg_left (hl i) (by positivity : 0 ≤ 4 * stepSize r ^ 2)
    have hs : 16 * stepSize r ^ 2 ≤ 1 / 2 := by nlinarith
    have hsr := mul_le_mul_of_nonneg_right hs hr'.le
    nlinarith
  unfold damping
  constructor <;> linarith

def rowIncrement {r m : ℕ} (a : Fin m → Row r) (s : State r m) (i : Fin m) : ℚ :=
  stepSize r * (a i).threshold *
    dot (a i).a (stepFraction s.x (direction a s) • direction a s)

theorem nextState_weight {r m : ℕ} (a : Fin m → Row r) (s : State r m) (i : Fin m) :
    (nextState a s).w i = roundUp (mesh r m)
      (s.w i * damping a i * (1 + rowIncrement a s i + rowIncrement a s i ^ 2)) := rfl

theorem rowIncrement_abs_le {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (s : State r m) (hx : RationalCube s.x)
    (hhalf : ¬r ≤ 2 * signCoordinateCount s.x) (i : Fin m) : |rowIncrement a s i| ≤ 1 := by
  have hr : 0 < r := by have := hp.dimension; omega
  obtain ⟨hα₀, hα₁, _⟩ := stepFraction_bounds hr s.x (direction a s) hx
  have hz := (direction_norm a x hp s hhalf).2
  have hy : dot (stepFraction s.x (direction a s) • direction a s)
      (stepFraction s.x (direction a s) • direction a s) ≤ 1 := by
    rw [dot_smul_left, dot_smul_right]
    have hs : stepFraction s.x (direction a s) ^ 2 ≤ 1 := by nlinarith
    have h := mul_le_mul hs hz (dot_self_nonneg _) (by norm_num : (0 : ℚ) ≤ 1)
    nlinarith
  have hd := dot_sq_le (a i).a (stepFraction s.x (direction a s) • direction a s)
  have hi : dot (a i).a (stepFraction s.x (direction a s) • direction a s) ^ 2 ≤ 1 := by
    have hmul := mul_le_mul (hp.row_norm_le i) hy
      (dot_self_nonneg _) (by norm_num : (0 : ℚ) ≤ 1)
    nlinarith
  have hΔr := stepSize_mul_dim hr
  have hΔ := stepSize_le hr
  have hΔ₀ := (stepSize_pos hr).le
  have hcoef : stepSize r ^ 2 * (a i).threshold ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (hp.threshold_sq_le i) (sq_nonneg (stepSize r))
    nlinarith
  have ht : rowIncrement a s i ^ 2 ≤ 1 := by
    unfold rowIncrement
    rw [mul_pow, mul_pow]
    have h := mul_le_mul_of_nonneg_left hi
      (mul_nonneg (sq_nonneg (stepSize r)) (sq_nonneg (a i).threshold))
    nlinarith
  exact (sq_le_one_iff_abs_le_one _).mp ht

theorem nextState_weight_nonneg {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ)) (s : State r m)
    (hw : ∀ i, 0 ≤ s.w i) (i : Fin m) : 0 ≤ (nextState a s).w i := by
  rw [nextState_weight]
  have hquad : 0 ≤ 1 + rowIncrement a s i + rowIncrement a s i ^ 2 := by nlinarith
  have hρ : 0 ≤ damping a i := by have := (damping_bounds hr a hl i).1; linarith
  exact (mul_nonneg (mul_nonneg (hw i) hρ) hquad).trans
    (roundUp_bounds (mesh_pos r m) _).1

theorem dot_weighted_rows {r m : ℕ} (c : Fin m → ℚ) (v : Fin m → Vec r) (z : Vec r) :
    dot (fun j => ∑ i, c i * v i j) z = ∑ i, c i * dot (v i) z := by
  simp only [dot, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem rowIncrement_linear_cancel {r m : ℕ} (a : Fin m → Row r) (s : State r m) :
    (∑ i, s.w i * damping a i * rowIncrement a s i) = 0 := by
  have h := direction_orthogonal a s
    (fun j => ∑ i, s.w i * damping a i * (a i).threshold * (a i).a j)
    (by simp [constraints])
  rw [dot_weighted_rows] at h
  calc
    _ = stepSize r * stepFraction s.x (direction a s) *
        (∑ i, s.w i * damping a i * (a i).threshold * dot (a i).a (direction a s)) := by
      simp only [rowIncrement, dot_smul_right, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [h, mul_zero]

theorem rowIncrement_quadratic_bound {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (s : State r m) (hx : RationalCube s.x)
    (hw : ∀ i, 0 ≤ s.w i) (hhalf : ¬r ≤ 2 * signCoordinateCount s.x) :
    (∑ i, s.w i * damping a i * rowIncrement a s i ^ 2) ≤
      ∑ i, s.w i * (1 - damping a i) := by
  have hr : 0 < r := by have := hp.dimension; omega
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  obtain ⟨hα₀, hα₁, _⟩ := stepFraction_bounds hr s.x (direction a s) hx
  have hy : energy (quadraticRows a s)
      (stepFraction s.x (direction a s) • direction a s) ≤
        energy (quadraticRows a s) (direction a s) := by
    rw [energy_smul]
    have hsq : stepFraction s.x (direction a s) ^ 2 ≤ 1 := by nlinarith
    simpa using mul_le_mul_of_nonneg_right hsq
      (quadraticRows_energy_nonneg a s hw _)
  calc
    _ ≤ ∑ i, s.w i * rowIncrement a s i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_left (damping_bounds hr a hp.threshold_sq_le i).2 (hw i)
      simpa using mul_le_mul_of_nonneg_right h (sq_nonneg (rowIncrement a s i))
    _ = stepSize r ^ 2 * energy (quadraticRows a s)
        (stepFraction s.x (direction a s) • direction a s) := by
      rw [energy_quadraticRows, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [rowIncrement]
      ring
    _ ≤ stepSize r ^ 2 * (4 / (r : ℚ) * ∑ i, s.w i * (a i).threshold ^ 2) :=
      mul_le_mul_of_nonneg_left (hy.trans (direction_energy_le a x hp s hw hhalf))
        (sq_nonneg _)
    _ = _ := by
      simp only [damping, sub_sub_cancel, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

def potential {r m : ℕ} (s : State r m) : ℚ := ∑ i, s.w i

theorem nextState_potential {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (s : State r m) (hx : RationalCube s.x)
    (hw : ∀ i, 0 ≤ s.w i) (hhalf : ¬r ≤ 2 * signCoordinateCount s.x) :
    potential (nextState a s) ≤ potential s + m * mesh r m := by
  have hlin := rowIncrement_linear_cancel a s
  have hquad := rowIncrement_quadratic_bound a x hp s hx hw hhalf
  have hid : (∑ i, s.w i * damping a i *
      (1 + rowIncrement a s i + rowIncrement a s i ^ 2)) =
      potential s - (∑ i, s.w i * (1 - damping a i)) +
        (∑ i, s.w i * damping a i * rowIncrement a s i) +
        (∑ i, s.w i * damping a i * rowIncrement a s i ^ 2) := by
    simp only [potential, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hround : potential (nextState a s) ≤ (∑ i, s.w i * damping a i *
      (1 + rowIncrement a s i + rowIncrement a s i ^ 2)) + m * mesh r m := by
    calc
      _ ≤ ∑ i, (s.w i * damping a i *
          (1 + rowIncrement a s i + rowIncrement a s i ^ 2) + mesh r m) := by
        apply Finset.sum_le_sum
        intro i _
        exact (roundUp_bounds (mesh_pos r m) _).2.le
      _ = _ := by simp [Finset.sum_add_distrib]
  rw [hid, hlin] at hround
  linarith

theorem initialState_weights_nonneg {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) (i : Fin m) : 0 ≤ (initialState a x).w i := by
  have hr : 0 < r := by have := hp.dimension; omega
  have h := (initialWeight_enclosure (m := m) hr (a i).threshold (hp.threshold_sq_le i)).1
  have h' : (0 : ℝ) ≤ initialWeight r m (a i).threshold := (Real.exp_pos _).le.trans h
  exact_mod_cast h'

theorem initialState_potential {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hp : WalkPremises a x) :
    (potential (initialState a x) : ℝ) ≤ (r : ℝ) / 32 + m * (mesh r m : ℝ) := by
  have hr : 0 < r := by have := hp.dimension; omega
  calc
    _ ≤ ∑ i, (Real.exp (-((a i).threshold : ℝ) ^ 2 / 16) + (mesh r m : ℝ)) := by
      simp only [potential, Rat.cast_sum]
      apply Finset.sum_le_sum
      intro i _
      have h := (initialWeight_enclosure (m := m) hr (a i).threshold
        (hp.threshold_sq_le i)).2.le
      have he : Real.exp (-((a i).threshold : ℝ) ^ 2) ≤
          Real.exp (-((a i).threshold : ℝ) ^ 2 / 16) := Real.exp_le_exp.mpr (by nlinarith)
      exact h.trans (by linarith)
    _ = coloringEntropy (fun i => (a i).threshold) + m * (mesh r m : ℝ) := by
      simp [coloringEntropy, Finset.sum_add_distrib]
    _ ≤ _ := by linarith [hp.entropy]

end Power2ModuleSVP.PartialColoringAlg
