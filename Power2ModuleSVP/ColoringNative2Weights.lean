import Power2ModuleSVP.ColoringNative
import Power2ModuleSVP.ColoringTrajectoryPotential

/-! Entropy-free magnitude and bit bounds for the concrete rounded walk. -/
namespace Power2ModuleSVP.ColoringNative

open PartialColoringAlg
open scoped BigOperators
set_option maxHeartbeats 800000

/-- Direction normalization needs no progress or entropy assumption. -/
theorem direction_norm_le {r m : ℕ} (a : Fin m → Row r) (s : State r m) :
    dot (direction a s) (direction a s) ≤ 1 := by
  have h := normalize_dot_self_le
    (bestColumn (quadraticRows a s) (cachedColumns (constraints a s)))
  unfold direction orient
  split_ifs
  · exact h
  · simpa [dot] using h

/-- The local increment bound holds even when the entropy budget fails. -/
theorem rowIncrement_abs_le_raw {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ))
    (hn : ∀ i, dot (a i).a (a i).a ≤ 1)
    (s : State r m) (hx : RationalCube s.x) (i : Fin m) :
    |rowIncrement a s i| ≤ 1 := by
  obtain ⟨hα₀, hα₁, _⟩ := stepFraction_bounds hr s.x (direction a s) hx
  have hz := direction_norm_le a s
  have hy : dot (stepFraction s.x (direction a s) • direction a s)
      (stepFraction s.x (direction a s) • direction a s) ≤ 1 := by
    rw [dot_smul_left, dot_smul_right]
    have hs : stepFraction s.x (direction a s) ^ 2 ≤ 1 := by nlinarith
    have h := mul_le_mul hs hz (dot_self_nonneg _) (by norm_num : (0 : ℚ) ≤ 1)
    nlinarith
  have hd := dot_sq_le (a i).a (stepFraction s.x (direction a s) • direction a s)
  have hi : dot (a i).a (stepFraction s.x (direction a s) • direction a s) ^ 2 ≤ 1 := by
    have h := mul_le_mul (hn i) hy (dot_self_nonneg _) (by norm_num : (0 : ℚ) ≤ 1)
    nlinarith
  have hΔr := stepSize_mul_dim hr
  have hΔ := stepSize_le hr
  have hΔ₀ := (stepSize_pos hr).le
  have hcoef : stepSize r ^ 2 * (a i).threshold ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (hl i) (sq_nonneg (stepSize r))
    nlinarith
  apply (sq_le_one_iff_abs_le_one _).mp
  unfold rowIncrement
  rw [mul_pow, mul_pow]
  have h := mul_le_mul_of_nonneg_left hi
    (mul_nonneg (sq_nonneg (stepSize r)) (sq_nonneg (a i).threshold))
  nlinarith

theorem mesh_le_one (r m : ℕ) : mesh r m ≤ 1 := by
  unfold mesh
  apply (div_le_one (by positivity : (0 : ℚ) < 2 ^ precision r m)).mpr
  exact one_le_pow₀ (by norm_num)

/-- A deliberately coarse bound: each step multiplies weight-plus-one by
at most four. Its bit cost is linear in the number of steps. -/
theorem nextState_weight_le_raw {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ))
    (hn : ∀ i, dot (a i).a (a i).a ≤ 1)
    (s : State r m) (hx : RationalCube s.x) (hw : ∀ i, 0 ≤ s.w i) (i : Fin m) :
    (nextState a s).w i + 1 ≤ 4 * (s.w i + 1) := by
  have ht := rowIncrement_abs_le_raw hr a hl hn s hx i
  have ht' := abs_le.mp ht
  have hsq : rowIncrement a s i ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr ht
  have hquad : 0 ≤ 1 + rowIncrement a s i + rowIncrement a s i ^ 2 := by nlinarith
  have hquad' : 1 + rowIncrement a s i + rowIncrement a s i ^ 2 ≤ 3 := by linarith
  have hρ := damping_bounds hr a hl i
  have hmul := mul_le_mul_of_nonneg_left hρ.2 (hw i)
  have h := mul_le_mul hmul hquad' hquad (by simpa using hw i)
  have hround := (roundUp_bounds (mesh_pos r m)
    (s.w i * damping a i * (1 + rowIncrement a s i + rowIncrement a s i ^ 2))).2.le
  rw [← nextState_weight] at hround
  have hm := mesh_le_one r m
  nlinarith [hw i]

/-- Uniform magnitude growth for every prefix, without entropy or a
half-coloring progress theorem. -/
theorem walk_weight_le_raw {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ))
    (hn : ∀ i, dot (a i).a (a i).a ≤ 1)
    (fuel : ℕ) (s : State r m) (hx : RationalCube s.x) (hw : ∀ i, 0 ≤ s.w i) :
    (∀ i, 0 ≤ (walk a fuel s).w i) ∧
    ∀ i, (walk a fuel s).w i + 1 ≤ 4 ^ fuel * (s.w i + 1) := by
  induction fuel generalizing s with
  | zero => exact ⟨hw, by simp [walk]⟩
  | succ fuel ih =>
    rw [walk]
    split_ifs
    · refine ⟨hw, fun i => ?_⟩
      have hp : (1 : ℚ) ≤ 4 ^ (fuel + 1) := one_le_pow₀ (by norm_num)
      nlinarith [hw i]
    · have hw' := nextState_weight_nonneg hr a hl s hw
      obtain ⟨h₀, h₁⟩ := ih (nextState a s) (nextState_cube hr a s hx) hw'
      refine ⟨h₀, fun i => ?_⟩
      have hb := mul_le_mul_of_nonneg_left
        (nextState_weight_le_raw hr a hl hn s hx hw i) (by positivity : (0 : ℚ) ≤ 4 ^ fuel)
      rw [pow_succ]
      nlinarith [h₁ i]

/-- Initialization is bounded on every threshold, with no entropy premise. -/
theorem initialWeight_raw_bounds (r m : ℕ) (lam : ℚ) :
    0 ≤ initialWeight r m lam ∧ initialWeight r m lam ≤ 2 := by
  have hL : 0 < max (32 * r) (precision r m + 4) := by omega
  have hS : (1 : ℚ) ≤ expSum (lam ^ 2) (max (32 * r) (precision r m + 4)) := by
    exact_mod_cast expSum_one_le (sq_nonneg lam) hL
  have hi : 0 ≤ (expSum (lam ^ 2) (max (32 * r) (precision r m + 4)))⁻¹ :=
    inv_nonneg.mpr (by linarith)
  have hi' : (expSum (lam ^ 2) (max (32 * r) (precision r m + 4)))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hS
  have hb := roundUp_bounds (half_pos (mesh_pos r m))
    ((expSum (lam ^ 2) (max (32 * r) (precision r m + 4)))⁻¹)
  change 0 ≤ roundUp _ _ ∧ roundUp _ _ ≤ 2
  constructor
  · linarith [hb.1]
  · linarith [hb.2, mesh_le_one r m]

/-- Every actual run weight has at most exponential magnitude in cubic
fuel; hence this magnitude contributes only polynomially many binary bits. -/
theorem run_weight_le_raw {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ))
    (hn : ∀ i, dot (a i).a (a i).a ≤ 1) (x : Vec r) (hx : RationalCube x)
    (i : Fin m) :
    0 ≤ (run a x).w i ∧ (run a x).w i ≤ 4 ^ (stepBudget r + 1) := by
  have hw : ∀ i, 0 ≤ (initialState a x).w i := fun i => (initialWeight_raw_bounds r m _).1
  obtain ⟨h₀, h₁⟩ := walk_weight_le_raw hr a hl hn (stepBudget r) (initialState a x) hx hw
  refine ⟨h₀ i, ?_⟩
  have hi := (initialWeight_raw_bounds r m (a i).threshold).2
  have hb := mul_le_mul_of_nonneg_left (show (initialState a x).w i + 1 ≤ 3 by
    change initialWeight r m (a i).threshold + 1 ≤ 3; linarith)
    (by positivity : (0 : ℚ) ≤ 4 ^ stepBudget r)
  change (walk a (stepBudget r) (initialState a x)).w i ≤ _
  rw [pow_succ]
  nlinarith [h₁ i, pow_nonneg (by norm_num : (0 : ℚ) ≤ 4) (stepBudget r)]

/-- The same bound applies at every fuel prefix of initialization. -/
theorem walk_initial_weight_le_raw {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ))
    (hn : ∀ i, dot (a i).a (a i).a ≤ 1) (x : Vec r) (hx : RationalCube x)
    (fuel : ℕ) (i : Fin m) :
    0 ≤ (walk a fuel (initialState a x)).w i ∧
      (walk a fuel (initialState a x)).w i ≤ 4 ^ (fuel + 1) := by
  have hw : ∀ i, 0 ≤ (initialState a x).w i := fun i => (initialWeight_raw_bounds r m _).1
  obtain ⟨h₀, h₁⟩ := walk_weight_le_raw hr a hl hn fuel (initialState a x) hx hw
  refine ⟨h₀ i, ?_⟩
  have hi := (initialWeight_raw_bounds r m (a i).threshold).2
  have hb := mul_le_mul_of_nonneg_left (show (initialState a x).w i + 1 ≤ 3 by
    change initialWeight r m (a i).threshold + 1 ≤ 3; linarith)
    (by positivity : (0 : ℚ) ≤ 4 ^ fuel)
  rw [pow_succ]
  nlinarith [h₁ i, pow_nonneg (by norm_num : (0 : ℚ) ≤ 4) fuel]

/-- Canonical numerator growth is controlled by magnitude and denominator
bits, without manipulating unreduced intermediate fractions. -/
theorem numerator_bits_le_of_nonneg_le_pow {q : ℚ} (hq : 0 ≤ q) {k : ℕ}
    (hk : q ≤ (4 : ℚ) ^ k) :
    q.num.natAbs.size ≤ 2 * k + 1 + q.den.size := by
  have hn : (q.num.natAbs : ℚ) ≤ (4 : ℚ) ^ k * q.den := by
    have hnum : (q.num : ℚ) = q * q.den :=
      (div_eq_iff (by exact_mod_cast q.den_ne_zero)).mp q.num_div_den
    have hpos : 0 ≤ q.num := Rat.num_nonneg.mpr hq
    have he : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
      have he' : (q.num.natAbs : ℤ) = q.num :=
        (Int.natCast_natAbs q.num).trans (abs_of_nonneg hpos)
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) he'
    rw [he, hnum]
    exact mul_le_mul_of_nonneg_right hk (by positivity)
  have hn' : q.num.natAbs ≤ 4 ^ k * q.den := by exact_mod_cast hn
  have hs := (Nat.size_le_size hn').trans (Nat.size_mul_le (4 ^ k) q.den)
  have hp : (4 ^ k : ℕ).size = 2 * k + 1 := by
    have he : (4 ^ k : ℕ) = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
    rw [he, Nat.size_pow]
  omega

/-- Polynomial bit bounds hold at every prefix, not only at termination. -/
theorem walk_initial_weight_bits_le_raw {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ))
    (hn : ∀ i, dot (a i).a (a i).a ≤ 1) (x : Vec r) (hx : RationalCube x)
    (fuel : ℕ) (i : Fin m) :
    ColoringRuntime.rationalBits ((walk a fuel (initialState a x)).w i) ≤
      2 * (fuel + 1) + 1 + 2 * (precision r m + 2) := by
  obtain ⟨h₀, h₁⟩ := walk_initial_weight_le_raw hr a hl hn x hx fuel i
  have hnum := numerator_bits_le_of_nonneg_le_pow h₀ h₁
  have hdiv := walk_weight_den a fuel (initialState a x)
    (fun i => initialWeight_den r m (a i).threshold) i
  have hd := Nat.le_of_dvd (by positivity : 0 < 2 ^ (precision r m + 1)) hdiv
  have hden : ((walk a fuel (initialState a x)).w i).den.size ≤ precision r m + 2 := by
    have hs := Nat.size_le_size hd
    rw [Nat.size_pow] at hs
    exact hs
  unfold ColoringRuntime.rationalBits
  omega

/-- Specialization to the actual retained signed rows; no entropy premise
is needed on the original matrix or thresholds. -/
theorem prepared_walk_weight_bits_le_raw {r m : ℕ} (hr : 0 < r)
    (V : Fin m → Vec r) (c : Fin m → ℚ) (hc : ∀ i, 0 ≤ c i)
    (x : Vec r) (hx : RationalCube x) (fuel : ℕ)
    (i : Fin (prepareRows V c).length) :
    ColoringRuntime.rationalBits
      ((walk (prepareRows V c).get fuel (initialState (prepareRows V c).get x)).w i) ≤
        2 * (fuel + 1) + 1 + 2 * (precision r (prepareRows V c).length + 2) := by
  have hp (j : Fin (prepareRows V c).length) :=
    prepareRows_row_properties V c hc ((prepareRows V c).get j) (List.get_mem _ _)
  exact walk_initial_weight_bits_le_raw hr (prepareRows V c).get
    (fun j => (hp j).2.1) (fun j => (hp j).2.2) x hx fuel i

/-- Explicit polynomial bit bound for every terminal weight on raw valid
walk data. Neither entropy nor the semantic trajectory hypothesis occurs. -/
theorem run_weight_bits_le_raw {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ))
    (hn : ∀ i, dot (a i).a (a i).a ≤ 1) (x : Vec r) (hx : RationalCube x)
    (i : Fin m) :
    ColoringRuntime.rationalBits ((run a x).w i) ≤
      2 * (stepBudget r + 1) + 1 + 2 * (precision r m + 2) := by
  obtain ⟨h₀, h₁⟩ := run_weight_le_raw hr a hl hn x hx i
  have hnum := numerator_bits_le_of_nonneg_le_pow h₀ h₁
  have hden := run_weight_den_size a x i
  unfold ColoringRuntime.rationalBits
  omega

end Power2ModuleSVP.ColoringNative
