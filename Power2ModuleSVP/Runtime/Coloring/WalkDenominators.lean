import Power2ModuleSVP.Runtime.Coloring.Weights

/-!
# Walk Denominators

A finite-horizon denominator invariant. The direction premise sees only
the retained rows, a fixed dyadic weight box, and the frozen-coordinate set;
it need not assume entropy or progress.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringNative

open PartialColoringAlg

/-- All numerically relevant state bounds for an entropy-free prefix. -/
def WeightBox {r m : ℕ} (k : ℕ) (s : State r m) : Prop :=
  RationalCube s.x ∧ (∀ i, 0 ≤ s.w i) ∧
    (∀ i, s.w i + 1 ≤ 3 * (4 : ℚ) ^ k) ∧
    ∀ i, (s.w i).den ∣ 2 ^ (precision r m + 1)

theorem weightBox_initial {r m : ℕ} (a : Fin m → Row r) (x : Vec r)
    (hx : RationalCube x) : WeightBox 0 (initialState a x) := by
  refine ⟨hx, fun i => (initialWeight_raw_bounds r m _).1, ?_, ?_⟩
  · intro i
    have h := (initialWeight_raw_bounds r m (a i).threshold).2
    change initialWeight r m (a i).threshold + 1 ≤ 3 * 4 ^ 0
    norm_num
    linarith
  · exact fun i => initialWeight_den r m (a i).threshold

theorem weightBox_next {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ))
    (hn : ∀ i, dot (a i).a (a i).a ≤ 1) {k : ℕ} {s : State r m}
    (hs : WeightBox k s) : WeightBox (k + 1) (nextState a s) := by
  refine ⟨nextState_cube hr a s hs.1, nextState_weight_nonneg hr a hl s hs.2.1, ?_, ?_⟩
  · intro i
    have h := nextState_weight_le_raw hr a hl hn s hs.1 hs.2.1 i
    have hb := mul_le_mul_of_nonneg_left (hs.2.2.1 i) (by norm_num : (0 : ℚ) ≤ 4)
    rw [pow_succ]
    nlinarith
  · intro i
    exact (nextState_weight_den a s i).trans (pow_dvd_pow 2 (by omega))

theorem weightBox_mono {r m k N : ℕ} {s : State r m}
    (hs : WeightBox k s) (hk : k ≤ N) : WeightBox N s := by
  refine ⟨hs.1, hs.2.1, fun i => (hs.2.2.1 i).trans ?_, hs.2.2.2⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 4) hk)
    (by norm_num)

/-- Instantiate the stopped-walk denominator analysis using a fixed weight
box. Unlike a globally preserved fixed magnitude bound, the indexed box
is preserved only while fuel remains, which is exactly what is needed. -/
theorem walk_commonDen_of_weightBox {r m N B : ℕ} (hr : 0 < r)
    (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ))
    (hn : ∀ i, dot (a i).a (a i).a ≤ 1)
    (hdirection : ∀ s : State r m, WeightBox N s →
      ∃ E : ℕ, 0 < E ∧ CommonDen E (direction a s) ∧ E.size ≤ B)
    (fuel k D : ℕ) (hk : k + fuel ≤ N) (hD : 0 < D)
    (s : State r m) (hs : WeightBox k s) (hx : CommonDen D s.x) :
    ∃ D' : ℕ, 0 < D' ∧ CommonDen D' (walk a fuel s).x ∧
      D'.size ≤ D.size + fuel * ((stepSize r).den.size + B) := by
  induction fuel generalizing k D s with
  | zero => exact ⟨D, hD, hx, by simp⟩
  | succ fuel ih =>
    rw [walk]
    split_ifs
    · exact ⟨D, hD, hx, by omega⟩
    · obtain ⟨E, hE, hz, hB⟩ := hdirection s (weightBox_mono hs (by omega))
      obtain ⟨D₁, hD₁, hx₁, hb₁⟩ := cubeStep_commonDen hr hD hE s.x
        (direction a s) hx hz (direction_coordinate_bound a s)
      obtain ⟨D₂, hD₂, hx₂, hb₂⟩ := ih (k + 1) D₁ (by omega) hD₁
        (nextState a s) (weightBox_next hr a hl hn hs) hx₁
      refine ⟨D₂, hD₂, hx₂, ?_⟩
      nlinarith

/-- The concrete cubic-fuel walk needs only a direction-denominator bound
on this explicitly bounded, entropy-free set of rational states. -/
theorem run_commonDen_of_weightBox {r m B D : ℕ} (hr : 0 < r)
    (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ))
    (hn : ∀ i, dot (a i).a (a i).a ≤ 1)
    (hdirection : ∀ s : State r m, WeightBox (stepBudget r) s →
      ∃ E : ℕ, 0 < E ∧ CommonDen E (direction a s) ∧ E.size ≤ B)
    (hD : 0 < D) (x : Vec r) (hx : RationalCube x) (hden : CommonDen D x) :
    ∃ D' : ℕ, 0 < D' ∧ CommonDen D' (run a x).x ∧
      D'.size ≤ D.size + stepBudget r * ((stepSize r).den.size + B) :=
  walk_commonDen_of_weightBox hr a hl hn hdirection (stepBudget r) 0 D
    (by omega) hD (initialState a x) (weightBox_initial a x hx) hden

/-- The denominator invariant controls all coordinate numerators as well. -/
theorem run_coordinate_bits_of_weightBox {r m B D : ℕ} (hr : 0 < r)
    (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ))
    (hn : ∀ i, dot (a i).a (a i).a ≤ 1)
    (hdirection : ∀ s : State r m, WeightBox (stepBudget r) s →
      ∃ E : ℕ, 0 < E ∧ CommonDen E (direction a s) ∧ E.size ≤ B)
    (hD : 0 < D) (x : Vec r) (hx : RationalCube x) (hden : CommonDen D x)
    (j : Fin r) :
    ColoringRuntime.rationalBits ((run a x).x j) ≤
      2 * (D.size + stepBudget r * ((stepSize r).den.size + B)) := by
  obtain ⟨D', hD', hden', hb⟩ := run_commonDen_of_weightBox hr a hl hn hdirection hD x hx hden
  have h := coordinate_bits_le hD' (run a x).x hden' (run_cube hr a x hx) j
  omega

end Power2ModuleSVP.ColoringNative
