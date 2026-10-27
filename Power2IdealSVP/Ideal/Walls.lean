import Power2IdealSVP.Ideal.Parity

/-!
# Full signs and odd alternating walls

The local `OddAlternating` predicate uses prefix sums: for an initial sign `η = ±1`,
all prefix sums are either `0` or `η` and the total is `η`. This is an intrinsic
characterization of odd alternating support, independent of `Spin/Defs.lean`.
Theorems below establish the sign bijection and the ternary, odd-support and
successive-sign properties needed to identify this predicate with the spin interface.

Paper: `paper/power2-ideal-svp.pdf`, Section 1.5; audit Section 11.
-/

namespace Power2IdealSVP.Ideal
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- A local prefix-sum characterization of an odd alternating integer support. -/
def OddAlternating {n : ℕ} (σ : Coeff n) : Prop :=
  ∃ η : ℤ, (η = -1 ∨ η = 1) ∧ (∑ i, σ i) = η ∧
    ∀ k ≤ n, prefixSum σ k = 0 ∨ prefixSum σ k = η

/-- Convolution by `S` bijects odd alternating supports with full signs. -/
theorem oddAlternating_iff_signs_sumPoly {n : ℕ} (hn : 0 < n) (σ : Coeff n) :
    OddAlternating σ ↔ Signs (mul (sumPoly n) σ) := by
  constructor
  · rintro ⟨η, hη, ht, hp⟩ i
    rw [sumPoly_mul_apply hn, ht]
    rcases hp (i.val + 1) (by omega) with hi | hi <;>
      rcases hη with hη | hη <;> simp [hi, hη]
  · intro hs
    let j : Fin n := ⟨n - 1, by omega⟩
    have hj : j.val + 1 = n := by dsimp [j]; omega
    have ht : (∑ i, σ i) = -1 ∨ (∑ i, σ i) = 1 := by
      have h := hs j
      rw [sumPoly_mul_apply hn, hj, prefixSum_all] at h
      simpa only [two_mul, add_sub_cancel_right] using h
    refine ⟨∑ i, σ i, ht, rfl, ?_⟩
    intro k hk
    by_cases h0 : k = 0
    · simp [h0]
    · let i : Fin n := ⟨k - 1, by omega⟩
      have hi : i.val + 1 = k := by dsimp [i]; omega
      have h := hs i
      rw [sumPoly_mul_apply hn, hi] at h
      rcases ht with ht | ht <;> rcases h with h | h <;> omega

/-- Odd alternating spins have coefficients in `{-1,0,1}`. -/
theorem OddAlternating.ternary {n : ℕ} {σ : Coeff n} (hσ : OddAlternating σ)
    (i : Fin n) : σ i = -1 ∨ σ i = 0 ∨ σ i = 1 := by
  obtain ⟨η, hη, _, hp⟩ := hσ
  have h0 := hp i.val (by omega)
  have h1 := hp (i.val + 1) (by omega)
  have he := prefixSum_succ σ i
  rcases hη with hη | hη <;> rcases h0 with h0 | h0 <;>
    rcases h1 with h1 | h1 <;> omega

/-- Odd alternating support is nonempty. -/
theorem OddAlternating.ne_zero {n : ℕ} {σ : Coeff n} (hσ : OddAlternating σ) :
    σ ≠ 0 := by
  rintro rfl
  obtain ⟨η, hη, ht, _⟩ := hσ
  simp only [Pi.zero_apply, Finset.sum_const_zero] at ht
  rcases hη with hη | hη <;> omega

/-- The wall spin of a full sign: zero at a nonwall and the new sign at a wall. -/
def wallSpin {n : ℕ} (hn : 0 < n) (s : Coeff n) : Coeff n :=
  fun i => if s i = shift hn s i then 0 else s i

/-- The signed predecessor of a full sign is again a sign. -/
theorem signs_shift {n : ℕ} (hn : 0 < n) {s : Coeff n} (hs : Signs s) :
    Signs (shift hn s) := by
  intro i
  simp only [shift]
  split_ifs
  · rcases hs ⟨n - 1, by omega⟩ with h | h <;> simp [h]
  · exact hs _

/-- The difference of a full sign is exactly twice its wall spin. -/
theorem difference_signs {n : ℕ} (hn : 0 < n) {s : Coeff n} (hs : Signs s) :
    mul (difference hn) s = (2 : ℤ) • wallSpin hn s := by
  rw [difference_mul]
  funext i
  have hpred := signs_shift hn hs i
  rcases hs i with hi | hi <;> rcases hpred with hj | hj <;>
    simp [wallSpin, hi, hj]

/-- Integrating the walls recovers the original full sign. -/
theorem sumPoly_wallSpin {n : ℕ} (hn : 0 < n) {s : Coeff n} (hs : Signs s) :
    mul (sumPoly n) (wallSpin hn s) = s := by
  have h := sumPoly_mul_difference hn s
  rw [difference_signs hn hs, mul_smul_right] at h
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  omega

/-- Walls always form an odd alternating spin. -/
theorem oddAlternating_wallSpin {n : ℕ} (hn : 0 < n) {s : Coeff n}
    (hs : Signs s) : OddAlternating (wallSpin hn s) := by
  rw [oddAlternating_iff_signs_sumPoly hn, sumPoly_wallSpin hn hs]
  exact hs

/-- Taking walls after integrating an odd alternating spin recovers the spin. -/
theorem wallSpin_sumPoly {n : ℕ} (hn : 0 < n) {σ : Coeff n}
    (hσ : OddAlternating σ) : wallSpin hn (mul (sumPoly n) σ) = σ := by
  apply sumPoly_mul_injective hn
  exact sumPoly_wallSpin hn ((oddAlternating_iff_signs_sumPoly hn σ).mp hσ)

/-- At active wall positions the sparse and full signs agree. -/
theorem wallSpin_active {n : ℕ} (hn : 0 < n) (s : Coeff n) (i : Fin n)
    (hi : wallSpin hn s i ≠ 0) : wallSpin hn s i = s i := by
  dsimp [wallSpin] at hi ⊢
  split_ifs <;> simp_all

/-- Each odd alternating spin is the wall array of exactly one full sign. -/
theorem oddAlternating_iff_existsUnique_sign {n : ℕ} (hn : 0 < n) (σ : Coeff n) :
    OddAlternating σ ↔ ∃! s : Coeff n, Signs s ∧ wallSpin hn s = σ := by
  constructor
  · intro hσ
    refine ⟨mul (sumPoly n) σ,
      ⟨(oddAlternating_iff_signs_sumPoly hn σ).mp hσ, wallSpin_sumPoly hn hσ⟩, ?_⟩
    intro s hs
    rw [← hs.2, sumPoly_wallSpin hn hs.1]
  · rintro ⟨s, ⟨hs, rfl⟩, _⟩
    exact oddAlternating_wallSpin hn hs

end Power2IdealSVP.Ideal
