import Power2ModuleSVP.ColoringNative3Box

/-! Direction and coordinate bounds depending only on fixed row data. -/
namespace Power2ModuleSVP.ColoringRuntime
open PartialColoringAlg ColoringNative
open Turing.MultiTapeTM
set_option maxHeartbeats 600000

theorem walk_direction_commonDen_uniform
    (h : CanonicalProjectorDenominatorHypothesis) :
    ∃ c d : ℕ, ∀ (r m : ℕ) (a : Fin m → Row r) (s : State r m),
      WeightBox (stepBudget r) s →
      ∃ E : ℕ, 0 < E ∧ CommonDen E (direction a s) ∧
        E.size ≤ c * ((encWalkParameter (walkParameter a)).length + 1) ^ d := by
  obtain ⟨c₁, d₁, hb₁⟩ := walkDirectionInput_uniform_encoding
  obtain ⟨c₂, d₂, hb₂⟩ := walk_direction_commonDen_of_projector h
  have hp : PolyBounded (fun p : WalkParameter => (encWalkParameter p).length)
      (fun p => c₂ * (c₁ * ((encWalkParameter p).length + 1) ^ d₁ + 1) ^ d₂) := by
    exact ⟨fun n => c₂ * (c₁ * (n + 1) ^ d₁ + 1) ^ d₂, by fun_prop, fun _ => le_rfl⟩
  obtain ⟨c, d, hb⟩ := hp.exists_le
  refine ⟨c, d, fun r m a s hs => ?_⟩
  obtain ⟨E, hE, hden, he⟩ := hb₂ r m a s
  refine ⟨E, hE, hden, he.trans ?_⟩
  exact (Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (hb₁ r m a s hs) 1) d₂)).trans (hb _)

/-- Every prefix has additive common-denominator growth, with a uniform
polynomial contribution independent of the initial point's denominator. -/
theorem walk_initial_commonDen_uniform
    (h : CanonicalProjectorDenominatorHypothesis) :
    ∃ c d : ℕ, ∀ (r m D fuel : ℕ) (_hr : 0 < r) (a : Fin m → Row r),
      (∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ)) →
      (∀ i, dot (a i).a (a i).a ≤ 1) →
      fuel ≤ stepBudget r → 0 < D → ∀ x : Vec r, RationalCube x → CommonDen D x →
      ∃ D' : ℕ, 0 < D' ∧ CommonDen D' (walk a fuel (initialState a x)).x ∧
        D'.size ≤ D.size + fuel * ((stepSize r).den.size +
          c * ((encWalkParameter (walkParameter a)).length + 1) ^ d) := by
  obtain ⟨c, d, hb⟩ := walk_direction_commonDen_uniform h
  refine ⟨c, d, fun r m D fuel hr a hl hn hf hD x hx hden => ?_⟩
  exact walk_commonDen_of_weightBox hr a hl hn (fun s hs => hb r m a s hs)
    fuel 0 D (by omega) hD (initialState a x) (weightBox_initial a x hx) hden

/-- Numerator and denominator bits of every coordinate at every prefix. -/
theorem walk_initial_coordinate_bits_uniform
    (h : CanonicalProjectorDenominatorHypothesis) :
    ∃ c d : ℕ, ∀ (r m D fuel : ℕ) (_hr : 0 < r) (a : Fin m → Row r),
      (∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ)) →
      (∀ i, dot (a i).a (a i).a ≤ 1) →
      fuel ≤ stepBudget r → 0 < D → ∀ x : Vec r, RationalCube x → CommonDen D x →
      ∀ j : Fin r, rationalBits ((walk a fuel (initialState a x)).x j) ≤
        2 * (D.size + fuel * ((stepSize r).den.size +
          c * ((encWalkParameter (walkParameter a)).length + 1) ^ d)) := by
  obtain ⟨c, d, hb⟩ := walk_initial_commonDen_uniform h
  refine ⟨c, d, fun r m D fuel hr a hl hn hf hD x hx hden j => ?_⟩
  obtain ⟨D', hD', hd, hsize⟩ := hb r m D fuel hr a hl hn hf hD x hx hden
  have hcube := walk_cube hr a fuel (initialState a x) hx
  exact (coordinate_bits_le hD' _ hd hcube j).trans (by omega)

end Power2ModuleSVP.ColoringRuntime
