import Power2ModuleSVP.Runtime.Coloring.Direction
import Power2ModuleSVP.Runtime.Coloring.WalkDenominators

/-!
# Coordinate encoding bounds for the coloring walk

Reified direction data depend only on weights and fixed-coordinate flags. A local canonical-
projector denominator bound controls the coordinate encodings of the stopped walk; that local
bound is proved in Runtime/Coloring/Gram/Identification.lean.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime

open PartialColoringAlg ColoringNative
open Turing.MultiTapeTM
set_option maxHeartbeats 400000

/-- Reified direction data do not read unfrozen rational point values. -/
theorem walkDirectionInput_eq_of_weights_and_fixed {r m : ℕ} (a : Fin m → Row r)
    (s t : State r m) (hw : s.w = t.w)
    (hf : ∀ j, (s.x j = -1 ∨ s.x j = 1) ↔ (t.x j = -1 ∨ t.x j = 1)) :
    walkDirectionInput a s = walkDirectionInput a t := by
  have hc := constraints_eq_of_weights_and_fixed a s t hw hf
  simp only [walkDirectionInput, hc, quadraticRows, hw]

/-- A single bound on the reified constraint data over the explicit weight
box instantiates the direction premise for the actual stopped walk. The
constants are uniform over dimensions, rows and starting points. -/
theorem run_coordinate_bits_of_projector
    (h : CanonicalProjectorDenominatorHypothesis) :
    ∃ c d : ℕ, ∀ (r m L D : ℕ) (_hr : 0 < r) (a : Fin m → Row r),
      (∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ)) →
      (∀ i, dot (a i).a (a i).a ≤ 1) →
      (∀ s : State r m, WeightBox (stepBudget r) s →
        (encDirectionInput (walkDirectionInput a s)).length ≤ L) →
      0 < D → ∀ x : Vec r, RationalCube x → CommonDen D x →
      ∀ j : Fin r, rationalBits ((run a x).x j) ≤
        2 * (D.size + stepBudget r * ((stepSize r).den.size + c * (L + 1) ^ d)) := by
  obtain ⟨c, d, hdir⟩ := walk_direction_commonDen_of_projector h
  refine ⟨c, d, fun r m L D hr a hl hn hdata hD x hx hden j => ?_⟩
  apply run_coordinate_bits_of_weightBox hr a hl hn ?_ hD x hx hden j
  intro s hs
  obtain ⟨E, hE, hz, hb⟩ := hdir r m a s
  refine ⟨E, hE, hz, hb.trans ?_⟩
  have hL := hdata s hs
  exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega :
    (encDirectionInput (walkDirectionInput a s)).length + 1 ≤ L + 1) d)

end Power2ModuleSVP.ColoringRuntime
