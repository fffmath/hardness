import Power2ModuleSVP.ColoringNative2Direction
import Power2ModuleSVP.ColoringNative2Walk

/-!
Native coloring components, second pass.

Unconditional results include entropy-free weight numerator/denominator
bounds at every prefix, exact native column selection, and a finite-horizon
coordinate denominator invariant. The complete cached projector and
normalized-direction certificates require only the local algebraic
`CanonicalProjectorDenominatorHypothesis`.

The two whole-coloring native hypotheses are not proved here. Outstanding
work includes proving that algebraic hypothesis, bounding the reified
constraint data uniformly on the weight box, certifying preparation and
heavy-row sorting, composing the stopped list walk, and certifying full
recursion with uniform intermediate encodings. These obligations are not
hidden in an alleged unconditional machine theorem.
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
