module

public import Power2ModuleSVP.Coloring.Trajectory.Lower
public import Power2ModuleSVP.Coloring.Trajectory.Upper

/-!
# Correctness of the rational coloring trajectory

Assemble progress and terminal-weight estimates for the concrete rational walk, proving semantic
correctness of partial and full coloring. Runtime/Coloring/Certificate.lean supplies the native
machine certificate.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

/-- Discharge all three estimates for the original rational walk. -/
theorem partialColoringTrajectory : PartialColoringTrajectoryHypothesis where
  terminal_half _r _m a x hp := run_terminal_half a x hp
  terminal_weight_upper _r _m a x hp := run_terminal_weight_upper a x hp
  terminal_weight_lower _r _m a x hp := run_terminal_weight_lower a x hp

/-- The implemented partial-coloring program fixes at least half the
coordinates and has discrepancy at most `68 * threshold * rowNorm`. -/
theorem partialColor_correct : PartialColoringCorrect partialColor :=
  partialColor_correct_of_trajectory partialColoringTrajectory

/-- Only the native-machine certificate remains to package the concrete
algorithm with its semantics. -/
theorem deterministicPartialColoring_of_native (hN : PartialColoringNativeHypothesis) :
    DeterministicPartialColoringHypothesis :=
  deterministicPartialColoring_of_trajectory_and_native partialColoringTrajectory hN

/-- Unconditional semantics of the full-coloring recursion instantiated with
the concrete partial program. -/
theorem fullColor_partialColor_spec
    (r m : ℕ) (V : Fin m → Vec r) (x : Vec r) (c : Fin m → ℚ)
    (hx : RationalCube x) (hc : ∀ i, 0 ≤ c i)
    (he : coloringEntropy c ≤ (r : ℝ) / 64) :
    ∃ y : Vec r, fullColor partialColor (partialColoringInput V x c) = List.ofFn y ∧
      FullColoringSpec V x y c :=
  fullColor_partialColor_spec_of_trajectory partialColoringTrajectory r m V x c hx hc he

end Power2ModuleSVP.PartialColoringAlg
