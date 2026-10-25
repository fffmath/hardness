import Power2ModuleSVP.Seed.Family
import Power2ModuleSVP.Anchor.FromSeed

/-!
# Unconditional NP-completeness in power-of-two cyclotomic rings

Prove NP-completeness of the coefficient unit-cube principal-coset problem and unit-threshold
rank-two module SVP over ℤ[X]/(X^d + 1) for dyadic d. The module proof uses the certified
spectral seed family and deterministic rigid-anchor repair.

Paper: `paper/power2svp.pdf`, Sections 1.1 and 3–5 (Theorem 1 and the composed reductions).
-/

namespace Power2ModuleSVP
open Turing.MultiTapeTM Cslib.Complexity

/-- The principal-coset decision language is NP-hard. -/
theorem coset_npHard : NPHard encCoset CosetLang :=
  ThreeSAT_npHard.trans threeSAT_polyTimeReducible_coset

/-- The principal-coset decision language is NP-complete. -/
theorem coset_npComplete : NPComplete encCoset CosetLang :=
  ⟨coset_mem_NP, coset_npHard⟩

/-- Unit-threshold rank-two module SVP is NP-complete. -/
theorem moduleSVP_npComplete : NPComplete encSVP ModuleSVPLang :=
  moduleSVP_npComplete_of_seed spectralSeedFamily_holds

end Power2ModuleSVP
