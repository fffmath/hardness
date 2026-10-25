import Power2ModuleSVP.MainAssembly
import Power2ModuleSVP.ColoringNative3

/-!
# Unconditional NP-completeness of unit-threshold module SVP over `Z[X]/(X^d+1)`

Unit-threshold SVP in the coefficient sup norm for rank-2 modules over
`R_d = Z[X]/(X^d+1)`, `d` a power of two, is NP-complete (and so is the principal
coset version, `coset_npComplete` in `Main.lean`).
-/

namespace Power2ModuleSVP
open Turing.MultiTapeTM Cslib.Complexity

theorem moduleSVP_npComplete : NPComplete encSVP ModuleSVPLang :=
  moduleSVP_npComplete_of_fullColoringNative ColoringRuntime.fullColoringNative_partialColor

end Power2ModuleSVP
