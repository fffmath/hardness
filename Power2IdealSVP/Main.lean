import Power2IdealSVP.Glue.Correctness
import Power2IdealSVP.Runtime.PolyTime
import Power2IdealSVP.Membership.NP

/-!
# NP-completeness of power-of-two principal ideal SVP

The total coefficient-list reduction from CLIQUE, its unconditional correctness,
and the binary-radius verifier establish NP-completeness in the coefficient infinity norm.

Paper: `paper/power2-ideal-svp.pdf`, Theorem 1 and equations (1)–(3).
-/

namespace Power2IdealSVP

open Turing.MultiTapeTM Cslib.Complexity

/-- CLIQUE reduces in polynomial time to principal ideal coefficient infinity-norm SVP. -/
theorem clique_polyTimeReducible_idealSVP :
    PolyTimeReducible (encPair encGraph encNat) encIdeal
      Cslib.Complexity.Clique IdealSVPLang :=
  ⟨Runtime.reduceList, Runtime.reduceList_polytime, reduceList_correct⟩

/-- Principal ideal coefficient infinity-norm SVP in dyadic degree is NP-hard. -/
theorem idealSVP_npHard : NPHard encIdeal IdealSVPLang :=
  Cslib.Complexity.Clique_npHard.trans clique_polyTimeReducible_idealSVP

/-- Principal ideal coefficient infinity-norm SVP in dyadic degree is NP-complete. -/
theorem idealSVP_npComplete : NPComplete encIdeal IdealSVPLang :=
  ⟨idealSVP_mem_NP, idealSVP_npHard⟩

end Power2IdealSVP
