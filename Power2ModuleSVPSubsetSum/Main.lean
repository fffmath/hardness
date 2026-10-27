import Power2ModuleSVPSubsetSum.Runtime.Reduction
import Power2ModuleSVPSubsetSum.Reduction.Correctness
import Power2ModuleSVPSubsetSum.Membership.NP

/-!
# NP-completeness of arbitrary-radius power-of-two module SVP

The native polynomial-time coefficient-list reduction from binary Subset Sum,
its mathematical correctness, and the binary-radius verifier establish
NP-completeness of the coefficient maximum-norm rank-two module problem.

Paper: `paper/power2svp-subsetsum.pdf`, Theorem 1.1 and Section 4.
-/

namespace Power2ModuleSVPSubsetSum
open Turing.MultiTapeTM Cslib.Complexity

/-- Binary Subset Sum reduces in polynomial time to arbitrary-radius module SVP. -/
theorem subsetSum_polyTimeReducible_moduleSVP :
    PolyTimeReducible (encPair (encList encNat) encNat) encSVP
      Cslib.Complexity.SubsetSum ModuleSVPLang :=
  ⟨reduce, reduce_polytime, reduce_correct⟩

/-- Coefficient maximum-norm rank-two module SVP over dyadic rings is NP-hard. -/
theorem moduleSVP_npHard : NPHard encSVP ModuleSVPLang :=
  Cslib.Complexity.SubsetSum_npHard.trans subsetSum_polyTimeReducible_moduleSVP

/-- Coefficient maximum-norm rank-two module SVP over dyadic rings is NP-complete. -/
theorem moduleSVP_npComplete : NPComplete encSVP ModuleSVPLang :=
  ⟨moduleSVP_mem_NP, moduleSVP_npHard⟩

end Power2ModuleSVPSubsetSum
