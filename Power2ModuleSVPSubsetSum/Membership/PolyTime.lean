import Power2ModuleSVPSubsetSum.Membership.Verifier

/-!
# Native polynomial-time module verification

Compose the existing multitape-TM programs with binary-radius coefficient scans.
Auxiliary CVP inputs control certificate bits using squared radius `2*d*T²`.

Paper: `paper/power2svp-subsetsum.pdf`, Theorem 1.1 (NP membership).
-/
namespace Power2ModuleSVPSubsetSum
open IdealCVP Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Nonzero detection and the two binary-radius scans run in polynomial time. -/
@[fun_prop] theorem moduleVectorCheck_polytime : ComputableTidilyInPolyTime
    moduleVectorCheck (encPair encNat Power2ModuleSVP.encMultipliers) encBool := by
  unfold moduleVectorCheck Power2ModuleSVP.encMultipliers
  fun_prop

/-- The integer-list module verifier has a native polynomial-time TM certificate. -/
@[fun_prop] theorem moduleVerifier_polytime : ComputableTidilyInPolyTime moduleVerifier
    (encPair encSVP Power2ModuleSVP.encMultipliers) encBool := by
  unfold moduleVerifier encSVP Power2ModuleSVP.encMultipliers encPairRingArgs
  fun_prop

namespace Membership

/-- Auxiliary nonsingular module basis with the squared Euclidean bound `2*d*T²`. -/
def moduleNormInput (x : SVPInput) : ModuleSIVPInput :=
  (x.1.1, x.1.2.1, x.1.2.2, (2 : ℤ) * x.1.1 * (x.2 : ℤ) ^ 2)

/-- Auxiliary diagonal CVP instance dominating the expanded module Cramer bound. -/
def moduleBoundInput (x : SVPInput) : CVPInput :=
  IdealCVP.moduleBoundInput (moduleNormInput x)

/-- Compute the squared bound using binary arithmetic on the radius. -/
@[fun_prop] theorem moduleNormInput_polytime : ComputableTidilyInPolyTime
    moduleNormInput encSVP encModuleSIVP := by
  unfold moduleNormInput encSVP encPairRingArgs encModuleSIVP
  fun_prop

/-- The imported dominating CVP bound input remains polynomial-time computable. -/
@[fun_prop] theorem moduleBoundInput_polytime : ComputableTidilyInPolyTime
    moduleBoundInput encSVP encCVP :=
  poly_moduleBoundInput.comp moduleNormInput_polytime

end Membership
end Power2ModuleSVPSubsetSum
