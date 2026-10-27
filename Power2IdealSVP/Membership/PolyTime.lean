import Power2IdealSVP.Membership.Verifier

/-!
# Principal ideal SVP runtime certificates

Compose the existing negacyclic arithmetic and radius scanner as native polynomial-time TMs.

Paper: `paper/power2-ideal-svp.pdf`, Theorem 1 (NP membership).
-/
namespace Power2IdealSVP
open IdealCVP Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open Power2ModuleSVPSubsetSum.Membership

attribute [local irreducible] List.getD

/-- The degree, length, and nonzero-generator checks run in native polynomial time. -/
@[fun_prop] theorem idealWellFormedCheck_polytime : ComputableTidilyInPolyTime
    idealWellFormedCheck encIdeal encBool := by
  unfold idealWellFormedCheck encIdeal
  fun_prop

/-- Negacyclic recomputation of the ideal element runs in native polynomial time. -/
@[fun_prop] theorem idealProduct_polytime : ComputableTidilyInPolyTime
    (fun p : IdealInput × List ℤ => idealProduct p.1 p.2)
    (encPair encIdeal (encList encIntBin)) (encList encIntBin) := by
  unfold idealProduct encIdeal
  fun_prop

/-- The complete ideal verifier has a native multitape-TM polynomial runtime certificate. -/
@[fun_prop] theorem idealVerifier_polytime : ComputableTidilyInPolyTime idealVerifier
    (encPair encIdeal (encList encIntBin)) encBool := by
  unfold idealVerifier encIdeal
  fun_prop

namespace Membership

/-- The zero-target CVP instance bounds the original multiplier by Cramer's rule. -/
def idealBoundInput (x : IdealInput) : CVPInput :=
  (x.1, x.2.1, [], (x.1 : ℤ) * (x.2.2 : ℤ) ^ 2)

/-- Forming the squared norm bound preserves polynomial encoded size. -/
@[fun_prop] theorem idealBoundInput_polytime : ComputableTidilyInPolyTime
    idealBoundInput encIdeal encCVP := by
  unfold idealBoundInput encIdeal encCVP
  fun_prop

end Membership
end Power2IdealSVP
