import Power2ModuleSVP.Membership.Verifier

/-!
# Poly Time

Native multitape-TM polynomial-time certificates, by composition of
the existing list and signed-binary arithmetic programs.

Paper: `paper/power2svp.pdf`, Section 3.3 (proof of Theorem 1, NP membership).
-/
namespace Power2ModuleSVP
open IdealCVP Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

attribute [local irreducible] List.getD

@[fun_prop] theorem listCube_polytime : ComputableTidilyInPolyTime
    listCube (encList encIntBin) encBool := by
  unfold listCube
  fun_prop

@[fun_prop] theorem listEven_polytime : ComputableTidilyInPolyTime
    listEven (encList encIntBin) encBool := by
  unfold listEven
  fun_prop

@[fun_prop] theorem cosetWellFormedCheck_polytime : ComputableTidilyInPolyTime
    cosetWellFormedCheck encCoset encBool := by
  unfold cosetWellFormedCheck encCoset encRingArgs
  fun_prop

@[fun_prop] theorem moduleWellFormedCheck_polytime : ComputableTidilyInPolyTime
    moduleWellFormedCheck encSVP encBool := by
  unfold moduleWellFormedCheck encSVP encPairRingArgs
  fun_prop

/-- Binary encoding of the two integer multiplier lists. -/
def encMultipliers : (List ℤ × List ℤ) ↪ List Bool :=
  encPair (encList encIntBin) (encList encIntBin)

@[fun_prop] theorem cosetProduct_polytime : ComputableTidilyInPolyTime
    (fun p : CosetInput × List ℤ => cosetProduct p.1 p.2)
    (encPair encCoset (encList encIntBin)) (encList encIntBin) := by
  unfold cosetProduct encCoset encRingArgs
  fun_prop

@[fun_prop] theorem moduleProduct_polytime : ComputableTidilyInPolyTime
    (fun p : SVPInput × (List ℤ × List ℤ) => moduleProduct p.1 p.2)
    (encPair encSVP encMultipliers) encMultipliers := by
  unfold moduleProduct encSVP encPairRingArgs encMultipliers
  fun_prop

@[fun_prop] theorem cosetVerifier_polytime : ComputableTidilyInPolyTime cosetVerifier
    (encPair encCoset (encList encIntBin)) encBool := by
  unfold cosetVerifier encCoset encRingArgs
  fun_prop

@[fun_prop] theorem moduleVectorCheck_polytime : ComputableTidilyInPolyTime
    moduleVectorCheck encMultipliers encBool := by
  unfold moduleVectorCheck encMultipliers
  fun_prop

@[fun_prop] theorem moduleVerifier_polytime : ComputableTidilyInPolyTime moduleVerifier
    (encPair encSVP (encPair (encList encIntBin) (encList encIntBin))) encBool := by
  unfold moduleVerifier encSVP encPairRingArgs
  fun_prop

namespace Membership

/-- This auxiliary CVP input is used only to bound the same coset multiplier.
The target is `-h`, and a cube vector has squared norm at most `d`. -/
def cosetBoundInput (x : CosetInput) : CVPInput :=
  (x.1, x.2.1, x.2.2.map (fun z => -z), (x.1 : ℤ))

/-- The auxiliary SIVP input is used only for its nonsingular matrix bound;
we do not use its two-short-vectors acceptance predicate. -/
def moduleNormInput (x : SVPInput) : ModuleSIVPInput :=
  (x.1, x.2.1, x.2.2, (2 : ℤ) * x.1)

/-- View a module input as a CVP input for the generic coefficient bound. -/
def moduleBoundInput (x : SVPInput) : CVPInput :=
  IdealCVP.moduleBoundInput (moduleNormInput x)

@[fun_prop] theorem cosetBoundInput_polytime : ComputableTidilyInPolyTime
    cosetBoundInput encCoset encCVP := by
  unfold cosetBoundInput encCoset encRingArgs encCVP
  fun_prop

@[fun_prop] theorem moduleNormInput_polytime : ComputableTidilyInPolyTime
    moduleNormInput encSVP encModuleSIVP := by
  unfold moduleNormInput encSVP encPairRingArgs encModuleSIVP
  fun_prop

@[fun_prop] theorem moduleBoundInput_polytime : ComputableTidilyInPolyTime
    moduleBoundInput encSVP encCVP :=
  poly_moduleBoundInput.comp moduleNormInput_polytime

end Membership
end Power2ModuleSVP
