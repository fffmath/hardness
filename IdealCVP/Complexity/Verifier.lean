import IdealCVP.Complexity.CertificateBits
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-! # Native polynomial-time verification of integer-list certificates -/

namespace IdealCVP

open Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- A unary dimension and two lists of signed integer coefficients. -/
abbrev RingArgs := ℕ × (List ℤ × List ℤ)

/-- Encode the arguments to coefficient multiplication and squared-distance computations. -/
def encRingArgs : RingArgs ↪ List Bool :=
  encPair encUnary (encPair (encList encIntBin) (encList encIntBin))

-- Lookup stays opaque while composing runtime certificates.

attribute [local irreducible] List.getD

@[fun_prop] theorem poly_negacyclicCoeff : ComputableTidilyInPolyTime
    (fun p : RingArgs × ℕ => negacyclicCoeff p.1.1 p.1.2.1 p.1.2.2 p.2)
    (encPair encRingArgs encUnary) encIntBin := by
  unfold negacyclicCoeff encRingArgs
  apply intBin_sum.comp
  apply mapWithInput (encA := encUnary) (by fun_prop)
  apply intBin_sum.comp
  apply mapWithInput (encA := encUnary) (by fun_prop)
  fun_prop

@[fun_prop] theorem poly_negacyclicMul : ComputableTidilyInPolyTime
    (fun p : RingArgs => negacyclicMul p.1 p.2.1 p.2.2)
    encRingArgs (encList encIntBin) := by
  unfold negacyclicMul
  apply mapWithInput (encA := encUnary)
  · unfold encRingArgs
    fun_prop
  · exact poly_negacyclicCoeff

@[fun_prop] theorem poly_listSqDistance : ComputableTidilyInPolyTime
    (fun p : RingArgs => listSqDistance p.1 p.2.1 p.2.2) encRingArgs encIntBin := by
  unfold listSqDistance encRingArgs
  apply intBin_sum.comp
  apply mapWithInput (encA := encUnary) (by fun_prop)
  fun_prop

@[fun_prop] theorem poly_cvpWellFormedCheck :
    ComputableTidilyInPolyTime cvpWellFormedCheck encCVP encBool := by
  have hp : ComputableTidilyInPolyTime
      (fun p : CVPInput × ℕ => decide (p.1.1 = 2 ^ p.2))
      (encPair encCVP encUnary) encBool :=
    (decide_eq encNat).comp
      ((unary_to_binary.comp (fst encCVP encUnary).fst').prod
        (binary_two_pow.comp (snd encCVP encUnary)))
  unfold encCVP at hp ⊢
  unfold cvpWellFormedCheck
  fun_prop

/-- The complete integer-list CVP certificate checker runs in native polynomial time. -/
@[fun_prop] theorem poly_cvpCheck : ComputableTidilyInPolyTime cvpCheck
    (encPair encCVP (encList encIntBin)) encBool := by
  unfold cvpCheck
  fun_prop

/-- NP membership with no resource hypotheses. -/
theorem principalCVP_mem_NP : PrincipalCVP ∈ NP encCVP :=
  principalCVP_mem_NP_of_resource_bounds poly_cvpCheck (fun x _ => cvpCertificateBound_bits x)

end IdealCVP
