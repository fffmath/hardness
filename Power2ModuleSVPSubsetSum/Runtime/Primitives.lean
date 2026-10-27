import Power2ModuleSVPSubsetSum.Reduction.Construction
import IdealCVP.Complexity.GeneralModule
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-!
# Polynomial-time coefficient-list primitives

Certify the unary degree calculation and the signed-binary coefficient programs.
All powers of five use the library's binary integer power machine with unary exponents.

Paper: `paper/power2svp-subsetsum.pdf`, Section 4.1.
-/

namespace Power2ModuleSVPSubsetSum.Reduction
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

attribute [local irreducible] List.getD

/-- Dyadic rounding is polynomial time when the requested size is unary. -/
@[fun_prop] theorem halfDegree_polytime :
    ComputableTidilyInPolyTime halfDegree encUnary encUnary := by
  unfold halfDegree
  exact unary_pow_clog_const (by fun_prop) 2 2

/-- The output degree has a polynomial-time unary certificate. -/
@[fun_prop] theorem degree_polytime :
    ComputableTidilyInPolyTime degree encUnary encUnary := by
  unfold degree
  fun_prop

/-- Summing binary absolute values computes the list l1 norm in polynomial time. -/
@[fun_prop] theorem listL1_polytime :
    ComputableTidilyInPolyTime listL1 (encList encIntBin) encNat := by
  unfold listL1
  fun_prop

/-- Binary scalar multiplication traverses the unary output degree. -/
@[fun_prop] theorem scale_polytime :
    ComputableTidilyInPolyTime (fun p : ℕ × (ℤ × List ℤ) => scale p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encIntBin (encList encIntBin)))
      (encList encIntBin) := by
  unfold scale
  apply mapWithInput (encA := encUnary) (by fun_prop)
  fun_prop

/-- The constant-polynomial array is polynomial time in its degree and coefficient. -/
@[fun_prop] theorem constant_polytime :
    ComputableTidilyInPolyTime (fun p : ℕ × ℤ => constant p.1 p.2)
      (encPair encUnary encIntBin) (encList encIntBin) := by
  unfold constant
  apply mapWithInput (encA := encUnary) (by fun_prop)
  fun_prop

/-- The two-term filter is computed by a unary traversal. -/
@[fun_prop] theorem filterD_polytime :
    ComputableTidilyInPolyTime filterD encUnary (encList encIntBin) := by
  unfold filterD
  apply mapWithInput (encA := encUnary) (by fun_prop)
  fun_prop

/-- The signed two-term adjoint filter is computed by a unary traversal. -/
@[fun_prop] theorem filterDStar_polytime :
    ComputableTidilyInPolyTime filterDStar encUnary (encList encIntBin) := by
  unfold filterDStar
  apply mapWithInput (encA := encUnary) (by fun_prop)
  fun_prop

/-- Powers of five have linear bit length in the unary half-degree. -/
@[fun_prop] theorem filterK_polytime :
    ComputableTidilyInPolyTime filterK encUnary (encList encIntBin) := by
  unfold filterK
  apply mapWithInput (encA := encUnary) (by fun_prop)
  fun_prop

/-- Boolean masks are polynomial-time coefficient arrays. -/
@[fun_prop] theorem mask_polytime :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => mask p.1 p.2)
      (encPair encUnary encUnary) (encList encIntBin) := by
  unfold mask
  apply mapWithInput (encA := encUnary) (by fun_prop)
  fun_prop

/-- Laurent weight packing reads binary weights at unary positions. -/
@[fun_prop] theorem weights_polytime :
    ComputableTidilyInPolyTime (fun p : ℕ × List ℕ => weights p.1 p.2)
      (encPair encUnary (encList encNat)) (encList encIntBin) := by
  unfold weights
  apply mapWithInput (encA := encUnary) (by fun_prop)
  have hlist := (fst (encPair encUnary (encList encNat)) encUnary).snd'
  have hzero : ComputableTidilyInPolyTime
      (fun p : (ℕ × List ℕ) × ℕ => p.1.2.getD 0 0)
      (encPair (encPair encUnary (encList encNat)) encUnary) encNat :=
    (listGetD (encA := encNat) (encL := encList encNat) 0).comp
      (hlist.prod (const 0))
  have hindex : ComputableTidilyInPolyTime
      (fun p : (ℕ × List ℕ) × ℕ => p.1.2.getD (p.1.1 - p.2) 0)
      (encPair (encPair encUnary (encList encNat)) encUnary) encNat :=
    (listGetD (encA := encNat) (encL := encList encNat) 0).comp
      (hlist.prod (by fun_prop))
  simpa only [decide_eq_true_eq, Function.comp_apply] using
    (show ComputableTidilyInPolyTime
    (fun p : (ℕ × List ℕ) × ℕ => decide (p.2 = 0))
    (encPair (encPair encUnary (encList encNat)) encUnary) encBool from by fun_prop).ite'
      (intBin_natCast.comp hzero) (intBin_neg.comp (intBin_natCast.comp hindex))

end Power2ModuleSVPSubsetSum.Reduction
