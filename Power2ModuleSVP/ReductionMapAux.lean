import Power2ModuleSVP.ReductionMap
import Power2ModuleSVP.SourceMapPoly
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-! Native-machine certificates for degree selection and explicit list packing.
All degrees and loop indices are unary; coefficient arithmetic is signed binary. -/
namespace Power2ModuleSVP
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD

/-- Affine data use exactly the already certified source encoding. -/
abbrev encAffine : AffineInput ↪ List Bool := encSource

@[fun_prop] theorem dyadicCeil_polytime :
    ComputableTidilyInPolyTime dyadicCeil encUnary encUnary := by
  exact unary_pow_clog_const id' 2 2

@[fun_prop] theorem packingDegree_polytime :
    ComputableTidilyInPolyTime packingDegree encUnary encUnary := by
  unfold packingDegree
  fun_prop

/-- The cutoff exponent is fixed, so its power of two is a constant output. -/
@[fun_prop] theorem modulePackingDegree_polytime (k0 : ℕ) :
    ComputableTidilyInPolyTime (modulePackingDegree k0) encUnary encUnary := by
  unfold modulePackingDegree
  fun_prop

/-- Packing is total on arbitrary raw tuples, without algebraic tests. -/
@[fun_prop] theorem packCoset_polytime :
    ComputableTidilyInPolyTime (fun p : ℕ × AffineInput => packCoset p.1 p.2)
      (encPair encUnary encAffine) encCoset := by
  let E := encPair encUnary encAffine
  have hg : ComputableTidilyInPolyTime (fun p : ℕ × AffineInput =>
      (List.range p.1).map (fun i =>
        2*((if i = p.2.1 then 1 else 0) + p.2.2.2.1.getD i 0)))
      E (encList encIntBin) := by
    apply mapWithInput (encA := encUnary)
    · unfold E
      fun_prop
    · unfold E encAffine encSource
      fun_prop
  have hh : ComputableTidilyInPolyTime (fun p : ℕ × AffineInput =>
      (List.range p.1).map (fun i =>
        (if i < 2*p.2.1 then 1 else 0) - 2*p.2.2.2.2.getD i 0))
      E (encList encIntBin) := by
    apply mapWithInput (encA := encUnary)
    · unfold E
      fun_prop
    · unfold E encAffine encSource
      fun_prop
  exact (fst _ _).prod (hg.prod hh)

/-- Attaching an anchor and constructing the zero column are polynomial time. -/
@[fun_prop] theorem triangularInput_polytime :
    ComputableTidilyInPolyTime
      (fun p : CosetInput × List ℤ => triangularInput p.1 p.2)
      (encPair encCoset (encList encIntBin)) encSVP := by
  unfold triangularInput encSVP IdealCVP.encPairRingArgs encCoset IdealCVP.encRingArgs
  fun_prop

end Power2ModuleSVP
