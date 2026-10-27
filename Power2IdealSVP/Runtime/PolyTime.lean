import Power2IdealSVP.Runtime.Construction

/-!
# Native polynomial-time certificates for the ideal SVP reduction

Unary counters bound the graph labels, windows and degree. Signed binary arithmetic computes
powers and all coefficient operations, using the library's certified list arithmetic.

Paper: `paper/power2-ideal-svp.pdf`, Section 1.5.
-/

namespace Power2IdealSVP.Runtime

open Cslib.Complexity Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] List.getD graphVertices vertexCount normalEdges mainCase smallAnswer
  labelBase graphLabel graphLabels maxLabel edgeDifference diffSet windowBound degree
  allowedDistance
  forbiddenDistances guardCoeff guardCoeffs symmetricCoeff interactionCoeff interactionCoeffs
  listNorm interactionNorm neighborAmplitude spinThreshold guardAmplitude spinCoeffs wallCoeffs
  wallNorm clockAmplitude clockCoeffs clockNorm dominantAmplitude parityCoeffs dominantCoeffs
  generatorCoeffs outputRadius construction reduceList

/-- Encoding of the binary CLIQUE input. -/
abbrev encSource := encPair encGraph encNat

/-- Encoding of a pair of unary vertex indices. -/
abbrev encEdge := encPair encUnary encUnary

/-- A unary counter can be converted to a signed binary integer in polynomial time. -/
@[fun_prop] theorem poly_unary_int : ComputableTidilyInPolyTime
    (fun n : ℕ => (n : ℤ)) encUnary encIntBin :=
  intBin_natCast.comp unary_to_binary

/-- Normalization reads the explicitly declared vertices in polynomial time. -/
@[fun_prop] theorem poly_graphVertices : ComputableTidilyInPolyTime
    graphVertices encGraph (encList encNat) := by
  unfold graphVertices
  exact Graph.computableTidilyInPolyTime_distinctVertices

/-- The distinct vertex count has unary polynomial cost. -/
@[fun_prop] theorem poly_vertexCount : ComputableTidilyInPolyTime
    vertexCount encGraph encUnary := by
  unfold vertexCount
  fun_prop

/-- The normalized edge list is computed using two bounded unary vertex loops. -/
@[fun_prop] theorem poly_normalEdges : ComputableTidilyInPolyTime
    normalEdges encGraph (encList encEdge) := by
  unfold normalEdges
  apply flatMapWithInput (encA := encUnary) (by fun_prop)
  apply mapWithInput (encA := encUnary)
  · apply filterWithInput (encA := encUnary) (by fun_prop)
    have ha : ComputableTidilyInPolyTime
        (fun p : (Graph × ℕ) × ℕ =>
          p.1.1.adjBool ((graphVertices p.1.1).getD p.1.2 0)
            ((graphVertices p.1.1).getD p.2 0))
        (encPair (encPair encGraph encUnary) encUnary) encBool := by
      exact Graph.computableTidilyInPolyTime_adjBool.comp
        (g := fun p : (Graph × ℕ) × ℕ =>
          ((p.1.1, (graphVertices p.1.1).getD p.1.2 0),
            (graphVertices p.1.1).getD p.2 0)) (by fun_prop)
    fun_prop
  · unfold encEdge
    fun_prop

/-- Main-case testing compares the binary target without expanding it in unary. -/
@[fun_prop] theorem poly_mainCase : ComputableTidilyInPolyTime
    mainCase encSource encBool := by
  have hv : ComputableTidilyInPolyTime (fun x : Graph × ℕ => vertexCount x.1)
      encSource encNat := unary_to_binary.comp (poly_vertexCount.comp (fst _ _))
  unfold mainCase encSource at *
  fun_prop

/-- Targets zero, one and two are decided using only the normalized graph. -/
@[fun_prop] theorem poly_smallAnswer : ComputableTidilyInPolyTime
    smallAnswer encSource encBool := by
  unfold smallAnswer encSource
  fun_prop

/-- The label base is polynomially bounded even as a unary counter. -/
@[fun_prop] theorem poly_labelBase : ComputableTidilyInPolyTime
    labelBase encSource encUnary := by
  unfold labelBase encSource
  fun_prop

/-- Evaluating a label uses fixed polynomial arithmetic on unary counters. -/
@[fun_prop] theorem poly_graphLabel : ComputableTidilyInPolyTime
    (fun p : (Graph × ℕ) × ℕ => graphLabel p.1 p.2)
    (encPair encSource encUnary) encUnary := by
  unfold graphLabel
  fun_prop

/-- All vertex labels are computed in polynomial time. -/
@[fun_prop] theorem poly_graphLabels : ComputableTidilyInPolyTime
    graphLabels encSource (encList encUnary) := by
  unfold graphLabels encSource
  fun_prop

/-- The largest label retains a unary polynomial bound. -/
@[fun_prop] theorem poly_maxLabel : ComputableTidilyInPolyTime
    maxLabel encSource encUnary := by
  unfold maxLabel encSource
  fun_prop

/-- An indexed edge difference uses unary subtraction. -/
@[fun_prop] theorem poly_edgeDifference : ComputableTidilyInPolyTime
    (fun p : (Graph × ℕ) × (ℕ × ℕ) => edgeDifference p.1 p.2)
    (encPair encSource encEdge) encUnary := by
  unfold edgeDifference encEdge
  fun_prop

/-- A bounded scan constructs the sorted set of edge differences. -/
@[fun_prop] theorem poly_diffSet : ComputableTidilyInPolyTime
    diffSet encSource (encList encUnary) := by
  unfold diffSet
  apply filterWithInput (encA := encUnary) (by fun_prop)
  have he : ComputableTidilyInPolyTime
      (fun p : ((Graph × ℕ) × ℕ) × (ℕ × ℕ) => edgeDifference p.1.1 p.2)
      (encPair (encPair encSource encUnary) encEdge) encUnary := by fun_prop
  unfold encSource
  fun_prop

/-- The window bound uses only unary polynomial arithmetic. -/
@[fun_prop] theorem poly_windowBound : ComputableTidilyInPolyTime
    windowBound encSource encUnary := by
  unfold windowBound windowSpacing
  fun_prop

/-- Dyadic rounding preserves unary polynomial running time and output size. -/
@[fun_prop] theorem poly_degree : ComputableTidilyInPolyTime
    degree encSource encUnary := by
  unfold degree
  exact unary_pow_clog_const (by fun_prop) 2 2

/-- Testing allowed distances scans only the polynomially bounded edge-difference set. -/
@[fun_prop] theorem poly_allowedDistance : ComputableTidilyInPolyTime
    (fun p : (Graph × ℕ) × ℕ => allowedDistance p.1 p.2)
    (encPair encSource encUnary) encBool := by
  unfold allowedDistance windowSpacing
  fun_prop

/-- The forbidden-distance list is enumerated by unary bounded loops. -/
@[fun_prop] theorem poly_forbiddenDistances : ComputableTidilyInPolyTime
    forbiddenDistances encSource (encList encUnary) := by
  unfold forbiddenDistances
  fun_prop

/-- Binary powers with unary exponents certify all guard coefficients and intermediate bits. -/
@[fun_prop] theorem poly_guardCoeff : ComputableTidilyInPolyTime
    (fun p : (Graph × ℕ) × ℕ => guardCoeff p.1 p.2)
    (encPair encSource encUnary) encIntBin := by
  unfold guardCoeff
  apply intBin_sum.comp
  apply mapWithInput (encA := encEdge) (by unfold encEdge; fun_prop)
  unfold encEdge
  fun_prop

/-- The guard array has a polynomial-time signed binary implementation. -/
@[fun_prop] theorem poly_guardCoeffs : ComputableTidilyInPolyTime
    guardCoeffs encSource (encList encIntBin) := by
  unfold guardCoeffs
  fun_prop

/-- A self-adjoint monomial pair is computed with unary indices and binary coefficients. -/
@[fun_prop] theorem poly_symmetricCoeff : ComputableTidilyInPolyTime
    (fun p : ℕ × (ℕ × ℕ) => symmetricCoeff p.1 p.2.1 p.2.2)
    (encPair encUnary encEdge) encIntBin := by
  unfold symmetricCoeff encEdge
  fun_prop

/-- A coefficient of the endpoint interaction is a polynomial sum of binary integers. -/
@[fun_prop] theorem poly_interactionCoeff : ComputableTidilyInPolyTime
    (fun p : (Graph × ℕ) × ℕ => interactionCoeff p.1 p.2)
    (encPair encSource encUnary) encIntBin := by
  unfold interactionCoeff
  apply intBin_sum.comp
  apply mapWithInput (encA := encUnary) (by fun_prop)
  unfold symmetricCoeff windowSpacing
  fun_prop

/-- All endpoint interaction coefficients are computed in polynomial time. -/
@[fun_prop] theorem poly_interactionCoeffs : ComputableTidilyInPolyTime
    interactionCoeffs encSource (encList encIntBin) := by
  unfold interactionCoeffs
  fun_prop

/-- Summing absolute binary values computes the exact one-norm in polynomial time. -/
@[fun_prop] theorem poly_listNorm : ComputableTidilyInPolyTime
    listNorm (encList encIntBin) encNat := by
  unfold listNorm
  fun_prop

/-- The endpoint interaction norm has a native binary certificate. -/
@[fun_prop] theorem poly_interactionNorm : ComputableTidilyInPolyTime
    interactionNorm encSource encNat := by
  unfold interactionNorm
  fun_prop

/-- The nearest-neighbor amplitude is computed in binary. -/
@[fun_prop] theorem poly_neighborAmplitude : ComputableTidilyInPolyTime
    neighborAmplitude encSource encNat := by
  unfold neighborAmplitude encSource
  fun_prop

/-- The sparse-spin threshold is computed in binary. -/
@[fun_prop] theorem poly_spinThreshold : ComputableTidilyInPolyTime
    spinThreshold encSource encNat := by
  unfold spinThreshold encSource
  fun_prop

/-- The guard amplitude is computed in binary. -/
@[fun_prop] theorem poly_guardAmplitude : ComputableTidilyInPolyTime
    guardAmplitude encSource encNat := by
  unfold guardAmplitude
  fun_prop

/-- The sparse-spin polynomial uses binary scalar arithmetic over a unary coefficient loop. -/
@[fun_prop] theorem poly_spinCoeffs : ComputableTidilyInPolyTime
    spinCoeffs encSource (encList encIntBin) := by
  unfold spinCoeffs
  apply mapWithInput (encA := encUnary) (by fun_prop)
  unfold symmetricCoeff
  fun_prop

/-- Certified negacyclic convolution constructs the wall polynomial. -/
@[fun_prop] theorem poly_wallCoeffs : ComputableTidilyInPolyTime
    wallCoeffs encSource (encList encIntBin) := by
  unfold wallCoeffs
  exact IdealCVP.poly_negacyclicMul.comp
    (g := fun x => (degree x, spinCoeffs x, [1, -1]))
    (by unfold IdealCVP.encRingArgs; fun_prop)

/-- The wall norm is computed in binary. -/
@[fun_prop] theorem poly_wallNorm : ComputableTidilyInPolyTime
    wallNorm encSource encNat := by
  unfold wallNorm
  fun_prop

/-- The clock amplitude is computed in binary. -/
@[fun_prop] theorem poly_clockAmplitude : ComputableTidilyInPolyTime
    clockAmplitude encSource encNat := by
  unfold clockAmplitude
  fun_prop

/-- The full-sign clock polynomial is computed by a unary coefficient loop. -/
@[fun_prop] theorem poly_clockCoeffs : ComputableTidilyInPolyTime
    clockCoeffs encSource (encList encIntBin) := by
  unfold clockCoeffs
  fun_prop

/-- The clock norm is computed in binary. -/
@[fun_prop] theorem poly_clockNorm : ComputableTidilyInPolyTime
    clockNorm encSource encNat := by
  unfold clockNorm
  fun_prop

/-- The dominating scalar is computed in binary. -/
@[fun_prop] theorem poly_dominantAmplitude : ComputableTidilyInPolyTime
    dominantAmplitude encSource encNat := by
  unfold dominantAmplitude
  fun_prop

/-- The parity polynomial is a unary-bounded replicated list. -/
@[fun_prop] theorem poly_parityCoeffs : ComputableTidilyInPolyTime
    parityCoeffs encSource (encList encIntBin) := by
  unfold parityCoeffs
  fun_prop

/-- Binary subtraction computes the dominating factor coefficientwise. -/
@[fun_prop] theorem poly_dominantCoeffs : ComputableTidilyInPolyTime
    dominantCoeffs encSource (encList encIntBin) := by
  unfold dominantCoeffs
  fun_prop

/-- Certified negacyclic convolution computes the final generator. -/
@[fun_prop] theorem poly_generatorCoeffs : ComputableTidilyInPolyTime
    generatorCoeffs encSource (encList encIntBin) := by
  unfold generatorCoeffs
  exact IdealCVP.poly_negacyclicMul.comp
    (g := fun x => (degree x, dominantCoeffs x, parityCoeffs x))
    (by unfold IdealCVP.encRingArgs; fun_prop)

/-- The final radius uses binary arithmetic. -/
@[fun_prop] theorem poly_outputRadius : ComputableTidilyInPolyTime
    outputRadius encSource encNat := by
  unfold outputRadius
  fun_prop

/-- Native polynomial-time certificate for the unrestricted construction. -/
@[fun_prop] theorem poly_construction : ComputableTidilyInPolyTime
    construction encSource encIdeal := by
  unfold construction encIdeal
  fun_prop

/-- The complete total reduction has a native tidy multitape TM polynomial-time certificate. -/
@[fun_prop] theorem reduceList_polytime : ComputableTidilyInPolyTime
    reduceList (encPair encGraph encNat) encIdeal := by
  unfold reduceList
  exact poly_mainCase.ite' poly_construction
    (poly_smallAnswer.ite' (const yesInput) (const noInput))

/-- The unary output degree is polynomially bounded by the binary input length. -/
theorem degree_polyBounded : PolyBounded
    (fun x => (encPair encGraph encNat x).length) degree := poly_degree.polyBounded

/-- The complete signed binary output encoding has polynomial length. -/
theorem reduceList_length_polyBounded : PolyBounded
    (fun x => (encPair encGraph encNat x).length)
    (fun x => (encIdeal (reduceList x)).length) := reduceList_polytime.polyBounded_length

end Power2IdealSVP.Runtime
