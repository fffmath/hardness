import Power2ModuleSVP.Source.Map

/-!
# Poly Time

Native multitape polynomial-time certificates for the Boolean source program.

Paper: `paper/power2svp.pdf`, Section 4 (Proposition 2 and Lemmas 5–6).
-/
namespace Power2ModuleSVP
open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace SourceRuntime
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD

@[fun_prop] theorem poly_compact :
    ComputableTidilyInPolyTime compact encCNF encFormula := by
  exact CNF.isPolyTime_compact encNat

@[fun_prop] theorem poly_normalizeData :
    ComputableTidilyInPolyTime normalizeData encCNF encNormalized := by
  unfold normalizeData encNormalized
  fun_prop

@[fun_prop] theorem poly_positiveRows :
    ComputableTidilyInPolyTime positiveRows encNormalized (encList encTriple) := by
  have hcomp : ComputableTidilyInPolyTime (fun p : NormalizedInput =>
      (List.range p.1).map (fun i => (xCode i true, xCode i false, 1)))
      encNormalized (encList encTriple) := by
    apply mapWithInput (encA := encUnary)
    · unfold encNormalized
      fun_prop
    · unfold encNormalized encTriple xCode
      fun_prop
  have hchoice : ComputableTidilyInPolyTime (fun p : NormalizedInput =>
      (List.range p.2.length).map (fun j =>
        (auxCode p.1 j 0 true, auxCode p.1 j 1 true, auxCode p.1 j 2 true)))
      encNormalized (encList encTriple) := by
    apply mapWithInput (encA := encUnary)
    · unfold encNormalized
      fun_prop
    · unfold encNormalized encTriple auxCode
      fun_prop
  have himp : ComputableTidilyInPolyTime (fun p : NormalizedInput =>
      ((List.range p.2.length).map fun j => (List.range 3).map fun k =>
        let l := (p.2.getD j []).getD k (0,false)
        (auxCode p.1 j k true, xCode l.1 (!l.2), auxCode p.1 j k false)).flatten)
      encNormalized (encList encTriple) := by
    apply (flatten encTriple).comp
    apply mapWithInput (encA := encUnary)
    · unfold encNormalized
      fun_prop
    · apply mapWithInput (encA := encUnary) (by fun_prop)
      let E := encPair (encPair encNormalized encUnary) encUnary
      have hlit : ComputableTidilyInPolyTime
          (fun p : (NormalizedInput × ℕ) × ℕ =>
            (p.1.1.2.getD p.1.2 []).getD p.2 (0,false)) E encLiteral := by
        have hrow : ComputableTidilyInPolyTime
            (fun p : (NormalizedInput × ℕ) × ℕ => p.1.1.2.getD p.1.2 [])
            E (encList encLiteral) := by
          unfold E encNormalized encFormula encLiteral
          fun_prop
        exact (listGetD (encA := encLiteral) (0,false)).comp
          (hrow.prod (by unfold E; fun_prop))
      have hv := (fst encUnary encBool).comp hlit
      have hb := (snd encUnary encBool).comp hlit
      dsimp only
      unfold encTriple auxCode xCode
      unfold E encNormalized at hv hb
      unfold encNormalized
      fun_prop
  unfold positiveRows
  exact listAppend' (listAppend' (listAppend'
    (const [(0,1,2),(0,1,3),(0,2,3)]) hcomp) hchoice) himp

@[fun_prop] theorem poly_positiveData :
    ComputableTidilyInPolyTime positiveData encNormalized encPositive := by
  unfold positiveData encPositive
  apply ComputableTidilyInPolyTime.prod
  · unfold encNormalized encFormula encLiteral
    fun_prop
  · exact poly_positiveRows

section Scalar
variable {α : Type} {E : α ↪ List Bool} {e v r i : α → ℕ}

@[fun_prop] theorem poly_position_of
    (he : ComputableTidilyInPolyTime e E encUnary)
    (hi : ComputableTidilyInPolyTime i E encUnary) :
    ComputableTidilyInPolyTime (fun a => position (e a) (i a)) E encUnary := by
  unfold position IdealCVP.SidonPositions.erdosTuranAlpha
  fun_prop

@[fun_prop] theorem poly_top_of
    (he : ComputableTidilyInPolyTime e E encUnary)
    (hv : ComputableTidilyInPolyTime v E encUnary)
    (hr : ComputableTidilyInPolyTime r E encUnary) :
    ComputableTidilyInPolyTime (fun a => top (e a) (v a) (r a)) E encUnary := by
  unfold top delta bound IdealCVP.SidonPositions.erdosTuranAlpha
  fun_prop

@[fun_prop] theorem poly_cluster_of
    (he : ComputableTidilyInPolyTime e E encUnary)
    (hv : ComputableTidilyInPolyTime v E encUnary)
    (hi : ComputableTidilyInPolyTime i E encUnary) :
    ComputableTidilyInPolyTime (fun a => cluster (e a) (v a) (i a)) E encUnary := by
  unfold cluster delta bound IdealCVP.SidonPositions.erdosTuranAlpha
  fun_prop

@[fun_prop] theorem poly_dimension_of
    (he : ComputableTidilyInPolyTime e E encUnary)
    (hv : ComputableTidilyInPolyTime v E encUnary)
    (hr : ComputableTidilyInPolyTime r E encUnary) :
    ComputableTidilyInPolyTime (fun a => dimension (e a) (v a) (r a)) E encUnary := by
  unfold dimension
  fun_prop
end Scalar

abbrev CheckArgs := PositiveInput × ℕ × ℕ
abbrev encCheck := encPair encPositive (encPair encUnary encUnary)

@[fun_prop] theorem poly_lowerCheck :
    ComputableTidilyInPolyTime (fun a : CheckArgs => lowerCheck a.1 a.2.1 a.2.2)
      encCheck encBool := by
  unfold lowerCheck
  apply anyWithInput (encA := encUnary)
  · unfold encCheck encPositive
    fun_prop
  · let E := encPair encCheck encUnary
    have ht : ComputableTidilyInPolyTime
        (fun p : CheckArgs × ℕ => p.1.1.2.getD (p.2/2) (0,0,0)) E encTriple := by
      unfold E encCheck encPositive encTriple
      fun_prop
    have h1 := (fst encUnary (encPair encUnary encUnary)).comp ht
    have h2 := (fst encUnary encUnary).comp ((snd encUnary (encPair encUnary encUnary)).comp ht)
    have h3 := (snd encUnary encUnary).comp ((snd encUnary (encPair encUnary encUnary)).comp ht)
    dsimp only
    unfold E encCheck encPositive at h1 h2 h3
    unfold encCheck encPositive
    fun_prop

@[fun_prop] theorem poly_lowerCheck_of {α : Type} {E : α ↪ List Bool}
    {p : α → PositiveInput} {e z : α → ℕ}
    (hp : ComputableTidilyInPolyTime p E encPositive)
    (he : ComputableTidilyInPolyTime e E encUnary)
    (hz : ComputableTidilyInPolyTime z E encUnary) :
    ComputableTidilyInPolyTime (fun a => lowerCheck (p a) (e a) (z a)) E encBool :=
  poly_lowerCheck.comp (hp.prod (he.prod hz))

@[fun_prop] theorem poly_supportCheck :
    ComputableTidilyInPolyTime (fun a : CheckArgs => supportCheck a.1 a.2.1 a.2.2)
      encCheck encBool := by
  unfold supportCheck
  have ha : ComputableTidilyInPolyTime (fun a : CheckArgs =>
      (List.range (top a.2.1 a.1.1 a.1.2.length+1)).any (fun z =>
        lowerCheck a.1 a.2.1 z && decide (top a.2.1 a.1.1 a.1.2.length-z = a.2.2)))
      encCheck encBool := by
    apply anyWithInput (encA := encUnary)
    · unfold encCheck encPositive
      fun_prop
    · unfold encCheck encPositive
      fun_prop
  unfold encCheck encPositive at *
  fun_prop

@[fun_prop] theorem poly_supportCheck_of {α : Type} {E : α ↪ List Bool}
    {p : α → PositiveInput} {e z : α → ℕ}
    (hp : ComputableTidilyInPolyTime p E encPositive)
    (he : ComputableTidilyInPolyTime e E encUnary)
    (hz : ComputableTidilyInPolyTime z E encUnary) :
    ComputableTidilyInPolyTime (fun a => supportCheck (p a) (e a) (z a)) E encBool :=
  poly_supportCheck.comp (hp.prod (he.prod hz))

@[fun_prop] theorem poly_touchedCheck :
    ComputableTidilyInPolyTime (fun a : CheckArgs => touchedCheck a.1 a.2.1 a.2.2)
      encCheck encBool := by
  unfold touchedCheck
  apply anyWithInput (encA := encUnary)
  · unfold encCheck encPositive
    fun_prop
  · apply anyWithInput (encA := encUnary)
    · unfold encCheck encPositive
      fun_prop
    · unfold encCheck encPositive
      fun_prop

@[fun_prop] theorem poly_negativeCheck :
    ComputableTidilyInPolyTime (fun a : CheckArgs => negativeCheck a.1 a.2.1 a.2.2)
      encCheck encBool := by
  unfold negativeCheck
  apply anyWithInput (encA := encUnary)
  · unfold encCheck encPositive
    fun_prop
  · unfold encCheck encPositive
    fun_prop

@[fun_prop] theorem poly_offset :
    ComputableTidilyInPolyTime (fun a : CheckArgs => offset a.1 a.2.1 a.2.2)
      encCheck encIntBin := by
  unfold offset
  fun_prop

@[fun_prop] theorem poly_affineData :
    ComputableTidilyInPolyTime affineData encPositive encSource := by
  unfold affineData encSource
  have he : ComputableTidilyInPolyTime (fun p : PositiveInput => positionPrime p.1)
      encPositive encUnary := by unfold encPositive; fun_prop
  have ht : ComputableTidilyInPolyTime (fun p : PositiveInput =>
      top (positionPrime p.1) p.1 p.2.length) encPositive encUnary := by
    unfold encPositive
    fun_prop
  have hd : ComputableTidilyInPolyTime (fun p : PositiveInput =>
      dimension (positionPrime p.1) p.1 p.2.length) encPositive encUnary := by
    unfold encPositive
    fun_prop
  have hP : ComputableTidilyInPolyTime (fun p : PositiveInput =>
      (List.range (top (positionPrime p.1) p.1 p.2.length+1)).map (fun z =>
        if supportCheck p (positionPrime p.1) z then (1 : ℤ) else 0))
      encPositive (encList encIntBin) := by
    apply mapWithInput (encA := encUnary) (by fun_prop)
    unfold encPositive
    fun_prop
  have hc : ComputableTidilyInPolyTime (fun p : PositiveInput =>
      (List.range (dimension (positionPrime p.1) p.1 p.2.length)).map (offset p (positionPrime p.1)))
      encPositive (encList encIntBin) := by
    apply mapWithInput (encA := encUnary) (by fun_prop)
    exact poly_offset.comp (g := fun p : PositiveInput × ℕ =>
      (p.1, positionPrime p.1.1, p.2)) (by unfold encPositive encCheck; fun_prop)
  exact hd.prod (ht.prod (hP.prod hc))

end SourceRuntime

/-- The complete Boolean source map is computable by one native multitape TM
in polynomial time, uniformly over all CNFs and arbitrary binary labels. -/
@[fun_prop] theorem sourceMap_polytime :
    ComputableTidilyInPolyTime sourceMap encCNF encSource :=
  SourceRuntime.poly_affineData.comp (SourceRuntime.poly_positiveData.comp
    (SourceRuntime.poly_normalizeData.comp computableTidilyInPolyTime_toExactThreeSAT))

end Power2ModuleSVP
