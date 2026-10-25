import Power2ModuleSVP.Runtime.Coloring.ConstraintData

/-!
# Native reification of coloring constraints

Certify scalar damping, fixed-coordinate tests, constraint lists, quadratic rows, and direction
data for the stopped coloring walk. Heavy-row ordering is passed through its explicit native
interface.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

namespace Power2ModuleSVP.ColoringRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open PartialColoringAlg
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD dampingList constraintHead

@[fun_prop] theorem walkRowAt_polytime :
    ComputableTidilyInPolyTime (fun p : WalkParameter × ℕ => p.1.2.getD p.2 (0, []))
      (encPair encWalkParameter encUnary) (encPair encColoringRational (encList encColoringRational)) := by
  unfold encWalkParameter encQuadraticRows
  fun_prop

@[fun_prop] theorem signTest_polytime :
    ComputableTidilyInPolyTime (fun q : ℚ => decide (q = -1 ∨ q = 1))
      encColoringRational encBool :=
  decide_or (decide_eq' (id' (encIn := encColoringRational)) (.const (-1))) (decide_eq' (id' (encIn := encColoringRational)) (.const 1))

def scalarDamping (p : ℕ × ℚ) : ℚ :=
  1 - 4 * (1 / (16 * (p.1 : ℚ))) ^ 2 * p.2 ^ 2 / p.1

theorem scalarDamping_polytime :
    ComputableTidilyInPolyTime scalarDamping (encPair encUnary encColoringRational)
      encColoringRational := by
  have hrq := natCast_polytime.comp (unary_to_binary.comp (fst encUnary encColoringRational))
  have hl := snd encUnary encColoringRational
  have hs := div_polytime.comp ((const 1).prod (mul_polytime.comp ((const 16).prod hrq)))
  have hs2 := pow_polytime.comp (hs.prod (const 2))
  have hl2 := pow_polytime.comp (hl.prod (const 2))
  have hout := sub_polytime.comp ((const 1).prod
    (div_polytime.comp ((mul_polytime.comp
      ((mul_polytime.comp ((const 4).prod hs2)).prod hl2)).prod hrq)))
  exact hout.of_enc_eq fun _ => congrArg encColoringRational (by rfl)

theorem dampingList_polytime :
    ComputableTidilyInPolyTime (fun p : WalkParameter × ℕ => dampingList p.1 p.2)
      (encPair encWalkParameter encUnary) encColoringRational := by
  have hr : ComputableTidilyInPolyTime (fun p : WalkParameter × ℕ => p.1.1)
      (encPair encWalkParameter encUnary) encUnary := by unfold encWalkParameter; fun_prop
  have hl := walkRowAt_polytime.fst'
  have hout := scalarDamping_polytime.comp (hr.prod hl)
  exact hout.of_enc_eq fun p => congrArg encColoringRational (by
    unfold dampingList scalarDamping stepSize
    rfl)

theorem constraintHead_polytime :
    ComputableTidilyInPolyTime constraintHead encWalkInput (encList encColoringRational) := by
  unfold constraintHead
  apply mapWithInput (encA := encUnary) (range.comp (by unfold encWalkInput encWalkParameter; fun_prop))
  apply sum_polytime.comp
  apply mapWithInput (encA := encUnary) (range.comp (by unfold encWalkInput encWalkParameter encQuadraticRows; fun_prop))
  have hrow : ComputableTidilyInPolyTime
      (fun p : (WalkInput × ℕ) × ℕ => p.1.1.1.2.getD p.2 (0, []))
      (encPair (encPair encWalkInput encUnary) encUnary)
      (encPair encColoringRational (encList encColoringRational)) := by
    have hraw := walkRowAt_polytime.comp (show ComputableTidilyInPolyTime
      (fun p : (WalkInput × ℕ) × ℕ => (p.1.1.1, p.2))
      (encPair (encPair encWalkInput encUnary) encUnary)
      (encPair encWalkParameter encUnary) from by unfold encWalkInput; fun_prop)
    exact hraw.of_enc_eq fun _ => congrArg (encPair encColoringRational (encList encColoringRational)) (by rfl)
  have ht := hrow.fst'
  have hv := hrow.snd'
  have hd : ComputableTidilyInPolyTime
      (fun p : (WalkInput × ℕ) × ℕ => dampingList p.1.1.1 p.2)
      (encPair (encPair encWalkInput encUnary) encUnary) encColoringRational := by
    have hraw := dampingList_polytime.comp (show ComputableTidilyInPolyTime
      (fun p : (WalkInput × ℕ) × ℕ => (p.1.1.1, p.2))
      (encPair (encPair encWalkInput encUnary) encUnary)
      (encPair encWalkParameter encUnary) from by unfold encWalkInput; fun_prop)
    exact hraw.of_enc_eq fun _ => congrArg encColoringRational (by rfl)
  have hw : ComputableTidilyInPolyTime
      (fun p : (WalkInput × ℕ) × ℕ => p.1.1.2.2.getD p.2 0)
      (encPair (encPair encWalkInput encUnary) encUnary) encColoringRational := by
    unfold encWalkInput encListState
    fun_prop
  have hvj := (listGetD (encA := encColoringRational) 0).comp
    (hv.prod (show ComputableTidilyInPolyTime
      (fun p : (WalkInput × ℕ) × ℕ => p.1.2)
      (encPair (encPair encWalkInput encUnary) encUnary) encUnary from by fun_prop))
  have hout := mul_polytime.comp ((mul_polytime.comp ((mul_polytime.comp (hw.prod hd)).prod ht)).prod hvj)
  exact hout.of_enc_eq fun _ => congrArg encColoringRational (by rfl)


@[fun_prop] theorem coordinateList_polytime :
    ComputableTidilyInPolyTime coordinateList (encPair encUnary encUnary)
      (encList encColoringRational) := by
  unfold coordinateList
  apply mapWithInput (encA := encUnary) (range.comp (fst _ _))
  fun_prop

@[fun_prop] theorem constraintsList_polytime (h : HeavyIndicesNativeHypothesis) :
    ComputableTidilyInPolyTime constraintsList encWalkInput
      (encList (encList encColoringRational)) := by
  unfold constraintsList
  apply cons' constraintHead_polytime
  apply listAppend'
  · apply listAppend'
    · apply mapWithInput
      · apply filterWithInput (range.comp (by unfold encWalkInput encWalkParameter; fun_prop))
        exact signTest_polytime.comp (show ComputableTidilyInPolyTime
          (fun p : WalkInput × ℕ => p.1.2.1.getD p.2 0)
          (encPair encWalkInput encUnary) encColoringRational from by
            unfold encWalkInput encListState; fun_prop)
      · exact coordinateList_polytime.comp (show ComputableTidilyInPolyTime
          (fun p : WalkInput × ℕ => (p.1.1.1, p.2))
          (encPair encWalkInput encUnary) (encPair encUnary encUnary) from by
            unfold encWalkInput encWalkParameter; fun_prop)
    · apply mapWithInput
      · exact h.polytime.comp (show ComputableTidilyInPolyTime
          (fun p : WalkInput => (p.1.1, p.2.2)) encWalkInput
          (encPair encUnary (encList encColoringRational)) from by
            unfold encWalkInput encWalkParameter encListState; fun_prop)
      · exact walkRowAt_polytime.snd'.comp (show ComputableTidilyInPolyTime (fun p : WalkInput × ℕ => (p.1.1, p.2)) (encPair encWalkInput encUnary) (encPair encWalkParameter encUnary) from by unfold encWalkInput; fun_prop)
  · apply mapWithInput
    · apply filterWithInput (range.comp (by unfold encWalkInput encWalkParameter encQuadraticRows; fun_prop))
      have ht := walkRowAt_polytime.fst'.comp (show ComputableTidilyInPolyTime
        (fun p : WalkInput × ℕ => (p.1.1, p.2))
        (encPair encWalkInput encUnary) (encPair encWalkParameter encUnary) from by
          unfold encWalkInput; fun_prop)
      have hout := le_polytime.comp (ht.prod (const 1))
      exact hout.of_enc_eq fun _ => congrArg encBool (by rfl)
    · exact walkRowAt_polytime.snd'.comp (show ComputableTidilyInPolyTime (fun p : WalkInput × ℕ => (p.1.1, p.2)) (encPair encWalkInput encUnary) (encPair encWalkParameter encUnary) from by unfold encWalkInput; fun_prop)

@[fun_prop] theorem quadraticList_polytime :
    ComputableTidilyInPolyTime quadraticList encWalkInput encQuadraticRows := by
  unfold quadraticList
  apply mapWithInput (encA := encUnary) (range.comp (by unfold encWalkInput encWalkParameter encQuadraticRows; fun_prop))
  have hrow := walkRowAt_polytime.comp
    (show ComputableTidilyInPolyTime (fun p : WalkInput × ℕ => (p.1.1, p.2))
      (encPair encWalkInput encUnary) (encPair encWalkParameter encUnary) from by
        unfold encWalkInput; fun_prop)
  have ht := hrow.fst'
  have hv := hrow.snd'
  have hw : ComputableTidilyInPolyTime (fun p : WalkInput × ℕ => p.1.2.2.getD p.2 0)
      (encPair encWalkInput encUnary) encColoringRational := by
    unfold encWalkInput encListState
    fun_prop
  have ht2 : ComputableTidilyInPolyTime (fun p : WalkInput × ℕ => (p.1.1.2.getD p.2 (0, [])).1 ^ 2)
      (encPair encWalkInput encUnary) encColoringRational := by fun_prop
  have hout := (mul_polytime.comp (hw.prod ht2)).prod hv
  exact hout.of_enc_eq fun _ => congrArg (encPair encColoringRational (encList encColoringRational)) (by rfl)


@[fun_prop] theorem directionDataList_polytime (h : HeavyIndicesNativeHypothesis) :
    ComputableTidilyInPolyTime directionDataList encWalkInput encDirectionInput := by
  unfold directionDataList encDirectionInput
  have hc := constraintsList_polytime h
  have hq := quadraticList_polytime
  unfold encWalkInput encWalkParameter at *
  fun_prop


end Power2ModuleSVP.ColoringRuntime
