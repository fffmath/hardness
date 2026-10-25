import Power2ModuleSVP.Runtime.Coloring.Recursion.Explicit

/-!
# Program

Reified one-level operations for the actual full-coloring recursion.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open Coloring
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def canonicalColoringInput (p : PartialColoringInput) : PartialColoringInput :=
  (p.1.map fun row => (List.range p.2.1.length).map fun j => row.getD j 0,
    (p.2.1, (List.range p.1.length).map fun i => p.2.2.getD i 0))

def recursivePoint (F : PartialColoringInput → List ℚ) (p : PartialColoringInput) : List ℚ :=
  F (canonicalColoringInput p)

def recursionProgress (F : PartialColoringInput → List ℚ) (p : PartialColoringInput) : Bool :=
  decide (64 < p.2.1.length) &&
    decide ((ExplicitRecursion.activeIndices p.2.1.length (recursivePoint F p)).length < p.2.1.length)

def recursionNext (F : PartialColoringInput → List ℚ) (p : PartialColoringInput) : PartialColoringInput :=
  let y := recursivePoint F p
  let active := ExplicitRecursion.activeIndices p.2.1.length y
  (p.1.map fun row => restrictList (active, row),
    (restrictList (active, y), (List.range p.1.length).map fun i => p.2.2.getD i 0 + 4))

def recursionAssemble (F : PartialColoringInput → List ℚ)
    (p : PartialColoringInput) (z : List ℚ) : List ℚ :=
  ExplicitRecursion.scatterList p.2.1.length (recursivePoint F p, z)

@[fun_prop] theorem canonicalColoringInput_polytime :
    ComputableTidilyInPolyTime canonicalColoringInput encPartialColoring encPartialColoring := by
  unfold canonicalColoringInput encPartialColoring
  apply prod
  · apply mapWithInput (fst _ _)
    apply mapWithInput (range.comp ((length_list encColoringRational).comp
      ((fst _ _).comp ((snd _ _).comp (fst _ _)))))
    fun_prop
  · apply prod
    · fun_prop
    · apply mapWithInput (range.comp ((length_list (encList encColoringRational)).comp (fst _ _)))
      fun_prop

 theorem recursivePoint_polytime (F : PartialColoringInput → List ℚ)
    (hF : ComputableTidilyInPolyTime F encPartialColoring (encList encColoringRational)) :
    ComputableTidilyInPolyTime (recursivePoint F) encPartialColoring
      (encList encColoringRational) := hF.comp canonicalColoringInput_polytime

 theorem recursionProgress_polytime (F : PartialColoringInput → List ℚ)
    (hF : ComputableTidilyInPolyTime F encPartialColoring (encList encColoringRational)) :
    ComputableTidilyInPolyTime (recursionProgress F) encPartialColoring encBool := by
  have hy := recursivePoint_polytime F hF
  unfold recursionProgress encPartialColoring at *
  fun_prop

 theorem recursionNext_polytime (F : PartialColoringInput → List ℚ)
    (hF : ComputableTidilyInPolyTime F encPartialColoring (encList encColoringRational)) :
    ComputableTidilyInPolyTime (recursionNext F) encPartialColoring encPartialColoring := by
  have hy := recursivePoint_polytime F hF
  have ha : ComputableTidilyInPolyTime
      (fun p : PartialColoringInput => ExplicitRecursion.activeIndices p.2.1.length (recursivePoint F p))
      encPartialColoring (encList encUnary) := by
    have hr : ComputableTidilyInPolyTime (fun p : PartialColoringInput => p.2.1.length)
        encPartialColoring encUnary := by unfold encPartialColoring; fun_prop
    exact ExplicitRecursion.activeIndices_polytime.comp (hr.prod hy)
  unfold recursionNext encPartialColoring at *
  apply prod
  · apply mapWithInput (fst _ _)
    apply restrictList_polytime.comp
    fun_prop
  · apply prod
    · apply restrictList_polytime.comp
      fun_prop
    · apply mapWithInput (range.comp ((length_list (encList encColoringRational)).comp (fst _ _)))
      fun_prop

 theorem recursionAssemble_polytime (F : PartialColoringInput → List ℚ)
    (hF : ComputableTidilyInPolyTime F encPartialColoring (encList encColoringRational)) :
    ComputableTidilyInPolyTime (fun p : PartialColoringInput × List ℚ => recursionAssemble F p.1 p.2)
      (encPair encPartialColoring (encList encColoringRational)) (encList encColoringRational) := by
  have hy := (recursivePoint_polytime F hF).comp (fst encPartialColoring (encList encColoringRational))
  have hr : ComputableTidilyInPolyTime (fun p : PartialColoringInput × List ℚ => p.1.2.1.length)
      (encPair encPartialColoring (encList encColoringRational)) encUnary := by
    unfold encPartialColoring; fun_prop
  exact ExplicitRecursion.scatterList_polytime.comp (hr.prod (hy.prod (snd _ _)))


 theorem recursionNext_dimension_lt (F : PartialColoringInput → List ℚ) (p : PartialColoringInput)
    (h : recursionProgress F p = true) : (recursionNext F p).2.1.length < p.2.1.length := by
  have h' := (Bool.and_eq_true_iff.mp h).2
  simpa [recursionNext] using of_decide_eq_true h'

end Power2ModuleSVP.ColoringRuntime

namespace Power2ModuleSVP.ColoringRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open Coloring
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def recursionSafeAssemble (F : PartialColoringInput → List ℚ)
    (p : PartialColoringInput) (z : List ℚ) : List ℚ :=
  let y := recursivePoint F p
  ExplicitRecursion.scatterList p.2.1.length (y, (List.range (ExplicitRecursion.activeIndices p.2.1.length y).length).map fun j =>
    nearestRationalSign (z.getD j 0))

 theorem recursionSafeAssemble_polytime (F : PartialColoringInput → List ℚ)
    (hF : ComputableTidilyInPolyTime F encPartialColoring (encList encColoringRational)) :
    ComputableTidilyInPolyTime (fun p : PartialColoringInput × List ℚ => recursionSafeAssemble F p.1 p.2)
      (encPair encPartialColoring (encList encColoringRational)) (encList encColoringRational) := by
  have hy := (recursivePoint_polytime F hF).comp (fst encPartialColoring (encList encColoringRational))
  have ha : ComputableTidilyInPolyTime
      (fun p : PartialColoringInput × List ℚ => ExplicitRecursion.activeIndices p.1.2.1.length (recursivePoint F p.1))
      (encPair encPartialColoring (encList encColoringRational)) (encList encUnary) := by
    have hr : ComputableTidilyInPolyTime (fun p : PartialColoringInput × List ℚ => p.1.2.1.length)
        (encPair encPartialColoring (encList encColoringRational)) encUnary := by
      unfold encPartialColoring; fun_prop
    exact ExplicitRecursion.activeIndices_polytime.comp (hr.prod hy)
  have hr : ComputableTidilyInPolyTime (fun p : PartialColoringInput × List ℚ => p.1.2.1.length)
      (encPair encPartialColoring (encList encColoringRational)) encUnary := by
    unfold encPartialColoring; fun_prop
  have hz : ComputableTidilyInPolyTime
      (fun p : PartialColoringInput × List ℚ =>
        (List.range (ExplicitRecursion.activeIndices p.1.2.1.length (recursivePoint F p.1)).length).map
          fun j => nearestRationalSign (p.2.getD j 0))
      (encPair encPartialColoring (encList encColoringRational)) (encList encColoringRational) := by
    apply mapWithInput (range.comp ((length_list encUnary).comp ha))
    fun_prop
  exact ExplicitRecursion.scatterList_polytime.comp (hr.prod (hy.prod hz))

 theorem recursionSafeAssemble_signs (F : PartialColoringInput → List ℚ)
    (p : PartialColoringInput) (z : List ℚ) :
    ∀ q ∈ recursionSafeAssemble F p z, q = -1 ∨ q = 1 := by
  intro q hq
  unfold recursionSafeAssemble at hq
  rw [ExplicitRecursion.scatterList_spec] at hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  apply extend_signs
  intro k
  have he := ExplicitRecursion.activeIndices_spec p.2.1.length (recursivePoint F p)
  have hlen : (ExplicitRecursion.activeIndices p.2.1.length (recursivePoint F p)).length =
      (activeSet (readColoringVector p.2.1.length (recursivePoint F p))).card := by
    rw [he, List.length_ofFn]
  have hk : k.val < (ExplicitRecursion.activeIndices p.2.1.length (recursivePoint F p)).length := by rw [hlen]; exact k.isLt
  simp only [readColoringVector, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some]
  exact nearestRationalSign_isSign _

abbrev RecursionStack := PartialColoringInput × List PartialColoringInput

def encRecursionStack : RecursionStack ↪ List Bool :=
  encPair encPartialColoring (encList encPartialColoring)

def descentStep (F : PartialColoringInput → List ℚ) (s : RecursionStack) : RecursionStack :=
  if recursionProgress F s.1 then (recursionNext F s.1, s.1 :: s.2) else s

def descent (F : PartialColoringInput → List ℚ) (p : PartialColoringInput) : RecursionStack :=
  (descentStep F)^[p.2.1.length] (p, [])

def fullColorListEvaluator (F : PartialColoringInput → List ℚ) (p : PartialColoringInput) : List ℚ :=
  let s := descent F p
  s.2.foldl (fun z frame => recursionSafeAssemble F frame z)
    (s.1.2.1.map nearestRationalSign)

 theorem descentStep_polytime (F : PartialColoringInput → List ℚ)
    (hF : ComputableTidilyInPolyTime F encPartialColoring (encList encColoringRational)) :
    ComputableTidilyInPolyTime (descentStep F) encRecursionStack encRecursionStack := by
  unfold descentStep encRecursionStack
  apply ((recursionProgress_polytime F hF).comp (fst _ _)).cond
  · exact ((recursionNext_polytime F hF).comp (fst _ _)).prod (by fun_prop)
  · exact id'

/-- This local size obligation concerns recursive input data only. Stack
frames store those same inputs; neither full outputs nor machine runtimes
occur in the field. -/
structure RecursiveInputEncodingHypothesis (F : PartialColoringInput → List ℚ) : Prop where
  input_bound : ∃ c d : ℕ, ∀ (p : PartialColoringInput) (i : ℕ), i ≤ p.2.1.length →
    (encPartialColoring (((descentStep F)^[i] (p, [])).1)).length ≤
      c * ((encPartialColoring p).length + 1) ^ d

end Power2ModuleSVP.ColoringRuntime

namespace Power2ModuleSVP.ColoringRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

 theorem descent_frames_length (F : PartialColoringInput → List ℚ) (p : PartialColoringInput)
    (i : ℕ) : (((descentStep F)^[i] (p, [])).2).length ≤ i := by
  have hs (s : RecursionStack) : (descentStep F s).2.length ≤ s.2.length + 1 := by
    unfold descentStep
    split_ifs <;> simp
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (hs _).trans (Nat.add_le_add_right ih 1)

 theorem descent_frame_mem (F : PartialColoringInput → List ℚ) (p : PartialColoringInput)
    (i : ℕ) (frame : PartialColoringInput)
    (hf : frame ∈ ((descentStep F)^[i] (p, [])).2) :
    ∃ j < i, frame = ((descentStep F)^[j] (p, [])).1 := by
  induction i with
  | zero => simp at hf
  | succ i ih =>
    rw [Function.iterate_succ_apply'] at hf
    unfold descentStep at hf
    split_ifs at hf
    · rcases List.mem_cons.mp hf with he | hm
      · exact ⟨i, by omega, he⟩
      · obtain ⟨j, hj, he⟩ := ih hm
        exact ⟨j, by omega, he⟩
    · obtain ⟨j, hj, he⟩ := ih hf
      exact ⟨j, by omega, he⟩

 theorem descent_polytime_of_input_bound (F : PartialColoringInput → List ℚ)
    (hF : ComputableTidilyInPolyTime F encPartialColoring (encList encColoringRational))
    (hsize : RecursiveInputEncodingHypothesis F) :
    ComputableTidilyInPolyTime (descent F) encPartialColoring encRecursionStack := by
  obtain ⟨c, d, hb⟩ := hsize.input_bound
  let B := fun p : PartialColoringInput => c * ((encPartialColoring p).length + 1) ^ d
  have hB : PolyBounded (fun p => (encPartialColoring p).length) B :=
    PolyBounded.of_forall_le c d (fun _ => le_rfl)
  have hr : ComputableTidilyInPolyTime (fun p : PartialColoringInput => p.2.1.length)
      encPartialColoring encUnary := by unfold encPartialColoring; fun_prop
  unfold descent
  apply iterate hr (by unfold encRecursionStack; fun_prop) (descentStep_polytime F hF)
    (((hB.mul (.const 2)).add (((hB.mul (.const 2)).add (.const 1)).mul hr.polyBounded)).add (.const 1))
  intro p i hi
  have hcur := hb p i hi
  have hframes : (encList encPartialColoring (((descentStep F)^[i] (p, [])).2)).length ≤
      (2 * B p + 1) * p.2.1.length := by
    have hm : ∀ frame ∈ ((descentStep F)^[i] (p, [])).2,
        (encPartialColoring frame).length ≤ B p := by
      intro frame hf
      obtain ⟨j, hj, rfl⟩ := descent_frame_mem F p i frame hf
      exact hb p j (by omega)
    exact (length_encList_le encPartialColoring _ hm).trans (by
      simpa [Nat.mul_comm] using
        Nat.mul_le_mul_right (2 * B p + 1) ((descent_frames_length F p i).trans hi))
  simp only [encRecursionStack, length_encPair]
  dsimp [B] at *
  nlinarith [hcur, hframes]

private theorem input_dimension_le_encoding (p : PartialColoringInput) :
    p.2.1.length ≤ (encPartialColoring p).length := by
  have hx := length_le_length_encList encColoringRational p.2.1
  have hp := length_le_encPair_left (encList encColoringRational)
    (encList encColoringRational) p.2
  have hi := length_le_encPair_right (encList (encList encColoringRational))
    (encPair (encList encColoringRational) (encList encColoringRational)) p
  exact hx.trans (hp.trans hi)

private theorem sign_word_encoding_le (y : List ℚ)
    (hy : ∀ q ∈ y, q = -1 ∨ q = 1) :
    (encList encColoringRational y).length ≤ 13 * y.length := by
  have h := length_encList_le encColoringRational y (b := 6) (by
    intro q hq
    rcases hy q hq with rfl | rfl <;>
      norm_num [encColoringRational, length_encPair, length_encIntBin, encNat_apply,
        Nat.size_eq_bits_len])
  simpa [Nat.mul_comm] using h

 theorem recursionSafeAssemble_encoding_le (F : PartialColoringInput → List ℚ)
    (p : PartialColoringInput) (z : List ℚ) :
    (encList encColoringRational (recursionSafeAssemble F p z)).length ≤
      13 * (encPartialColoring p).length := by
  have hs := sign_word_encoding_le _ (recursionSafeAssemble_signs F p z)
  have hl : (recursionSafeAssemble F p z).length = p.2.1.length := by
    simp [recursionSafeAssemble]
  rw [hl] at hs
  exact hs.trans (Nat.mul_le_mul_left _ (input_dimension_le_encoding p))

private theorem assemble_fold_encoding_le (F : PartialColoringInput → List ℚ)
    (frames : List PartialColoringInput) (z : List ℚ) (B : ℕ)
    (hf : ∀ frame ∈ frames, (encPartialColoring frame).length ≤ B)
    (hz : (encList encColoringRational z).length ≤ 13 * B) :
    (encList encColoringRational
      (frames.foldl (fun z frame => recursionSafeAssemble F frame z) z)).length ≤ 13 * B := by
  induction frames generalizing z with
  | nil => exact hz
  | cons frame frames ih =>
    apply ih _ (fun f hf' => hf f (List.mem_cons_of_mem _ hf'))
    exact (recursionSafeAssemble_encoding_le F frame z).trans
      (Nat.mul_le_mul_left _ (hf frame (List.mem_cons_self)))

/-- A native full-recursion evaluator, conditional only on a uniform bound
for its actual recursive input encodings and the selected partial runtime. -/
 theorem fullColorListEvaluator_polytime_of_input_bound (F : PartialColoringInput → List ℚ)
    (hF : ComputableTidilyInPolyTime F encPartialColoring (encList encColoringRational))
    (hsize : RecursiveInputEncodingHypothesis F) :
    ComputableTidilyInPolyTime (fullColorListEvaluator F) encPartialColoring
      (encList encColoringRational) := by
  obtain ⟨c, d, hb⟩ := hsize.input_bound
  have hdes := descent_polytime_of_input_bound F hF hsize
  have hinit : ComputableTidilyInPolyTime
      (fun p => (descent F p).1.2.1.map nearestRationalSign)
      encPartialColoring (encList encColoringRational) :=
    malformedFallback_polytime.comp (hdes.fst')
  unfold fullColorListEvaluator
  apply foldl' (hdes.snd') hinit
    ((recursionSafeAssemble_polytime F hF).comp ((snd _ _).prod (fst _ _)))
    ((PolyBounded.const 13).mul (PolyBounded.of_forall_le c d (fun _ => le_rfl)))
  intro p i hi
  apply assemble_fold_encoding_le F _ _ (c * ((encPartialColoring p).length + 1) ^ d)
  · intro frame hf
    obtain ⟨j, hj, he⟩ := descent_frame_mem F p p.2.1.length frame (List.mem_of_mem_take hf)
    rw [he]
    exact hb p j (by omega)
  · have hs := sign_word_encoding_le ((descent F p).1.2.1.map nearestRationalSign) (by
      intro q hq
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hq
      exact nearestRationalSign_isSign q)
    simp only [List.length_map] at hs
    exact hs.trans (by
      have hc := hb p p.2.1.length le_rfl
      have hd := input_dimension_le_encoding ((descent F p).1)
      dsimp [descent] at hd ⊢
      nlinarith)

end Power2ModuleSVP.ColoringRuntime
