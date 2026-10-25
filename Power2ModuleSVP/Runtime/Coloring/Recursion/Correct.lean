import Power2ModuleSVP.Runtime.Coloring.Recursion.Program

/-!
# Correct

Semantic checks for the native list full-recursion evaluator.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open Coloring ColoringNative
open Turing.MultiTapeTM
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem range_map_ofFn {α : Type} (r : ℕ) (f : ℕ → α) :
    (List.range r).map f = List.ofFn (fun j : Fin r => f j) := by
  apply List.ext_getElem <;> simp

private theorem ofFn_read (l : List ℚ) :
    List.ofFn (readColoringVector l.length l) = l := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [readColoringVector, List.getD_eq_getElem?_getD, hj]

private theorem nearest_ofFn_read (l : List ℚ) :
    List.ofFn (fun j : Fin l.length => nearestRationalSign (readColoringVector l.length l j)) =
      l.map nearestRationalSign := by
  simpa only [List.map_ofFn, Function.comp_def] using
    congrArg (List.map nearestRationalSign) (ofFn_read l)

 theorem canonicalColoringInput_spec (p : PartialColoringInput) :
    canonicalColoringInput p = partialColoringInput
      (fun i : Fin p.1.length => fun j : Fin p.2.1.length => (p.1.getD i []).getD j 0)
      (readColoringVector p.2.1.length p.2.1)
      (readColoringVector p.1.length p.2.2) := by
  unfold canonicalColoringInput partialColoringInput
  apply Prod.ext
  · apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [List.getD_eq_getElem?_getD, range_map_ofFn]
  · simp only [range_map_ofFn, ofFn_read]
    rfl


 theorem fullColor_canonical (F : PartialColoringInput → List ℚ) (p : PartialColoringInput) :
    fullColor F (canonicalColoringInput p) = fullColor F p := by
  rw [canonicalColoringInput_spec, fullColor_on_input]
  rfl

 theorem recursionAssemble_signs_eq_safe (F : PartialColoringInput → List ℚ)
    (p : PartialColoringInput) (z : List ℚ)
    (hlen : z.length = (ExplicitRecursion.activeIndices p.2.1.length (recursivePoint F p)).length)
    (hsign : ∀ q ∈ z, q = -1 ∨ q = 1) :
    recursionSafeAssemble F p z = recursionAssemble F p z := by
  have he : (List.range (ExplicitRecursion.activeIndices p.2.1.length (recursivePoint F p)).length).map
      (fun j => nearestRationalSign (z.getD j 0)) = z := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      have hiz : i < z.length := hj
      simp only [List.getElem_map, List.getElem_range]
      have hz : z.getD i 0 = z[i] := by simp [List.getD_eq_getElem?_getD, hiz]
      rw [hz]
      rcases hsign z[i] (List.getElem_mem hiz) with h | h <;>
        simp [h, nearestRationalSign]
  simp only [recursionSafeAssemble, recursionAssemble, he]

end Power2ModuleSVP.ColoringRuntime

namespace Power2ModuleSVP.ColoringRuntime
open Coloring ColoringNative
open Turing.MultiTapeTM
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

 theorem recursionNext_spec (F : PartialColoringInput → List ℚ) (p : PartialColoringInput) :
    recursionNext F p =
      let y := readColoringVector p.2.1.length (F (canonicalColoringInput p))
      let A := activeSet y
      partialColoringInput
        (fun i : Fin p.1.length => fun j : Fin A.card =>
          (p.1.getD i []).getD (embed A j) 0)
        (fun j => y (embed A j))
        (fun i => p.2.2.getD i 0 + 4) := by
  unfold recursionNext
  dsimp only
  unfold partialColoringInput
  apply Prod.ext
  · apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map, List.getElem_ofFn]
      rw [ExplicitRecursion.restrictList_spec]
      have hi' : i < p.1.length := by simpa using hi
      simp [List.getD_eq_getElem?_getD, hi', recursivePoint]
  · apply Prod.ext
    · exact ExplicitRecursion.restrictList_spec p.2.1.length
        (recursivePoint F p) (recursivePoint F p)
    · exact range_map_ofFn _ _

 theorem recursionProgress_spec (F : PartialColoringInput → List ℚ) (p : PartialColoringInput) :
    recursionProgress F p = true ↔
      64 < p.2.1.length ∧
      (activeSet (readColoringVector p.2.1.length (F (canonicalColoringInput p)))).card <
        p.2.1.length := by
  unfold recursionProgress
  rw [ExplicitRecursion.activeIndices_spec]
  simp only [recursivePoint, List.length_ofFn, Bool.and_eq_true_iff, decide_eq_true_eq]

 theorem fullColor_step (F : PartialColoringInput → List ℚ) (p : PartialColoringInput) :
    fullColor F p = if recursionProgress F p then
      recursionSafeAssemble F p (fullColor F (recursionNext F p))
      else p.2.1.map nearestRationalSign := by
  have hf := fullColor_signs F (recursionNext F p)
  have hp := recursionProgress_spec F p
  have hnext := recursionNext_spec F p
  by_cases h : recursionProgress F p = true
  · rw [ite_eq_left h]
    have hdim : (fullColor F (recursionNext F p)).length =
        (ExplicitRecursion.activeIndices p.2.1.length (recursivePoint F p)).length := by
      simp [fullColor_length, recursionNext]
    rw [recursionAssemble_signs_eq_safe F p _ hdim hf]
    rw [hnext, fullColor_on_input]
    unfold recursionAssemble
    rw [ExplicitRecursion.scatterList_spec]
    simp only [readColoringVector_ofFn]
    unfold recursivePoint
    have hr : ¬ p.2.1.length ≤ 64 := by have := (hp.mp h).1; omega
    unfold fullColor
    apply congrArg List.ofFn
    funext j
    rw [fullColorCore, ite_eq_right hr]
    rw [← canonicalColoringInput_spec p]
    rw [dite_eq_left (hp.mp h).2]
    rfl
  · have hn : recursionProgress F p = false := Bool.eq_false_of_not_eq_true h
    simp only [hn, Bool.false_eq_true]
    rw [← nearest_ofFn_read p.2.1]
    unfold fullColor
    apply congrArg List.ofFn
    funext j
    rw [fullColorCore]
    by_cases hsmall : p.2.1.length ≤ 64
    · rw [ite_eq_left hsmall]
    · rw [ite_eq_right hsmall, ← canonicalColoringInput_spec p]
      have hA : ¬ (activeSet (readColoringVector p.2.1.length
          (F (canonicalColoringInput p)))).card < p.2.1.length := by
        intro hprogress
        exact h (hp.mpr ⟨by omega, hprogress⟩)
      rw [dite_eq_right hA]

end Power2ModuleSVP.ColoringRuntime

namespace Power2ModuleSVP.ColoringRuntime
open Coloring ColoringNative
open Turing.MultiTapeTM
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def interpretStack (F : PartialColoringInput → List ℚ) (s : RecursionStack) : List ℚ :=
  s.2.foldl (fun z frame => recursionSafeAssemble F frame z) (fullColor F s.1)

private theorem interpret_descentStep (F : PartialColoringInput → List ℚ) (s : RecursionStack) :
    interpretStack F (descentStep F s) = interpretStack F s := by
  unfold descentStep
  split_ifs with h
  · simp only [interpretStack, List.foldl_cons]
    rw [fullColor_step F s.1, ite_eq_left h]
  · rfl

private theorem interpret_descent (F : PartialColoringInput → List ℚ) (p : PartialColoringInput)
    (i : ℕ) : interpretStack F ((descentStep F)^[i] (p, [])) = fullColor F p := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', interpret_descentStep, ih]

private theorem descent_terminal_aux (F : PartialColoringInput → List ℚ) (n : ℕ)
    (s : RecursionStack) (hs : s.1.2.1.length ≤ n) :
    recursionProgress F (((descentStep F)^[n] s).1) = false := by
  induction n generalizing s with
  | zero =>
    apply Bool.eq_false_of_not_eq_true
    intro h
    have := (recursionProgress_spec F s.1).mp h
    have hdim : s.1.2.1.length = 0 := Nat.eq_zero_of_le_zero hs
    omega
  | succ n ih =>
    by_cases h : recursionProgress F s.1 = true
    · rw [Function.iterate_succ_apply]
      apply ih
      have hlt := recursionNext_dimension_lt F s.1 h
      simpa [descentStep, h] using (show (recursionNext F s.1).2.1.length ≤ n by omega)
    · have hfalse : recursionProgress F s.1 = false := Bool.eq_false_of_not_eq_true h
      have hfixed : descentStep F s = s := by simp [descentStep, hfalse]
      rw [Function.iterate_fixed hfixed]
      exact hfalse

 theorem descent_terminal (F : PartialColoringInput → List ℚ) (p : PartialColoringInput) :
    recursionProgress F (descent F p).1 = false :=
  descent_terminal_aux F p.2.1.length (p, []) le_rfl

 theorem fullColorListEvaluator_eq (F : PartialColoringInput → List ℚ) :
    fullColorListEvaluator F = fullColor F := by
  funext p
  have he := interpret_descent F p p.2.1.length
  change (descent F p).2.foldl _ (fullColor F (descent F p).1) = _ at he
  rw [fullColor_step F (descent F p).1] at he
  simp only [descent_terminal F p, Bool.false_eq_true] at he
  exact he

 theorem fullColoringNative_of_recursive_input_bound (F : PartialColoringInput → List ℚ)
    (hF : Turing.MultiTapeTM.ComputableTidilyInPolyTime F encPartialColoring
      (encList encColoringRational)) (hsize : RecursiveInputEncodingHypothesis F) :
    FullColoringNativeHypothesis F := by
  constructor
  rw [← fullColorListEvaluator_eq F]
  exact fullColorListEvaluator_polytime_of_input_bound F hF hsize

 theorem fullColor_partialColor_native_of_recursive_input_bound
    (hF : PartialColoringAlg.PartialColoringNativeHypothesis)
    (hsize : RecursiveInputEncodingHypothesis PartialColoringAlg.partialColor) :
    FullColoringNativeHypothesis PartialColoringAlg.partialColor :=
  fullColoringNative_of_recursive_input_bound _ hF.polytime hsize

end Power2ModuleSVP.ColoringRuntime
