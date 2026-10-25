import Power2ModuleSVP.Runtime.Coloring.Step
import Power2ModuleSVP.Runtime.Coloring.Preparation
import Power2ModuleSVP.Coloring.Partial.Correct
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration

/-!
# Loop

The stopped walk as one captured native iteration. Its only loop-size
premise bounds the encoded prefixes of this particular evaluator.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open PartialColoringAlg
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD initialWeight dotPrefix normalizeList

/-- Prepare the ambient dimension and rows for a partial-coloring input. -/
def loopParameter (input : PartialColoringInput) : WalkParameter :=
  (input.2.1.length, prepareList (input.2.1.length, (input.1, input.2.2)))

/-- Number of stopped walk steps, with zero steps for fallback inputs. -/
def loopCount (input : PartialColoringInput) : ℕ :=
  if validInput input && !(loopParameter input).2.isEmpty then stepBudget input.2.1.length else 0

/-- Initial point and weights for the stopped walk, including fallback signs. -/
def loopInitial (input : PartialColoringInput) : ListState :=
  (if validInput input && !(loopParameter input).2.isEmpty then input.2.1
    else input.2.1.map nearestRationalSign,
   initializeList (loopParameter input))

/-- Evaluate the stopped partial-coloring walk on list data. -/
def partialList (input : PartialColoringInput) : List ℚ :=
  ((fun s => stoppedStep (loopParameter input, s))^[loopCount input] (loopInitial input)).1

/-- Native polynomial-time certificate for `loopParameter`. -/
@[fun_prop] theorem loopParameter_polytime :
    ComputableTidilyInPolyTime loopParameter encPartialColoring encWalkParameter := by
  have hr : ComputableTidilyInPolyTime (fun p : PartialColoringInput => p.2.1.length)
      encPartialColoring encUnary := by unfold encPartialColoring; fun_prop
  have ha := prepareList_polytime.comp
    (show ComputableTidilyInPolyTime
      (fun p : PartialColoringInput => (p.2.1.length, (p.1, p.2.2)))
      encPartialColoring encPreparation from by
        unfold encPartialColoring encPreparation; fun_prop)
  exact hr.prod ha

/-- Native polynomial-time certificate for `loopCount`. -/
@[fun_prop] theorem loopCount_polytime :
    ComputableTidilyInPolyTime loopCount encPartialColoring encUnary := by
  unfold loopCount
  have hp := loopParameter_polytime
  have he : ComputableTidilyInPolyTime
      (fun p : PartialColoringInput => (loopParameter p).2.isEmpty)
      encPartialColoring encBool := by
    exact (listIsEmpty' (encPair encColoringRational (encList encColoringRational))).comp hp.snd'
  have ht := bool_and.comp (validInput_polytime.prod (bool_not.comp he))
  apply ht.cond
  · exact stepBudget_polytime.comp (by unfold encPartialColoring; fun_prop)
  · exact .const 0

/-- Native polynomial-time certificate for `loopInitial`. -/
@[fun_prop] theorem loopInitial_polytime :
    ComputableTidilyInPolyTime loopInitial encPartialColoring encListState := by
  have hp := loopParameter_polytime
  have he : ComputableTidilyInPolyTime
      (fun p : PartialColoringInput => (loopParameter p).2.isEmpty)
      encPartialColoring encBool := by
    exact (listIsEmpty' (encPair encColoringRational (encList encColoringRational))).comp hp.snd'
  have ht := bool_and.comp (validInput_polytime.prod (bool_not.comp he))
  unfold loopInitial encListState
  exact (ht.cond (by unfold encPartialColoring; fun_prop)
    malformedFallback_polytime).prod (initializeList_polytime.comp hp)

/-- Interpret the prepared input rows as mathematical coloring constraints. -/
def preparedInputRows (input : PartialColoringInput) : List (Row input.2.1.length) :=
  prepareRows (fun i : Fin input.1.length => fun j => (input.1.getD i []).getD j 0)
    (fun i => input.2.2.getD i 0)

/-- The loop parameters encode the prepared mathematical input rows. -/
theorem loopParameter_read (input : PartialColoringInput) :
    loopParameter input = reifyRows (preparedInputRows input).get := by
  unfold loopParameter reifyRows
  rw [prepareList_read]
  congr 1
  have h : List.ofFn (preparedInputRows input).get = preparedInputRows input := by
    apply List.ext_getElem <;> simp
  simpa only [preparedInputRows, List.map_ofFn, Function.comp_def] using
    (congrArg (List.map (fun row : Row input.2.1.length =>
      (row.threshold, List.ofFn row.a))) h).symm

/-- The initial list state agrees with the mathematical initial state on active inputs. -/
theorem loopInitial_spec_of_active (input : PartialColoringInput)
    (hv : validInput input = true) (hne : (loopParameter input).2.isEmpty = false) :
    loopInitial input = reifyState
      (initialState (preparedInputRows input).get
        (fun j => input.2.1.getD j 0)) := by
  have hg : (validInput input && (!(loopParameter input).2.isEmpty)) = true := by simp [hv, hne]
  unfold loopInitial
  rw [ite_eq_left hg, loopParameter_read]
  simp only [reifyRows, initializeList_spec, reifyState, initialState]
  congr 1
  apply List.ext_getElem <;> simp [List.getD_eq_getElem?_getD]

/-- Polynomial encoding bound for every state of the stopped coloring walk. -/
structure StoppedWalkEncodingHypothesis : Prop where
  bound : ∃ c d : ℕ, ∀ input : PartialColoringInput, ∀ k ≤ loopCount input,
    (encListState ((fun s => stoppedStep (loopParameter input, s))^[k]
      (loopInitial input))).length ≤ c * ((encPartialColoring input).length + 1) ^ d

/-- This certifies the entire stopped walk, rather than one rational step. -/
theorem partialList_polytime (hD : CanonicalProjectorDenominatorHypothesis)
    (hH : HeavyIndicesNativeHypothesis) (hB : StoppedWalkEncodingHypothesis) :
    ComputableTidilyInPolyTime partialList encPartialColoring (encList encColoringRational) := by
  obtain ⟨c, d, hb⟩ := hB.bound
  have hi := iterateWith (par := loopParameter) (count := loopCount) (init := loopInitial)
    (step := fun par state => stoppedStep (par, state))
    loopParameter_polytime loopCount_polytime loopInitial_polytime (stoppedStep_polytime hD hH)
    (PolyBounded.of_forall_le c d (fun _ => le_rfl)) hb
  exact hi.fst'

private theorem ofFn_getD {α : Type} (xs : List α) (d : α) :
    List.ofFn (fun i : Fin xs.length => xs.getD i d) = xs := by
  apply List.ext_getElem <;> simp [List.getD_eq_getElem?_getD]

/-- The list evaluator is the original program on every raw input. -/
theorem partialList_spec (input : PartialColoringInput) :
    partialList input = partialColor input := by
  let r := input.2.1.length
  let m := input.1.length
  let V : Fin m → Vec r := fun i j => (input.1.getD i []).getD j 0
  let x : Vec r := fun j => input.2.1.getD j 0
  let c : Fin m → ℚ := fun i => input.2.2.getD i 0
  let rows := prepareRows V c
  have hp : loopParameter input = reifyRows rows.get := by
    unfold loopParameter reifyRows
    rw [prepareList_read]
    congr 1
    have h : List.ofFn rows.get = rows := by
      apply List.ext_getElem <;> simp
    simpa only [List.map_ofFn, Function.comp_def] using
      (congrArg (List.map (fun row : Row r => (row.threshold, List.ofFn row.a))) h).symm
  have hx : List.ofFn x = input.2.1 := ofFn_getD _ _
  have hsign : List.ofFn (fun j => nearestRationalSign (x j)) =
      input.2.1.map nearestRationalSign := by
    rw [← hx, List.map_ofFn]
    rfl
  by_cases hv : validInput input = true
  · have hpc : partialColor input = partialColorCore r m V x c := by
      unfold partialColor
      rw [ite_eq_left hv]
    by_cases he : rows.isEmpty = true
    · have hpe : (loopParameter input).2.isEmpty = true := by
        rw [hp]
        simpa [reifyRows] using he
      have hg : (validInput input && (!(loopParameter input).2.isEmpty)) = false := by
        simp [hv, hpe]
      have hc : loopCount input = 0 := by simp [loopCount, hg]
      have hi : (loopInitial input).1 = input.2.1.map nearestRationalSign := by
        unfold loopInitial
        rw [ite_eq_right (by simp [hg])]
      unfold partialList
      rw [hc]
      change (loopInitial input).1 = partialColor input
      rw [hi, hpc]
      change input.2.1.map nearestRationalSign =
        if rows.isEmpty then List.ofFn (fun j => nearestRationalSign (x j))
          else List.ofFn (run rows.get x).x
      rw [ite_eq_left he, hsign]
    · have hne : (loopParameter input).2.isEmpty = false := by
        rw [hp]
        simpa [reifyRows] using he
      have hinit := loopInitial_spec_of_active input hv hne
      change loopInitial input = reifyState (initialState rows.get x) at hinit
      have hc : loopCount input = stepBudget r := by simp [loopCount, hv, hne, r]
      unfold partialList
      rw [hc, hinit, hp, stopped_iterate_spec, hpc]
      change List.ofFn (run rows.get x).x =
        if rows.isEmpty then List.ofFn (fun j => nearestRationalSign (x j))
          else List.ofFn (run rows.get x).x
      rw [ite_eq_right he]
  · have hf : validInput input = false := Bool.eq_false_iff.mpr hv
    simp [partialList, loopCount, loopInitial, hf, partialColor]

theorem partialColorNative_of_components
    (hD : CanonicalProjectorDenominatorHypothesis)
    (hH : HeavyIndicesNativeHypothesis) (hB : StoppedWalkEncodingHypothesis) :
    PartialColoringNativeHypothesis := by
  refine ⟨(partialList_polytime hD hH hB).of_enc_eq fun input => ?_⟩
  exact congrArg (encList encColoringRational) (partialList_spec input).symm

end Power2ModuleSVP.ColoringRuntime
