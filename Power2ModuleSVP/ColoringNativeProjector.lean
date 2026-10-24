import Power2ModuleSVP.ColoringNativeArithmetic

/-!
List implementations and native certificates for one materialized projector
stage. The correspondence theorem covers dependent and zero constraints.
A certificate for iterating the stages still needs a uniform denominator
bound for the resulting projector tables.
-/

namespace Power2ModuleSVP.ColoringRuntime

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open PartialColoringAlg
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
attribute [local irreducible] List.getD

abbrev DotInput := ℕ × (List ℚ × List ℚ)
def encDotInput : DotInput ↪ List Bool :=
  encPair encUnary (encPair (encList encColoringRational) (encList encColoringRational))

def dotPrefix (p : DotInput) : ℚ :=
  ((List.range p.1).map fun j => p.2.1.getD j 0 * p.2.2.getD j 0).sum

@[fun_prop] theorem dotPrefix_polytime :
    ComputableTidilyInPolyTime dotPrefix encDotInput encColoringRational := by
  unfold dotPrefix
  apply sum_polytime.comp
  apply mapWithInput (range.comp (by unfold encDotInput; fun_prop))
  unfold encDotInput
  fun_prop

private theorem map_range_eq_ofFn {α : Type} (r : ℕ) (f : ℕ → α) :
    (List.range r).map f = List.ofFn (fun j : Fin r => f j) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

theorem dotPrefix_ofFn {r : ℕ} (x y : Vec r) :
    dotPrefix (r, (List.ofFn x, List.ofFn y)) = dot x y := by
  simp [dotPrefix, map_range_eq_ofFn, List.sum_ofFn, dot, List.getD_eq_getElem?_getD]

abbrev ProjectorInput := ℕ × (List (List ℚ) × List ℚ)
def encProjectorInput : ProjectorInput ↪ List Bool :=
  encPair encUnary
    (encPair (encList (encList encColoringRational)) (encList encColoringRational))

/-- Materialize a table-vector product before reusing its entries. -/
def applyTable (p : ProjectorInput) : List ℚ :=
  (List.range p.1).map fun j => dotPrefix (p.1, (p.2.1.getD j [], p.2.2))

@[fun_prop] theorem applyTable_polytime :
    ComputableTidilyInPolyTime applyTable encProjectorInput (encList encColoringRational) := by
  unfold applyTable
  apply mapWithInput (range.comp (by unfold encProjectorInput; fun_prop))
  apply dotPrefix_polytime.comp
  unfold encProjectorInput encDotInput
  fun_prop

/-- One exact rank-one elimination stage, with the zero-residual case
handled by rational division's total value at zero. -/
def projectorStep (p : ProjectorInput) : List (List ℚ) :=
  let q := applyTable p
  let den := dotPrefix (p.1, (q, q))
  (List.range p.1).map fun j => (List.range p.1).map fun k =>
    (p.2.1.getD j []).getD k 0 - q.getD j 0 * q.getD k 0 / den

@[fun_prop] theorem projectorStep_polytime :
    ComputableTidilyInPolyTime projectorStep encProjectorInput
      (encList (encList encColoringRational)) := by
  have hq := applyTable_polytime
  have hd : ComputableTidilyInPolyTime
      (fun p : ProjectorInput => dotPrefix (p.1, (applyTable p, applyTable p)))
      encProjectorInput encColoringRational := by
    apply dotPrefix_polytime.comp
    unfold encDotInput encProjectorInput at *
    fun_prop
  unfold projectorStep
  apply mapWithInput (range.comp (by unfold encProjectorInput; fun_prop))
  apply mapWithInput (range.comp (by unfold encProjectorInput; fun_prop))
  have hp : ComputableTidilyInPolyTime (fun p : (ProjectorInput × ℕ) × ℕ => p.1.1)
      (encPair (encPair encProjectorInput encUnary) encUnary) encProjectorInput := by fun_prop
  have hj : ComputableTidilyInPolyTime (fun p : (ProjectorInput × ℕ) × ℕ => p.1.2)
      (encPair (encPair encProjectorInput encUnary) encUnary) encUnary := by fun_prop
  have hk : ComputableTidilyInPolyTime (fun p : (ProjectorInput × ℕ) × ℕ => p.2)
      (encPair (encPair encProjectorInput encUnary) encUnary) encUnary := by fun_prop
  have hT : ComputableTidilyInPolyTime (fun p : ProjectorInput => p.2.1)
      encProjectorInput (encList (encList encColoringRational)) := by
    unfold encProjectorInput
    fun_prop
  have hs := (listGetD (encA := encColoringRational) 0).comp
    (((listGetD (encA := encList encColoringRational) []).comp ((hT.comp hp).prod hj)).prod hk)
  have hjq := (listGetD (encA := encColoringRational) 0).comp ((hq.comp hp).prod hj)
  have hkq := (listGetD (encA := encColoringRational) 0).comp ((hq.comp hp).prod hk)
  exact (sub_polytime.comp (hs.prod (div_polytime.comp
    ((mul_polytime.comp (hjq.prod hkq)).prod (hd.comp hp))))).of_enc_eq fun _ => rfl

theorem applyTable_spec {r : ℕ} (T : List (List ℚ)) (a : Vec r) :
    applyTable (r, (T, List.ofFn a)) = List.ofFn (tableApply T a) := by
  simp only [applyTable, dotPrefix, map_range_eq_ofFn, List.sum_ofFn]
  congr 1
  funext j
  simp [PartialColoringAlg.tableApply, PartialColoringAlg.tableEntry,
    List.getD_eq_getElem?_getD]

/-- Exact agreement with the stage used by the committed projector program. -/
theorem projectorStep_spec {r : ℕ} (a : Vec r) (C : List (Vec r)) :
    projectorStep (r, (projectorTable C, List.ofFn a)) = projectorTable (a :: C) := by
  simp only [projectorStep, applyTable_spec]
  rw [dotPrefix_ofFn]
  simp only [projectorTable, map_range_eq_ofFn]
  congr 1
  funext j
  congr 1
  funext k
  simp [tableEntry, List.getD_eq_getElem?_getD]

/-- The native stage controls all its canonical numerator and denominator
bits. Iteration cannot use this bound recursively without further analysis. -/
theorem projectorStep_length_polyBounded :
    PolyBounded (fun p => (encProjectorInput p).length)
      (fun p => (encList (encList encColoringRational) (projectorStep p)).length) :=
  projectorStep_polytime.polyBounded_length

end Power2ModuleSVP.ColoringRuntime
