import Power2ModuleSVP.Runtime.Coloring.CoordinateBounds

/-!
# Constraint Data

Reification of the finite constraint data. Sorting is separated from
rational linear algebra: its premise concerns only a list of weights and
returns a list of indices.

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
attribute [local irreducible] List.getD

abbrev WalkParameter := ℕ × QuadraticRows
def encWalkParameter : WalkParameter ↪ List Bool := encPair encUnary encQuadraticRows
abbrev ListState := List ℚ × List ℚ
def encListState : ListState ↪ List Bool :=
  encPair (encList encColoringRational) (encList encColoringRational)
abbrev WalkInput := WalkParameter × ListState
def encWalkInput : WalkInput ↪ List Bool := encPair encWalkParameter encListState

/-- Exact original heavy-row order, including the comparison tie rule. -/
def heavyIndices (p : ℕ × List ℚ) : List ℕ :=
  ((List.range p.2.length).mergeSort
    (fun i j => decide (p.2.getD j 0 ≤ p.2.getD i 0))).take ((p.1 + 7) / 8)

structure HeavyIndicesNativeHypothesis : Prop where
  polytime : ComputableTidilyInPolyTime heavyIndices
    (encPair encUnary (encList encColoringRational)) (encList encUnary)

def dampingList (p : WalkParameter) (i : ℕ) : ℚ :=
  1 - 4 * stepSize p.1 ^ 2 * (p.2.getD i (0, [])).1 ^ 2 / p.1

def constraintHead (p : WalkInput) : List ℚ :=
  (List.range p.1.1).map fun j =>
    ((List.range p.1.2.length).map fun i =>
      p.2.2.getD i 0 * dampingList p.1 i * (p.1.2.getD i (0, [])).1 *
        (p.1.2.getD i (0, [])).2.getD j 0).sum

def coordinateList (p : ℕ × ℕ) : List ℚ :=
  (List.range p.1).map fun j => if j = p.2 then 1 else 0

def constraintsList (p : WalkInput) : List (List ℚ) :=
  let fixed := ((List.range p.1.1).filter fun j =>
    p.2.1.getD j 0 = -1 ∨ p.2.1.getD j 0 = 1).map fun j => coordinateList (p.1.1, j)
  let heavy := (heavyIndices (p.1.1, p.2.2)).map fun i => (p.1.2.getD i (0, [])).2
  let small := ((List.range p.1.2.length).filter fun i => (p.1.2.getD i (0, [])).1 ≤ 1).map
    fun i => (p.1.2.getD i (0, [])).2
  constraintHead p :: (fixed ++ heavy ++ small)

def quadraticList (p : WalkInput) : QuadraticRows :=
  (List.range p.1.2.length).map fun i =>
    (p.2.2.getD i 0 * (p.1.2.getD i (0, [])).1 ^ 2, (p.1.2.getD i (0, [])).2)

def directionDataList (p : WalkInput) : DirectionInput :=
  (p.1.1, (constraintsList p, quadraticList p))

theorem heavyIndices_spec {r m : ℕ} (w : Fin m → ℚ) :
    heavyIndices (r, List.ofFn w) = (heavyRows (r := r) w).map Fin.val := by
  unfold heavyIndices heavyRows
  simp only [List.length_ofFn]
  symm
  rw [List.map_take, List.map_mergeSort (s := fun i j : ℕ =>
    decide ((List.ofFn w).getD j 0 ≤ (List.ofFn w).getD i 0))]
  · simp
  · intro i _ j _
    simp [List.getD_eq_getElem?_getD]

private theorem range_map_ofFn {α : Type} (r : ℕ) (f : ℕ → α) :
    (List.range r).map f = List.ofFn (fun j : Fin r => f j) := by
  apply List.ext_getElem <;> simp

private theorem range_filter_map {α : Type} (n : ℕ) (p : ℕ → Bool) (f : ℕ → α) :
    ((List.range n).filter p).map f =
      ((List.finRange n).filter (fun i : Fin n => p i.val)).map (fun i : Fin n => f i.val) := by
  have h : (List.finRange n).map Fin.val = List.range n := by simp
  conv_lhs => rw [← h, List.filter_map, List.map_map]
  rfl

theorem directionDataList_spec {r m : ℕ} (a : Fin m → Row r) (s : State r m) :
    directionDataList ((r, List.ofFn fun i => ((a i).threshold, List.ofFn (a i).a)),
      (List.ofFn s.x, List.ofFn s.w)) = walkDirectionInput a s := by
  have hcoordinate (j : Fin r) : coordinateList (r, j) = List.ofFn (coordinate j) := by
    rw [coordinateList, range_map_ofFn]
    congr 1
    funext k
    simp [coordinate, Fin.ext_iff]
  have hfixed :
      (((List.range r).filter fun j => (List.ofFn s.x).getD j 0 = -1 ∨
        (List.ofFn s.x).getD j 0 = 1).map fun j => coordinateList (r, j)) =
      (((List.finRange r).filter fun j => s.x j = -1 ∨ s.x j = 1).map coordinate).map List.ofFn := by
    rw [range_filter_map]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Fin.isLt,
      ↓reduceDIte, Option.getD_some, List.map_map, Function.comp_def, hcoordinate]
  have hsmall :
      (((List.range m).filter fun i =>
        ((List.ofFn fun i => ((a i).threshold, List.ofFn (a i).a)).getD i (0, [])).1 ≤ 1).map
        fun i => ((List.ofFn fun i => ((a i).threshold, List.ofFn (a i).a)).getD i (0, [])).2) =
      (((List.finRange m).filter fun i => (a i).threshold ≤ 1).map fun i => (a i).a).map List.ofFn := by
    rw [range_filter_map]
    simp [List.getD_eq_getElem?_getD, List.map_map, Function.comp_def]
  have hhead : constraintHead ((r, List.ofFn fun i => ((a i).threshold, List.ofFn (a i).a)),
      (List.ofFn s.x, List.ofFn s.w)) =
      List.ofFn (fun j => ∑ i, s.w i * damping a i * (a i).threshold * (a i).a j) := by
    simp [constraintHead, range_map_ofFn, List.getD_eq_getElem?_getD,
      List.sum_ofFn, dampingList, damping]
  unfold directionDataList walkDirectionInput
  apply Prod.ext
  · rfl
  apply Prod.ext
  · simp only [constraintsList, constraints,
      List.length_ofFn, hhead, hfixed, hsmall, heavyIndices_spec,
      List.map_cons, List.map_append, List.map_map, Function.comp_def]
    congr 2
    simp [List.getD_eq_getElem?_getD]
  · simp [quadraticList, quadraticRows,
      range_map_ofFn, List.getD_eq_getElem?_getD, Function.comp_def]

end Power2ModuleSVP.ColoringRuntime
