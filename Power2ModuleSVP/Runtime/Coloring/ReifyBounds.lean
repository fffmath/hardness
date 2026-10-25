import Power2ModuleSVP.Runtime.Coloring.Constraints

/-!
# Reify Bounds

Sorting-free size accounting: supply the heavy indices as data.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open PartialColoringAlg
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD

/-- Walk input paired with a supplied list of heavy-row indices. -/
abbrev ReifyInput := WalkInput × List ℕ
/-- Binary encoding for `ReifyInput` runtime data. -/
def encReifyInput : ReifyInput ↪ List Bool := encPair encWalkInput (encList encUnary)

/-- List the coordinate constraints corresponding to already fixed coordinates. -/
def fixedRowsList (p : WalkInput) : List (List ℚ) :=
  ((List.range p.1.1).filter fun j =>
    p.2.1.getD j 0 = -1 ∨ p.2.1.getD j 0 = 1).map fun j => coordinateList (p.1.1, j)

/-- Reify direction data using a supplied heavy-row ordering. -/
def directionGivenHeavy (p : ReifyInput) : DirectionInput :=
  (p.1.1.1, (constraintHead p.1 ::
    (fixedRowsList p.1 ++ p.2.map (fun i => (p.1.1.2.getD i (0, [])).2) ++
      ((List.range p.1.1.2.length).filter fun i => (p.1.1.2.getD i (0, [])).1 ≤ 1).map
        (fun i => (p.1.1.2.getD i (0, [])).2)), quadraticList p.1))

/-- Native polynomial-time certificate for `fixedRowsList`. -/
@[fun_prop] theorem fixedRowsList_polytime :
    ComputableTidilyInPolyTime fixedRowsList encWalkInput
      (encList (encList encColoringRational)) := by
  unfold fixedRowsList
  apply mapWithInput
  · apply filterWithInput (range.comp (by unfold encWalkInput encWalkParameter; fun_prop))
    exact signTest_polytime.comp (show ComputableTidilyInPolyTime
      (fun p : WalkInput × ℕ => p.1.2.1.getD p.2 0)
      (encPair encWalkInput encUnary) encColoringRational from by
        unfold encWalkInput encListState; fun_prop)
  · exact coordinateList_polytime.comp (show ComputableTidilyInPolyTime
      (fun p : WalkInput × ℕ => (p.1.1.1, p.2))
      (encPair encWalkInput encUnary) (encPair encUnary encUnary) from by
        unfold encWalkInput encWalkParameter; fun_prop)

/-- Native polynomial-time certificate for `directionGivenHeavy`. -/
@[fun_prop] theorem directionGivenHeavy_polytime :
    ComputableTidilyInPolyTime directionGivenHeavy encReifyInput encDirectionInput := by
  have hhead := constraintHead_polytime.comp (fst encWalkInput (encList encUnary))
  have hfixed := fixedRowsList_polytime.comp (fst encWalkInput (encList encUnary))
  have hq := quadraticList_polytime.comp (fst encWalkInput (encList encUnary))
  have hheavy : ComputableTidilyInPolyTime
      (fun p : ReifyInput => p.2.map (fun i => (p.1.1.2.getD i (0, [])).2))
      encReifyInput (encList (encList encColoringRational)) := by
    apply mapWithInput (encA := encUnary) (by unfold encReifyInput; fun_prop)
    have hout := walkRowAt_polytime.snd'.comp (show ComputableTidilyInPolyTime
      (fun p : ReifyInput × ℕ => (p.1.1.1, p.2))
      (encPair encReifyInput encUnary) (encPair encWalkParameter encUnary) from by
        unfold encReifyInput encWalkInput; fun_prop)
    exact hout.of_enc_eq fun _ => congrArg (encList encColoringRational) (by rfl)
  have hsmall : ComputableTidilyInPolyTime
      (fun p : ReifyInput =>
        ((List.range p.1.1.2.length).filter fun i => (p.1.1.2.getD i (0, [])).1 ≤ 1).map
        (fun i => (p.1.1.2.getD i (0, [])).2))
      encReifyInput (encList (encList encColoringRational)) := by
    apply mapWithInput (encA := encUnary)
    · apply filterWithInput (range.comp (by
        unfold encReifyInput encWalkInput encWalkParameter encQuadraticRows; fun_prop))
      have ht := walkRowAt_polytime.fst'.comp (show ComputableTidilyInPolyTime
        (fun p : ReifyInput × ℕ => (p.1.1.1, p.2))
        (encPair encReifyInput encUnary) (encPair encWalkParameter encUnary) from by
          unfold encReifyInput encWalkInput; fun_prop)
      exact le_polytime' ht (.const 1)
    · have hout := walkRowAt_polytime.snd'.comp (show ComputableTidilyInPolyTime
        (fun p : ReifyInput × ℕ => (p.1.1.1, p.2))
        (encPair encReifyInput encUnary) (encPair encWalkParameter encUnary) from by
          unfold encReifyInput encWalkInput; fun_prop)
      exact hout.of_enc_eq fun _ => congrArg (encList encColoringRational) (by rfl)
  have hc := cons' hhead ((hfixed.listAppend' hheavy).listAppend' hsmall)
  have hr : ComputableTidilyInPolyTime (fun p : ReifyInput => p.1.1.1)
      encReifyInput encUnary := by unfold encReifyInput encWalkInput encWalkParameter; fun_prop
  have hout := hr.prod (hc.prod hq)
  exact hout.of_enc_eq fun _ => congrArg encDirectionInput (by rfl)

/-- The supplied heavy-row order gives the exact reified walk direction data. -/
theorem directionGivenHeavy_spec (p : WalkInput) :
    directionGivenHeavy (p, heavyIndices (p.1.1, p.2.2)) = directionDataList p := rfl

/-- Sorting changes neither membership nor length; both suffice for the
unary index-list encoding bound. -/
theorem heavyIndices_encoding (r : ℕ) (w : List ℚ) :
    (encList encUnary (heavyIndices (r, w))).length ≤ (2 * w.length + 1) * w.length := by
  have hmem : ∀ i ∈ heavyIndices (r, w), i < w.length := by
    intro i hi
    have hi' := List.mem_of_mem_take hi
    have hp := List.mergeSort_perm (List.range w.length)
      (fun i j => decide (w.getD j 0 ≤ w.getD i 0))
    exact List.mem_range.mp (hp.mem_iff.mp hi')
  have hlen : (heavyIndices (r, w)).length ≤ w.length := by
    unfold heavyIndices
    exact (List.length_take_le' _ _).trans (by simp)
  have he := length_encList_le encUnary (heavyIndices (r, w)) (b := w.length)
    (fun i hi => by simpa using (hmem i hi).le)
  exact he.trans (by nlinarith)

end Power2ModuleSVP.ColoringRuntime
