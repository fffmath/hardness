import Power2ModuleSVP.Runtime.Repair.Candidates

/-!
# Rows

Polynomial-time ordered row variables and reverse greedy packing.

Paper: `paper/power2svp.pdf`, Section 5 (Theorems 3–4 and deterministic anchor repair).
-/
namespace Power2ModuleSVP.AnchorRepairRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD

abbrev RowInput := (ℕ × List ℤ) × ℕ
abbrev encRowInput := encPair encSupportInput encUnary

def rowVars (a : RowInput) : List ℕ :=
  (List.range a.1.1).filter fun k =>
    (supportList a.1.1 a.1.2).any fun j => decide ((a.2+a.1.1-j)%a.1.1 = k)

@[fun_prop] theorem rowVars_polytime :
    ComputableTidilyInPolyTime rowVars encRowInput (encList encUnary) := by
  unfold rowVars
  apply filterWithInput (encA := encUnary)
  · unfold encRowInput encSupportInput
    fun_prop
  · apply anyWithInput (encA := encUnary)
    · exact supportList_polytime.comp ((fst _ _).comp (fst _ _))
    · apply ComputableTidilyInPolyTime.decide_eq'
        (encB := encUnary)
      · apply unary_mod.comp (g := fun x : (RowInput × ℕ) × ℕ =>
          (x.1.1.2 + x.1.1.1.1 - x.2, x.1.1.1.1))
        unfold encRowInput encSupportInput
        fun_prop
      · unfold encRowInput encSupportInput
        fun_prop

theorem rowVars_eq (a : RowInput) : rowVars a =
    AnchorTests.rowVariables a.1.1 (AnchorTests.multiplierSupport a.1.1 a.1.2) a.2 := by
  apply (List.pairwise_lt_range.filter _).eq_of_mem_iff
    (Finset.sortedLT_sort _).pairwise
  intro k
  change (k ∈ (List.range a.1.1).filter _) ↔
    k ∈ AnchorTests.rowVariables a.1.1
      (AnchorTests.multiplierSupport a.1.1 a.1.2) a.2
  simp only [List.mem_filter, List.mem_range, List.any_eq_true,
    decide_eq_true_eq, AnchorTests.mem_rowVariables, AnchorTests.rowFlags,
    Finset.mem_image]
  constructor
  · rintro ⟨_, j, hj, he⟩
    exact ⟨j, by simpa only [← supportList_eq, List.mem_toFinset] using hj, he⟩
  · rintro ⟨j, hj, he⟩
    have hd : 0 < a.1.1 := by
      have hjlt := (Finset.mem_filter.mp hj).1
      have := Finset.mem_range.mp hjlt
      omega
    refine ⟨?_, j, ?_, he⟩
    · rw [← he]
      exact Nat.mod_lt _ hd
    · simpa only [← supportList_eq, List.mem_toFinset] using hj

def rowsDisjoint (a : (ℕ × List ℤ) × (ℕ × ℕ)) : Bool :=
  (rowVars (a.1, a.2.1)).all fun j =>
    !((rowVars (a.1, a.2.2)).any fun k => decide (j = k))

abbrev encDisjointInput := encPair encSupportInput (encPair encUnary encUnary)

@[fun_prop] theorem rowsDisjoint_polytime :
    ComputableTidilyInPolyTime rowsDisjoint encDisjointInput encBool := by
  unfold rowsDisjoint
  apply allWithInput (encA := encUnary)
  · exact rowVars_polytime.comp (by unfold encRowInput encDisjointInput; fun_prop)
  · apply bool_not.comp
    apply anyWithInput (encA := encUnary)
    · apply rowVars_polytime.comp
      unfold encRowInput encDisjointInput
      fun_prop
    · unfold encDisjointInput
      fun_prop

theorem rowsDisjoint_spec (a : (ℕ × List ℤ) × (ℕ × ℕ)) :
    rowsDisjoint a = true ↔
      Disjoint (AnchorTests.rowFlags a.1.1 (AnchorTests.multiplierSupport a.1.1 a.1.2) a.2.1)
        (AnchorTests.rowFlags a.1.1 (AnchorTests.multiplierSupport a.1.1 a.1.2) a.2.2) := by
  simp only [rowsDisjoint, List.all_eq_true, Bool.not_eq_true', List.any_eq_false,
    decide_eq_true_eq, rowVars_eq, AnchorTests.mem_rowVariables,
    Finset.disjoint_left]
  constructor
  · intro h j hj hk
    exact h j hj j hk rfl
  · intro h j hj k hk he
    subst k
    exact h hj hk

def selectStep (a : ℕ × List ℤ) (rest : List ℕ) (i : ℕ) : List ℕ :=
  if rest.all (fun j => rowsDisjoint (a, (i,j))) then i :: rest else rest

def rowsList (a : ℕ × List ℤ) : List ℕ :=
  (List.range a.1).reverse.foldl (selectStep a) []

abbrev encSelectStep := encPair (encPair encSupportInput (encList encUnary)) encUnary

@[fun_prop] theorem selectStep_polytime : ComputableTidilyInPolyTime
    (fun a : ((ℕ × List ℤ) × List ℕ) × ℕ => selectStep a.1.1 a.1.2 a.2)
    encSelectStep (encList encUnary) := by
  unfold selectStep
  have ht : ComputableTidilyInPolyTime
      (fun a : ((ℕ × List ℤ) × List ℕ) × ℕ =>
        a.1.2.all (fun j => rowsDisjoint (a.1.1, (a.2,j)))) encSelectStep encBool := by
    apply allWithInput (encA := encUnary)
    · unfold encSelectStep
      fun_prop
    · apply rowsDisjoint_polytime.comp
      unfold encDisjointInput encSelectStep
      fun_prop
  apply ht.ite'
  · unfold encSelectStep
    fun_prop
  · unfold encSelectStep
    fun_prop

@[fun_prop] theorem rowsList_polytime :
    ComputableTidilyInPolyTime rowsList encSupportInput (encList encUnary) := by
  unfold rowsList
  apply foldlWith_of_bounded_growth (encA := encUnary) (encP := encSupportInput)
    (growth := fun a => (encSupportInput a).length * 2 + 1)
    id' (by unfold encSupportInput; fun_prop) (const []) selectStep_polytime
    (PolyBounded.self.mul (.const 2) |>.add (.const 1))
  intro a rest i hi
  have hi' : i < a.1 := List.mem_range.mp (by simpa using hi)
  have hd : a.1 ≤ (encSupportInput a).length :=
    by simpa using length_le_encPair_left encUnary (encList encIntBin) a
  unfold selectStep
  split_ifs
  · simp only [encList_cons, List.length_append, length_frame,
      encUnary_apply, List.length_replicate]
    omega
  · omega

theorem rowsList_eq (a : ℕ × List ℤ) :
    rowsList a = AnchorTests.selectedRows a.1 a.2 := by
  have hs (rest : List ℕ) (i : ℕ) : selectStep a rest i =
      if rest.all (fun j => decide (Disjoint
        (AnchorTests.rowFlags a.1 (AnchorTests.multiplierSupport a.1 a.2) i)
        (AnchorTests.rowFlags a.1 (AnchorTests.multiplierSupport a.1 a.2) j)))
      then i :: rest else rest := by
    unfold selectStep
    have ht : (rest.all fun j => rowsDisjoint (a,(i,j))) =
        (rest.all fun j => decide (Disjoint
          (AnchorTests.rowFlags a.1 (AnchorTests.multiplierSupport a.1 a.2) i)
          (AnchorTests.rowFlags a.1 (AnchorTests.multiplierSupport a.1 a.2) j))) := by
      apply List.all_congr rfl
      intro j
      exact Bool.eq_iff_iff.mpr (by simp only [rowsDisjoint_spec, decide_eq_true_eq])
    rw [ht]
  unfold rowsList AnchorTests.selectedRows
  rw [List.foldl_reverse]
  have he (rows : List ℕ) : rows.foldr (fun i rest => selectStep a rest i) [] =
      AnchorTests.greedySelect
        (AnchorTests.rowFlags a.1 (AnchorTests.multiplierSupport a.1 a.2)) rows := by
    induction rows with
    | nil => rfl
    | cons i rows ih => rw [List.foldr_cons, ih, hs, AnchorTests.greedySelect]
  exact he _

end Power2ModuleSVP.AnchorRepairRuntime
