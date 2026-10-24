import IdealCVP.Complexity.ExactCoverGadget
import IdealCVP.Complexity.SatToMasked

/-! # Correctness-only SAT to list X3C

This reference uses finite-type equivalences. Its correctness is proved, but
no native runtime certificate for this enumeration is asserted.
-/
namespace IdealCVP
open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

namespace X3COccurrences

def positions (S : MaskedSys) (j : Fin S.cols) : List ℕ :=
  (List.range S.rows.length).filter fun i => (S.rows.getD i []).getD j.val false

def sizes (S : MaskedSys) (j : Fin S.cols) : ℕ := (positions S j).length

theorem positions_bound (S : MaskedSys) (j : Fin S.cols) {i : ℕ}
    (hi : i ∈ positions S j) : i < S.rows.length := by
  exact List.mem_range.mp (List.mem_filter.mp hi).1

def row (S : MaskedSys) (e : ExactCoverGadget.Edge (sizes S)) : Fin S.rows.length :=
  ⟨(positions S e.1)[e.2.val], positions_bound S e.1 (List.getElem_mem e.2.isLt)⟩

theorem sum_nodup (l : List ℕ) (hl : l.Nodup) (i : ℕ) (z : ℤ) :
    (∑ k : Fin l.length, if l[k.val] = i then z else 0) = if i ∈ l then z else 0 := by
  have hm : (l.map (fun a => if a = i then z else 0)).sum =
      ∑ k : Fin l.length, if l[k.val] = i then z else 0 := by
    have he := congrArg (fun xs : List ℕ => (xs.map (fun a => if a = i then z else 0)).sum)
      (List.ofFn_get l)
    simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def, List.get_eq_getElem] using he.symm
  rw [← hm, ← List.sum_toFinset _ hl]
  simp

theorem source_sum (S : MaskedSys) (v : Fin S.cols → Bool) (i : Fin S.rows.length) :
    (∑ e : ExactCoverGadget.Edge (sizes S),
      if row S e = i then bit (v e.1) else 0) =
      ∑ j, bit (S.toSystem.A i j) * bit (v j) := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ k : Fin (positions S j).length,
    if (⟨(positions S j)[k.val], positions_bound S j (List.getElem_mem k.isLt)⟩ :
      Fin S.rows.length) = i then bit (v j) else 0) = _
  simp only [Fin.ext_iff]
  rw [sum_nodup (positions S j) ((List.nodup_range).filter _) i.val]
  simp only [positions, List.mem_filter, List.mem_range, i.isLt, true_and]
  change (if S.toSystem.A i j = true then bit (v j) else 0) = _
  cases S.toSystem.A i j <;> simp

theorem solvable_iff (S : MaskedSys)
    (hb : ∀ i, S.toSystem.b i = true) (hμ : ∀ j, S.toSystem.μ j = true) :
    ExactCoverGadget.Solvable (sizes S) (row S) ↔ S.toSystem.HasSolution := by
  apply exists_congr
  intro v
  change (∀ i, (∑ e : ExactCoverGadget.Edge (sizes S),
    if row S e = i then bit (v e.1) else 0) = 1) ↔ _
  simp only [source_sum]
  change _ ↔ ((∀ j, v j = true → S.toSystem.μ j = true) ∧
    (fun i => (∑ j, bit (S.toSystem.A i j) * bit (v j)) - bit (S.toSystem.b i)) = 0)
  simp [hμ, hb, funext_iff, sub_eq_zero]

noncomputable def reduce (S : MaskedSys) : X3CList :=
  ExactCoverGadget.semanticList (sizes S) (row S)

theorem correct (S : MaskedSys) (hw : S.WellFormed)
    (hb : ∀ i, S.toSystem.b i = true) (hμ : ∀ j, S.toSystem.μ j = true) :
    reduce S ∈ X3CLang ↔ S.Feasible := by
  rw [reduce, ExactCoverGadget.semanticList_correct, solvable_iff S hb hμ]
  exact (and_iff_right hw).symm

end X3COccurrences

namespace SatToMasked

theorem reduce_wellFormed (φ : CNF ℕ) : (reduce φ).WellFormed := by
  unfold reduce
  split
  · exact denseSystem_wellFormed _ _
  · decide

theorem denseSystem_rhs_true (cs : List Column) (rs : List (List Column))
    (i : Fin (denseSystem cs rs).rows.length) : (denseSystem cs rs).toSystem.b i = true := by
  have hi : i.val < rs.length := by simpa [denseSystem, MaskedSys.rows] using i.isLt
  simp [MaskedSys.toSystem, MaskedSys.rhs, denseSystem, List.getD_eq_getElem?_getD, hi]

theorem denseSystem_mask_true (cs : List Column) (rs : List (List Column))
    (j : Fin (denseSystem cs rs).cols) : (denseSystem cs rs).toSystem.μ j = true := by
  have hj : j.val < cs.length := j.isLt
  simp [MaskedSys.toSystem, MaskedSys.mask, denseSystem, List.getD_eq_getElem?_getD, hj]

theorem reduce_rhs_true (φ : CNF ℕ) : ∀ i, (reduce φ).toSystem.b i = true := by
  by_cases h : (φ.all fun c => c.length == 3) = true
  · rw [show reduce φ = denseSystem (columns φ) (supports φ) from if_pos h]
    exact denseSystem_rhs_true _ _
  · rw [show reduce φ = noSystem from if_neg h]
    intro i
    have hi : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
    simp [MaskedSys.toSystem, MaskedSys.rhs, noSystem, hi]

theorem reduce_mask_true (φ : CNF ℕ) : ∀ j, (reduce φ).toSystem.μ j = true := by
  by_cases h : (φ.all fun c => c.length == 3) = true
  · rw [show reduce φ = denseSystem (columns φ) (supports φ) from if_pos h]
    exact denseSystem_mask_true _ _
  · rw [show reduce φ = noSystem from if_neg h]
    intro j
    have hj : j.val = 0 := by have := j.isLt; change j.val < 1 at this; omega
    simp [MaskedSys.toSystem, MaskedSys.mask, noSystem, hj]

end SatToMasked

/-- Correctness-only reference: the finite gadget applied to the SAT equations. -/
noncomputable def satToX3CSemantic (φ : CNF ℕ) : X3CList :=
  X3COccurrences.reduce (satToMasked φ)

theorem satToX3CSemantic_correct (φ : CNF ℕ) :
    φ ∈ ExactThreeSAT ↔ satToX3CSemantic φ ∈ X3CLang :=
  (satToMasked_correct φ).trans
    (X3COccurrences.correct _ (SatToMasked.reduce_wellFormed φ)
      (SatToMasked.reduce_rhs_true φ) (SatToMasked.reduce_mask_true φ)).symm

end IdealCVP
