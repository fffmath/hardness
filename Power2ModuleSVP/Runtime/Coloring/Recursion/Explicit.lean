import Power2ModuleSVP.Runtime.Coloring.Recursion.Lists

/-!
# Explicit

Explicit-dimension finite-list operations avoid changing dependent vector
indices when a partial output is reified, including malformed outputs.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime.ExplicitRecursion
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def fixedIndices (r : ℕ) (y : List ℚ) : List ℕ :=
  ((List.range r).filter fun j =>
    decide (y.getD j 0 = -1 ∨ y.getD j 0 = 1)).take (r - r / 2)

def activeIndices (r : ℕ) (y : List ℚ) : List ℕ :=
  (List.range r).filter fun j => !(fixedIndices r y).any (fun k => decide (k = j))

def scatterList (r : ℕ) (p : List ℚ × List ℚ) : List ℚ :=
  let active := activeIndices r p.1
  (List.range r).map fun j =>
    if active.any (fun k => decide (k = j)) then
      p.2.getD (activeRank (active, j)) 0 else p.1.getD j 0

@[fun_prop] theorem fixedIndices_polytime :
    ComputableTidilyInPolyTime (fun p : ℕ × List ℚ => fixedIndices p.1 p.2)
      (encPair encUnary (encList encColoringRational)) (encList encUnary) := by
  unfold fixedIndices
  apply listTakeWithInput
  · apply filterWithInput (range.comp (fst _ _))
    have hg : ComputableTidilyInPolyTime (fun p : (ℕ × List ℚ) × ℕ => p.1.2.getD p.2 0)
        (encPair (encPair encUnary (encList encColoringRational)) encUnary) encColoringRational := by fun_prop
    exact decide_or (decide_eq' hg (.const (-1))) (decide_eq' hg (.const 1))
  · fun_prop

@[fun_prop] theorem activeIndices_polytime :
    ComputableTidilyInPolyTime (fun p : ℕ × List ℚ => activeIndices p.1 p.2)
      (encPair encUnary (encList encColoringRational)) (encList encUnary) := by
  unfold activeIndices
  apply filterWithInput (range.comp (fst _ _))
  apply bool_not.comp
  apply anyWithInput (fixedIndices_polytime.comp (fst _ _))
  fun_prop

@[fun_prop] theorem scatterList_polytime :
    ComputableTidilyInPolyTime (fun p : ℕ × (List ℚ × List ℚ) => scatterList p.1 p.2)
      (encPair encUnary (encPair (encList encColoringRational) (encList encColoringRational)))
      (encList encColoringRational) := by
  unfold scatterList
  apply mapWithInput (range.comp (fst _ _))
  have ha : ComputableTidilyInPolyTime
      (fun p : (ℕ × (List ℚ × List ℚ)) × ℕ => activeIndices p.1.1 p.1.2.1)
      (encPair (encPair encUnary (encPair (encList encColoringRational) (encList encColoringRational))) encUnary)
      (encList encUnary) := by fun_prop
  have ht := anyWithInput (test := fun (p : (ℕ × (List ℚ × List ℚ)) × ℕ) k => decide (k = p.2))
    ha (by fun_prop)
  apply ht.cond <;> fun_prop

@[simp] theorem scatterList_length (r : ℕ) (p : List ℚ × List ℚ) :
    (scatterList r p).length = r := by simp [scatterList]

 theorem activeIndices_length_le (r : ℕ) (y : List ℚ) :
    (activeIndices r y).length ≤ r := by
  exact (List.length_filter_le _ _).trans (by simp)

 theorem activeIndices_sorted (r : ℕ) (y : List ℚ) : (activeIndices r y).Pairwise (· < ·) := by
  exact List.pairwise_lt_range.filter _

 theorem fixedIndices_sorted (r : ℕ) (y : List ℚ) : (fixedIndices r y).Pairwise (· < ·) := by
  exact (List.pairwise_lt_range.filter _).take

end Power2ModuleSVP.ColoringRuntime.ExplicitRecursion

namespace Power2ModuleSVP.ColoringRuntime.ExplicitRecursion
open Coloring

private theorem sort_values_pairwise {r : ℕ} (s : Finset (Fin r)) :
    ((s.sort (· ≤ ·)).map Fin.val).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  exact (s.sortedLT_sort).pairwise

private theorem sign_sort_values (r : ℕ) (y : List ℚ) :
    ((signSet (readColoringVector r y)).sort (· ≤ ·)).map Fin.val =
      (List.range r).filter (fun j => decide (y.getD j 0 = -1 ∨ y.getD j 0 = 1)) := by
  apply (sort_values_pairwise _).eq_of_mem_iff (List.pairwise_lt_range.filter _)
  intro n
  simp only [List.mem_map, Finset.mem_sort, List.mem_filter, List.mem_range,
    decide_eq_true_eq, signSet,
    readColoringVector]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.isLt, by simpa [signSet] using hj⟩
  · rintro ⟨hn, hsign⟩
    exact ⟨⟨n, hn⟩, by simpa [signSet, List.getD_eq_getElem?_getD, hn] using hsign, rfl⟩

 theorem fixedIndices_mem_iff (r : ℕ) (y : List ℚ) (j : Fin r) :
    j.val ∈ fixedIndices r y ↔ j ∈ fixedSet (readColoringVector r y) := by
  unfold fixedIndices fixedSet
  rw [← sign_sort_values, ← List.map_take]
  simp only [List.mem_map, List.mem_toFinset]
  constructor
  · rintro ⟨k, hk, he⟩
    have : k = j := Fin.ext he
    simpa [this] using hk
  · intro hj
    exact ⟨j, hj, rfl⟩

 theorem activeIndices_mem_iff (r : ℕ) (y : List ℚ) (j : Fin r) :
    j.val ∈ activeIndices r y ↔ j ∈ activeSet (readColoringVector r y) := by
  have ha : ((fixedIndices r y).any (fun k => decide (k = j.val))) = true ↔
      j.val ∈ fixedIndices r y := by simp [List.any_eq_true]
  simp only [activeIndices, List.mem_filter, List.mem_range]
  rw [show ((!(fixedIndices r y).any fun k => decide (k = j.val)) = true) ↔
      j.val ∉ fixedIndices r y by cases hb : ((fixedIndices r y).any fun k => decide (k = j.val)) <;> simp_all]
  simp [j.isLt, fixedIndices_mem_iff, activeSet]

/-- The concrete native active-list order is the order embedding used by
`fullColorCore`, not merely a permutation of its coordinates. -/
 theorem activeIndices_spec (r : ℕ) (y : List ℚ) :
    activeIndices r y = List.ofFn (fun j : Fin (activeSet (readColoringVector r y)).card =>
      (embed (activeSet (readColoringVector r y)) j).val) := by
  let A := activeSet (readColoringVector r y)
  have he : List.ofFn (fun j : Fin A.card => (embed A j).val) =
      (A.sort (· ≤ ·)).map Fin.val := by
    rw [List.ofFn_eq_map]
    change (List.finRange A.card).map (Fin.val ∘ A.orderEmbOfFin rfl) = _
    rw [← List.map_map, Finset.listMap_orderEmbOfFin_finRange]
  rw [he]
  apply (activeIndices_sorted r y).eq_of_mem_iff (sort_values_pairwise A)
  intro n
  constructor
  · intro hn
    have hlt : n < r := (List.mem_filter.mp hn).1 |> List.mem_range.mp
    have hm := (activeIndices_mem_iff r y ⟨n, hlt⟩).mp hn
    exact List.mem_map.mpr ⟨⟨n, hlt⟩, (Finset.mem_sort _).mpr hm, rfl⟩
  · intro hn
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hn
    exact (activeIndices_mem_iff r y j).mpr ((Finset.mem_sort _).mp hj)

end Power2ModuleSVP.ColoringRuntime.ExplicitRecursion

namespace Power2ModuleSVP.ColoringRuntime.ExplicitRecursion
open Coloring

private theorem rank_at_sorted (l : List ℕ) (hl : l.Pairwise (· < ·))
    (i : Fin l.length) :
    (l.filter fun n => decide (n < l[i])).length = i.val := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons a l ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hl
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        have hz : l.filter (fun n => decide (n < a)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro n hn h
          exact (not_lt_of_ge (ha n hn).le) (of_decide_eq_true h)
        simp [hz]
      | succ n =>
        have hn' : n < l.length := by simpa using hn
        have hlt : a < l[n] := ha _ (List.getElem_mem hn')
        have hi := ih ht ⟨n, hn'⟩
        simpa [List.filter_cons, hlt] using hi

 theorem activeRank_embed (r : ℕ) (y : List ℚ)
    (j : Fin (activeSet (readColoringVector r y)).card) :
    activeRank (activeIndices r y,
      (embed (activeSet (readColoringVector r y)) j).val) = j.val := by
  have he := activeIndices_spec r y
  have hlen : (activeIndices r y).length = (activeSet (readColoringVector r y)).card := by
    rw [he, List.length_ofFn]
  have hi : j.val < (activeIndices r y).length := by rw [hlen]; exact j.isLt
  have hget : (activeIndices r y)[j.val] =
      (embed (activeSet (readColoringVector r y)) j).val := by
    simp [he]
  simpa [activeRank, hget] using rank_at_sorted (activeIndices r y)
    (activeIndices_sorted r y) ⟨j.val, hi⟩

 theorem restrictList_spec (r : ℕ) (y v : List ℚ) :
    restrictList (activeIndices r y, v) =
      List.ofFn (fun j : Fin (activeSet (readColoringVector r y)).card =>
        v.getD (embed (activeSet (readColoringVector r y)) j) 0) := by
  simp [restrictList, activeIndices_spec, List.map_ofFn, Function.comp_def]

 theorem scatterList_spec (r : ℕ) (y z : List ℚ) :
    scatterList r (y, z) = List.ofFn
      (extend (activeSet (readColoringVector r y))
        (readColoringVector r y)
        (readColoringVector (activeSet (readColoringVector r y)).card z)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hlt : i < r := by simpa using hi
    let j : Fin r := ⟨i, hlt⟩
    simp only [scatterList, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    change (if (activeIndices r y).any (fun k => decide (k = i)) then
      z.getD (activeRank (activeIndices r y, i)) 0 else y.getD i 0) =
        extend (activeSet (readColoringVector r y))
          (readColoringVector r y)
          (readColoringVector (activeSet (readColoringVector r y)).card z) j
    by_cases hmem : j ∈ activeSet (readColoringVector r y)
    · have hn : i ∈ activeIndices r y := (activeIndices_mem_iff r y j).mpr hmem
      have ht : (activeIndices r y).any (fun k => decide (k = i)) = true := by
        simp only [List.any_eq_true, decide_eq_true_eq]
        exact ⟨i, hn, rfl⟩
      rw [ht, ite_eq_left rfl]
      let k := ((activeSet (readColoringVector r y)).orderIsoOfFin rfl).symm ⟨j, hmem⟩
      have hk : embed (activeSet (readColoringVector r y)) k = j := by
        exact congrArg Subtype.val (((activeSet (readColoringVector r y)).orderIsoOfFin rfl).apply_symm_apply ⟨j, hmem⟩)
      have hrank := activeRank_embed r y k
      rw [hk] at hrank
      rw [extend, dite_eq_left hmem]
      change z.getD (activeRank (activeIndices r y, i)) 0 = z.getD k.val 0
      simpa [j, k] using congrArg (fun n => z.getD n 0) hrank
    · have hn : i ∉ activeIndices r y := by
        intro hn
        exact hmem ((activeIndices_mem_iff r y j).mp hn)
      have ht : (activeIndices r y).any (fun k => decide (k = i)) = false := by
        simp only [List.any_eq_false]
        intro k hk he
        have he' : k = i := of_decide_eq_true he
        exact hn (he' ▸ hk)
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      simpa [j, readColoringVector] using
        (extend_outside (activeSet (readColoringVector r y))
          (readColoringVector r y) _ j hmem).symm

end Power2ModuleSVP.ColoringRuntime.ExplicitRecursion
