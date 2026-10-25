import Power2ModuleSVP.ColoringNative2
import Mathlib.Data.List.Sort

/-! Native heavy-row sorting. Ties follow the original index, matching the
stable merge sort in the unchanged walk. Filter-based insertion has exactly
additive encoded accumulator growth. -/
namespace Power2ModuleSVP.ColoringRuntime

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD

/-- Descending weight, with original-index order at ties. -/
def weightOrder (w : List ℚ) (i j : ℕ) : Prop :=
  w.getD j 0 < w.getD i 0 ∨ (w.getD j 0 = w.getD i 0 ∧ i ≤ j)

instance (w : List ℚ) (i j : ℕ) : Decidable (weightOrder w i j) :=
  inferInstanceAs (Decidable (_ ∨ _))

private theorem weightOrder_total (w : List ℚ) (i j : ℕ) :
    weightOrder w i j ∨ weightOrder w j i := by
  unfold weightOrder
  rcases lt_trichotomy (w.getD j 0) (w.getD i 0) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total i j with hij | hji
    · exact Or.inl (Or.inr ⟨h, hij⟩)
    · exact Or.inr (Or.inr ⟨h.symm, hji⟩)
  · exact Or.inr (Or.inl h)

private theorem weightOrder_trans (w : List ℚ) (i j k : ℕ)
    (hij : weightOrder w i j) (hjk : weightOrder w j k) : weightOrder w i k := by
  unfold weightOrder at *
  rcases hij with hij | ⟨hij, hij'⟩ <;> rcases hjk with hjk | ⟨hjk, hjk'⟩
  · exact Or.inl (lt_trans hjk hij)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨hjk.trans hij, hij'.trans hjk'⟩

private theorem weightOrder_antisymm (w : List ℚ) (i j : ℕ)
    (hij : weightOrder w i j) (hji : weightOrder w j i) : i = j := by
  unfold weightOrder at *
  rcases hij with hij | ⟨hij, hij'⟩ <;> rcases hji with hji | ⟨hji, hji'⟩
  · linarith
  · linarith
  · linarith
  · omega

instance weightOrderTotal (w : List ℚ) : Std.Total (weightOrder w) :=
  ⟨weightOrder_total w⟩
instance weightOrderTrans (w : List ℚ) : IsTrans ℕ (weightOrder w) :=
  ⟨weightOrder_trans w⟩
instance weightOrderAntisymm (w : List ℚ) : Std.Antisymm (weightOrder w) :=
  ⟨weightOrder_antisymm w⟩

/-- On sorted inputs the two filters split the prefix and suffix at the
insertion point. On arbitrary inputs they still partition every element. -/
def insertWeight (w : List ℚ) (xs : List ℕ) (a : ℕ) : List ℕ :=
  xs.filter (fun b => !decide (weightOrder w a b)) ++
    a :: xs.filter (fun b => decide (weightOrder w a b))

@[fun_prop] theorem weightOrder_polytime :
    ComputableTidilyInPolyTime
      (fun p : (List ℚ × ℕ) × ℕ => decide (weightOrder p.1.1 p.1.2 p.2))
      (encPair (encPair (encList encColoringRational) encUnary) encUnary) encBool := by
  have hi : ComputableTidilyInPolyTime (fun p : (List ℚ × ℕ) × ℕ => p.1.1.getD p.1.2 0)
      (encPair (encPair (encList encColoringRational) encUnary) encUnary) encColoringRational := by fun_prop
  have hj : ComputableTidilyInPolyTime (fun p : (List ℚ × ℕ) × ℕ => p.1.1.getD p.2 0)
      (encPair (encPair (encList encColoringRational) encUnary) encUnary) encColoringRational := by fun_prop
  have he := decide_eq' hj hi
  have hn : ComputableTidilyInPolyTime (fun p : (List ℚ × ℕ) × ℕ => decide (p.1.2 ≤ p.2))
      (encPair (encPair (encList encColoringRational) encUnary) encUnary) encBool := by fun_prop
  exact decide_or (lt_polytime.comp (hj.prod hi)) (decide_and he hn)

attribute [local irreducible] weightOrder insertWeight

/-- Native insertion for an arbitrary certified comparison. Keeping the
comparison abstract also keeps elaboration independent of rational internals. -/
theorem filterInsertWith_polytime {σ : Type} (encS : σ ↪ List Bool)
    (test : σ → ℕ → ℕ → Bool)
    (htest : ComputableTidilyInPolyTime
      (fun p : (σ × ℕ) × ℕ => test p.1.1 p.1.2 p.2)
      (encPair (encPair encS encUnary) encUnary) encBool) :
    ComputableTidilyInPolyTime
      (fun p : (σ × List ℕ) × ℕ =>
        p.1.2.filter (fun b => !test p.1.1 p.2 b) ++
          p.2 :: p.1.2.filter (fun b => test p.1.1 p.2 b))
      (encPair (encPair encS (encList encUnary)) encUnary) (encList encUnary) := by
  let encP := encPair (encPair encS (encList encUnary)) encUnary
  have hx : ComputableTidilyInPolyTime (fun p : (σ × List ℕ) × ℕ => p.1.2)
      encP (encList encUnary) := by dsimp [encP]; fun_prop
  have ha : ComputableTidilyInPolyTime (fun p : (σ × List ℕ) × ℕ => p.2)
      encP encUnary := by dsimp [encP]; fun_prop
  have hkey : ComputableTidilyInPolyTime
      (fun p : ((σ × List ℕ) × ℕ) × ℕ => ((p.1.1.1, p.1.2), p.2))
      (encPair encP encUnary) (encPair (encPair encS encUnary) encUnary) := by
    dsimp [encP]
    fun_prop
  have hc : ComputableTidilyInPolyTime
      (fun p : ((σ × List ℕ) × ℕ) × ℕ => test p.1.1.1 p.1.2 p.2)
      (encPair encP encUnary) encBool :=
    (htest.comp hkey).of_enc_eq (fun _ => rfl)
  have hneg := filterWithInput (test := fun (p : (σ × List ℕ) × ℕ) (b : ℕ) => !test p.1.1 p.2 b) hx (bool_not.comp hc)
  have hpos := filterWithInput (test := fun (p : (σ × List ℕ) × ℕ) (b : ℕ) => test p.1.1 p.2 b) hx hc
  exact listAppend' hneg (cons' ha hpos)

theorem insertWeight_polytime :
    ComputableTidilyInPolyTime
      (fun p : (List ℚ × List ℕ) × ℕ => insertWeight p.1.1 p.1.2 p.2)
      (encPair (encPair (encList encColoringRational) (encList encUnary)) encUnary)
      (encList encUnary) := by
  have h := filterInsertWith_polytime (encList encColoringRational)
    (fun w a b => decide (weightOrder w a b)) weightOrder_polytime
  exact h.of_enc_eq (fun p => congrArg (encList encUnary) (by rw [insertWeight]))

private theorem insertWeight_eq_orderedInsert (w : List ℚ) (a : ℕ)
    (xs : List ℕ) (hs : xs.Pairwise (weightOrder w)) :
    insertWeight w xs a = List.orderedInsert (weightOrder w) a xs := by
  induction xs with
  | nil => simp [insertWeight, List.orderedInsert]
  | cons b xs ih =>
    obtain ⟨hb, hxs⟩ := List.pairwise_cons.mp hs
    by_cases hab : weightOrder w a b
    · have hall : ∀ c ∈ b :: xs, weightOrder w a c := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hab
        · exact weightOrder_trans w a b c hab (hb c hc)
      have hyes : (b :: xs).filter (fun c => decide (weightOrder w a c)) = b :: xs := by
        exact List.filter_eq_self.mpr (by intro c hc; simpa using hall c hc)
      have hno : (b :: xs).filter (fun c => !decide (weightOrder w a c)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro c hc
        simp [hall c hc]
      rw [insertWeight, hyes, hno]
      simpa using (List.orderedInsert_cons_of_le (r := weightOrder w) xs hab).symm
    · simp only [insertWeight, List.filter_cons, hab, decide_false, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, List.cons_append]
      rw [List.orderedInsert_of_not_le (r := weightOrder w) xs hab]
      apply congrArg (List.cons b)
      rw [← ih hxs, insertWeight]

private theorem filter_encoding_partition (xs : List ℕ) (p : ℕ → Bool) :
    (encList encUnary (xs.filter p)).length +
      (encList encUnary (xs.filter (fun n => !p n))).length =
        (encList encUnary xs).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases hp : p a <;>
      simp [hp, encList_cons, length_frame, encUnary_apply] at * <;> omega

theorem insertWeight_encoding (w : List ℚ) (xs : List ℕ) (a : ℕ) :
    (encList encUnary (insertWeight w xs a)).length =
      (encList encUnary xs).length + 2 * a + 1 := by
  have h := filter_encoding_partition xs (fun b => decide (weightOrder w a b))
  simp only [insertWeight, encList_append, List.length_append,
    encList_cons, length_frame, encUnary_apply, List.length_replicate]
  omega

def sortWeights (w : List ℚ) : List ℕ :=
  (List.range w.length).reverse.foldl (insertWeight w) []

private theorem sortWeights_eq_insertionSort (w : List ℚ) :
    sortWeights w = List.insertionSort (weightOrder w) (List.range w.length) := by
  have h (xs : List ℕ) : xs.foldr (fun a xs => insertWeight w xs a) [] =
      List.insertionSort (weightOrder w) xs := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      simp only [List.foldr_cons, ih, List.insertionSort_cons]
      exact insertWeight_eq_orderedInsert w a _ (List.pairwise_insertionSort _ _)
  rw [sortWeights, ← List.foldr_eq_foldl_reverse]
  exact h _

@[fun_prop] theorem sortWeights_polytime :
    ComputableTidilyInPolyTime sortWeights (encList encColoringRational)
      (encList encUnary) := by
  unfold sortWeights
  apply foldlWith_of_bounded_growth (encP := encList encColoringRational)
    (encA := encUnary) (encL := encList encUnary) (encB := encList encUnary)
    (id' (encIn := encList encColoringRational))
    (by fun_prop) (const []) insertWeight_polytime
    (growth := fun w => 2 * w.length + 1)
  · exact ((PolyBounded.const 2).mul (by
      simpa only [encUnary_apply, List.length_replicate] using
        (length_list encColoringRational).polyBounded_length)).add (.const 1)
  · intro w state a ha
    have ha' : a < w.length := List.mem_range.mp (List.mem_reverse.mp ha)
    rw [insertWeight_encoding]
    omega

private theorem stable_range_sort (w : List ℚ) :
    (List.range w.length).mergeSort (fun i j => decide (w.getD j 0 ≤ w.getD i 0)) =
      (List.range w.length).mergeSort (fun i j => decide (weightOrder w i j)) := by
  let le := fun i j : ℕ => decide (w.getD j 0 ≤ w.getD i 0)
  have hdiag (a : ℕ × ℕ) (ha : a ∈ (List.range w.length).zipIdx) : a.1 = a.2 := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    simp
  have hm := List.map_mergeSort (l := (List.range w.length).zipIdx)
    (r := List.zipIdxLE le) (s := fun i j => decide (weightOrder w i j))
    (f := Prod.fst) (by
      intro a ha b hb
      have ha' := hdiag a ha
      have hb' := hdiag b hb
      by_cases hab : w.getD b.1 0 ≤ w.getD a.1 0
      · by_cases hba : w.getD a.1 0 ≤ w.getD b.1 0
        · have he := le_antisymm hab hba
          have hw : weightOrder w a.1 b.1 ↔ a.2 ≤ b.2 := by
            unfold weightOrder
            rw [he]
            simp only [lt_self_iff_false, true_and, false_or]
            rw [ha', hb']
          simp only [List.zipIdxLE, le, hab, hba, decide_true, ite_true]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          exact hw.symm
        · have hlt : w.getD b.1 0 < w.getD a.1 0 := by linarith
          have hw : weightOrder w a.1 b.1 := by unfold weightOrder; exact Or.inl hlt
          simp only [List.zipIdxLE, le, hab, hba, decide_true, decide_false,
            Bool.false_eq_true, ite_true, ite_false, hw]
      · have hn : ¬weightOrder w a.1 b.1 := by
          unfold weightOrder
          rintro (h | ⟨h, _⟩) <;> apply hab <;> linarith
        simp only [List.zipIdxLE, le, hab, decide_false, Bool.false_eq_true, ite_false, hn])
  have hstable := List.mergeSort_zipIdx (l := List.range w.length) (le := le)
  rw [hm] at hstable
  simpa only [List.zipIdx_map_fst] using hstable.symm

theorem sortWeights_eq_mergeSort (w : List ℚ) :
    sortWeights w =
      (List.range w.length).mergeSort (fun i j => decide (w.getD j 0 ≤ w.getD i 0)) := by
  rw [sortWeights_eq_insertionSort, stable_range_sort]
  exact (List.mergeSort_eq_insertionSort (weightOrder w) _).symm

end Power2ModuleSVP.ColoringRuntime
