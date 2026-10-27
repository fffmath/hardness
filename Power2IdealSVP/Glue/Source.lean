import Power2IdealSVP.Runtime.Construction
import Power2IdealSVP.Source.Labels

/-! # Executable source labels and the difference-set interface

The list program uses precisely the cubic labels of Lemma 1 on the normalized graph.
Its difference list is identified with the mathematical edge-difference set, and CLIQUE
is characterized by finite sets of integer positions with allowed positive differences.

Paper: `Power2IdealSVP/paper/power2-ideal-svp.txt`, Section 1.1, Lemma 1.
-/

namespace Power2IdealSVP.Glue

open Cslib.Complexity Power2IdealSVP.Runtime Power2IdealSVP.Source

/-- The runtime's natural difference list, viewed as a finite set of integers. -/
def differenceSet (x : Graph × ℕ) : Finset ℤ :=
  ((diffSet x).map (fun d => (d : ℤ))).toFinset

/-- The executable label at a valid vertex is the source-layer cubic label. -/
theorem graphLabel_eq_label (x : Graph × ℕ) (i : Fin (vertexCount x.1)) :
    (graphLabel x (i.val + 1) : ℤ) = label i := by
  simp [graphLabel, labelBase, label, index, base, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow]

/-- The largest executable label is the mathematical bound, including empty graphs. -/
theorem maxLabel_eq_labelBound (x : Graph × ℕ) :
    (maxLabel x : ℤ) = labelBound (vertexCount x.1) := by
  simp [maxLabel, graphLabel, labelBase, labelBound, base, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow]

/-- For an increasing runtime edge, the executable distance is the absolute label difference. -/
theorem edgeDifference_eq_abs (x : Graph × ℕ) (i j : Fin (vertexCount x.1))
    (hij : i.val < j.val) :
    (edgeDifference x (i.val, j.val) : ℤ) = |label i - label j| := by
  have hlt := graphLabel_strictMono x (Nat.add_lt_add_right hij 1)
  have hsub : graphLabel x (i.val + 1) - graphLabel x (j.val + 1) = 0 :=
    Nat.sub_eq_zero_of_le hlt.le
  rw [edgeDifference, hsub, zero_add, Nat.cast_sub hlt.le,
    graphLabel_eq_label, graphLabel_eq_label]
  have hl := Source.label_strictMono (show i < j from hij)
  rw [abs_of_neg (sub_neg.mpr hl)]
  omega

/-- Membership in the cast runtime difference set exposes its natural list entry. -/
theorem mem_differenceSet (x : Graph × ℕ) (d : ℤ) :
    d ∈ differenceSet x ↔ ∃ e ∈ diffSet x, (e : ℤ) = d := by
  simp [differenceSet, eq_comm]

/-- The runtime difference-list scan equals the edge differences of the normalized graph. -/
theorem differenceSet_eq_edgeDifferences (x : Graph × ℕ) :
    differenceSet x = edgeDifferences (normalGraph x.1) := by
  classical
  ext d
  rw [mem_differenceSet, edgeDifferences, mem_edgeDifferencesOf]
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := (mem_diffSet_iff x e).mp he
    obtain ⟨hi, hj, hlt, _⟩ := mem_normalEdges.mp hij
    let a : Fin (vertexCount x.1) := ⟨i, hi⟩
    let b : Fin (vertexCount x.1) := ⟨j, hj⟩
    exact ⟨a, b, (normalGraph_adj_iff a b).mpr (Or.inl hij),
      edgeDifference_eq_abs x a b hlt⟩
  · rintro ⟨i, j, hij, rfl⟩
    rcases (normalGraph_adj_iff i j).mp hij with he | he
    · refine ⟨edgeDifference x (i.val, j.val),
        (mem_diffSet_iff x _).mpr ⟨_, he, rfl⟩, ?_⟩
      exact edgeDifference_eq_abs x i j (mem_normalEdges.mp he).2.2.1
    · refine ⟨edgeDifference x (j.val, i.val),
        (mem_diffSet_iff x _).mpr ⟨_, he, rfl⟩, ?_⟩
      rw [edgeDifference_eq_abs x j i (mem_normalEdges.mp he).2.2.1, abs_sub_comm]

/-- Lemma 1 and its anchored converse over the executable difference list.
The lower bound two also covers the edge case; the reduction uses targets at least three. -/
theorem normalised_clique_iff_positions (x : Graph × ℕ) (hh : 2 ≤ x.2) :
    (∃ C : Finset (Fin (vertexCount x.1)),
      (normalGraph x.1).IsNClique x.2 C) ↔
    ∃ P : Finset ℤ, x.2 ≤ P.card ∧
      PositiveDifferences P (differenceSet x) ∧ 0 ∈ P := by
  rw [differenceSet_eq_edgeDifferences, ← clique_iff_positions _ hh]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, hC.card_eq.ge, hC.isClique⟩
  · rintro ⟨C, hc, hC⟩
    obtain ⟨S, hs, hcard⟩ := Finset.exists_subset_card_eq hc
    exact ⟨S, ⟨fun _ hi _ hj hij => hC (hs hi) (hs hj) hij, hcard⟩⟩

/-- CLIQUE's original declared-label encoding has exactly the runtime difference-set semantics. -/
theorem clique_iff_positions (x : Graph × ℕ) (hh : 2 ≤ x.2) :
    x ∈ Clique ↔ ∃ P : Finset ℤ, x.2 ≤ P.card ∧
      PositiveDifferences P (differenceSet x) ∧ 0 ∈ P := by
  rw [Runtime.normalised_clique_iff, normalised_clique_iff_positions x hh]

/-- An exact-cardinality, nonnegative anchored version useful for spin-gadget construction. -/
theorem clique_iff_positions_exact (x : Graph × ℕ) (hh : 2 ≤ x.2) :
    x ∈ Clique ↔ ∃ P : Finset ℤ, P.card = x.2 ∧
      PositiveDifferences P (differenceSet x) ∧ 0 ∈ P ∧
      ∀ p ∈ P, 0 ≤ p ∧ p ≤ (maxLabel x : ℤ) := by
  constructor
  · intro hx
    obtain ⟨C, hC⟩ := Runtime.normalised_clique_iff x |>.mp hx
    have hne : C.Nonempty := Finset.card_pos.mp (by rw [hC.card_eq]; omega)
    obtain ⟨P, hzero, hcard, hdiff, hbound⟩ :=
      clique_positions_nonneg (normalGraph x.1) hC.isClique hne
    refine ⟨P, hcard.trans hC.card_eq, ?_, hzero, ?_⟩
    · rwa [differenceSet_eq_edgeDifferences]
    · rwa [maxLabel_eq_labelBound]
  · rintro ⟨P, hcard, hdiff, hzero, _⟩
    exact (clique_iff_positions x hh).mpr ⟨P, hcard.ge, hdiff, hzero⟩

end Power2IdealSVP.Glue
