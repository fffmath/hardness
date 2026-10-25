import Power2ModuleSVP.Runtime.Coloring.Components

/-!
# Cached Projector

A native certificate for the whole materialized projector, conditional
only on a uniform algebraic size bound for its canonical tables.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open PartialColoringAlg
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev ProjectorBatchInput := ℕ × List (List ℚ)
def encProjectorBatch : ProjectorBatchInput ↪ List Bool :=
  encPair encUnary (encList (encList encColoringRational))

def readConstraints (r : ℕ) (rows : List (List ℚ)) : List (Vec r) :=
  rows.map fun row j => row.getD j 0

def identityTable (r : ℕ) : List (List ℚ) :=
  (List.range r).map fun j => (List.range r).map fun k => if k = j then 1 else 0

def trimRow (p : ℕ × List ℚ) : List ℚ :=
  (List.range p.1).map fun j => p.2.getD j 0

def batchStep (r : ℕ) (T : List (List ℚ)) (row : List ℚ) : List (List ℚ) :=
  projectorStep (r, (T, trimRow (r, row)))

def projectorBatch (p : ProjectorBatchInput) : List (List ℚ) :=
  p.2.reverse.foldl (batchStep p.1) (identityTable p.1)

private theorem range_map_ofFn {α : Type} (r : ℕ) (f : ℕ → α) :
    (List.range r).map f = List.ofFn (fun j : Fin r => f j) := by
  apply List.ext_getElem <;> simp

theorem identityTable_spec (r : ℕ) : identityTable r = projectorTable ([] : List (Vec r)) := by
  simp only [identityTable, projectorTable, range_map_ofFn]
  congr 1
  funext j
  congr 1
  funext k
  simp [coordinate, Fin.ext_iff]

theorem trimRow_spec (r : ℕ) (row : List ℚ) :
    trimRow (r, row) = List.ofFn (fun j : Fin r => row.getD j 0) :=
  range_map_ofFn r _

theorem batchStep_spec (r : ℕ) (C : List (Vec r)) (row : List ℚ) :
    batchStep r (projectorTable C) row =
      projectorTable ((fun j => row.getD j 0) :: C) := by
  unfold batchStep
  rw [trimRow_spec, projectorStep_spec]

/-- Every prefix accumulator is precisely a canonical projector table,
including dependent rows and raw rows of the wrong length. -/
theorem batch_fold_spec (r : ℕ) (rows : List (List ℚ)) (C : List (Vec r)) :
    rows.foldl (batchStep r) (projectorTable C) =
      projectorTable (readConstraints r rows.reverse ++ C) := by
  induction rows generalizing C with
  | nil => simp [readConstraints]
  | cons row rows ih =>
    rw [List.foldl_cons, batchStep_spec, ih]
    simp [readConstraints, List.reverse_cons, List.map_append, List.append_assoc]

theorem projectorBatch_spec (p : ProjectorBatchInput) :
    projectorBatch p = projectorTable (readConstraints p.1 p.2) := by
  unfold projectorBatch
  rw [identityTable_spec, batch_fold_spec]
  simp

@[fun_prop] theorem identityTable_polytime :
    ComputableTidilyInPolyTime identityTable encUnary
      (encList (encList encColoringRational)) := by
  unfold identityTable
  apply mapWithInput range
  apply mapWithInput (range.comp (fst _ _))
  fun_prop

@[fun_prop] theorem trimRow_polytime :
    ComputableTidilyInPolyTime trimRow (encPair encUnary (encList encColoringRational))
      (encList encColoringRational) := by
  unfold trimRow
  apply mapWithInput (range.comp (fst _ _))
  fun_prop

@[fun_prop] theorem batchStep_polytime :
    ComputableTidilyInPolyTime
      (fun p : (ℕ × List (List ℚ)) × List ℚ => batchStep p.1.1 p.1.2 p.2)
      (encPair encProjectorBatch (encList encColoringRational))
      (encList (encList encColoringRational)) := by
  unfold batchStep
  apply projectorStep_polytime.comp
  unfold encProjectorInput encProjectorBatch
  fun_prop

/-- The projector encoding contract is a uniform size inequality.
It has no native-machine or coloring-correctness field. The sublist clause
covers all intermediate tables in the actual reverse elimination order. -/
structure CanonicalProjectorSizeHypothesis : Prop where
  size_bound : ∃ coefficient degree : ℕ,
    ∀ (p : ProjectorBatchInput) (rows : List (List ℚ)), rows.Sublist p.2 →
      (encList (encList encColoringRational)
        (projectorTable (readConstraints p.1 rows))).length ≤
          coefficient * ((encProjectorBatch p).length + 1) ^ degree

/-- A canonical-table height bound suffices for the entire projector loop,
not merely one elimination stage. -/
theorem projectorBatch_polytime_of_size (h : CanonicalProjectorSizeHypothesis) :
    ComputableTidilyInPolyTime projectorBatch encProjectorBatch
      (encList (encList encColoringRational)) := by
  obtain ⟨c, d, hb⟩ := h.size_bound
  unfold projectorBatch
  apply foldlWith (encP := encUnary) (encA := encList encColoringRational)
    (encL := encList (encList encColoringRational))
    (encB := encList (encList encColoringRational))
    (B := fun p => c * ((encProjectorBatch p).length + 1) ^ d)
    (by unfold encProjectorBatch; fun_prop)
    (by unfold encProjectorBatch; fun_prop)
    (by unfold encProjectorBatch; fun_prop)
    batchStep_polytime
    (PolyBounded.of_forall_le c d (fun _ => le_rfl))
  intro p i hi
  rw [identityTable_spec, batch_fold_spec]
  simp only [List.append_nil]
  apply hb
  have hs := (List.take_sublist i p.2.reverse).reverse
  simpa using hs

end Power2ModuleSVP.ColoringRuntime
