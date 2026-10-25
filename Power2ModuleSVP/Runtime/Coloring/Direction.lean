import Power2ModuleSVP.Runtime.Coloring.Column

/-!
# Direction

Once canonical projector denominators are bounded, native score
selection and normalization give a direction bound independent of the
current point's denominators.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open PartialColoringAlg ColoringNative
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Normalize a list vector using the canonical rational norm scale. -/
def normalizeList (p : ℕ × List ℚ) : List ℚ :=
  let scale := (normScale (dotPrefix (p.1, (p.2, p.2))))⁻¹
  (List.range p.1).map fun j => scale * p.2.getD j 0

/-- Native polynomial-time certificate for `normalizeList`. -/
@[fun_prop] theorem normalizeList_polytime :
    ComputableTidilyInPolyTime normalizeList (encPair encUnary (encList encColoringRational))
      (encList encColoringRational) := by
  unfold normalizeList
  apply mapWithInput (range.comp (fst _ _))
  fun_prop

private theorem range_map_ofFn {α : Type} (r : ℕ) (f : ℕ → α) :
    (List.range r).map f = List.ofFn (fun j : Fin r => f j) := by
  apply List.ext_getElem <;> simp

/-- List normalization agrees with the canonical vector normalization. -/
theorem normalizeList_spec (r : ℕ) (v : List ℚ) :
    normalizeList (r, v) =
      List.ofFn (PartialColoringAlg.normalize (fun j : Fin r => v.getD j 0)) := by
  simp [normalizeList, dotPrefix_read, range_map_ofFn, PartialColoringAlg.normalize,
    Pi.smul_def, smul_eq_mul]

/-- Ambient dimension, constraint rows, and weighted rows used for direction selection. -/
abbrev DirectionInput := ℕ × (List (List ℚ) × QuadraticRows)
/-- Binary encoding for `DirectionInput` runtime data. -/
def encDirectionInput : DirectionInput ↪ List Bool :=
  encPair encUnary (encPair (encList (encList encColoringRational)) encQuadraticRows)

/-- Select and normalize a projector column before choosing its sign. -/
def unorientedDirection (p : DirectionInput) : List ℚ :=
  normalizeList (p.1,
    bestColumnList ((p.1, p.2.2), projectorBatch (p.1, p.2.1)))

/-- Native polynomial-time certificate for `unorientedDirection`. -/
theorem unorientedDirection_polytime (h : CanonicalProjectorDenominatorHypothesis) :
    ComputableTidilyInPolyTime unorientedDirection encDirectionInput
      (encList encColoringRational) := by
  have ht : ComputableTidilyInPolyTime
      (fun p : DirectionInput => projectorBatch (p.1, p.2.1))
      encDirectionInput (encList (encList encColoringRational)) := by
    apply (projectorBatch_polytime_of_denominator h).comp
    unfold encDirectionInput encProjectorBatch
    fun_prop
  have hb : ComputableTidilyInPolyTime
      (fun p : DirectionInput => bestColumnList ((p.1, p.2.2), projectorBatch (p.1, p.2.1)))
      encDirectionInput (encList encColoringRational) := by
    apply bestColumnList_polytime.comp
    unfold encColumnInput encColumnParameter encDirectionInput
    fun_prop
  unfold unorientedDirection
  apply normalizeList_polytime.comp
  unfold encDirectionInput
  fun_prop

private theorem read_projectorTable {r : ℕ} (C : List (Vec r)) :
    readConstraints r (projectorTable C) = cachedColumns C := by
  have hshape : projectorTable C = List.ofFn (fun j : Fin r =>
      List.ofFn (fun k : Fin r => tableEntry (projectorTable C) j k)) := by
    cases C <;> simp [projectorTable, tableEntry, List.getD_eq_getElem?_getD]
  unfold readConstraints
  conv_lhs => rw [hshape]
  simp [List.map_ofFn, Function.comp_def, List.getD_eq_getElem?_getD, cachedColumns]

/-- The native data program computes the exact normalized candidate used
in the original direction, before its point-dependent sign is chosen. -/
theorem unorientedDirection_spec (p : DirectionInput) :
    unorientedDirection p = List.ofFn
      (PartialColoringAlg.normalize (bestColumn (readQuadraticRows p.1 p.2.2)
        (cachedColumns (readConstraints p.1 p.2.1)))) := by
  unfold unorientedDirection
  rw [normalizeList_spec]
  have hb : (fun j : Fin p.1 =>
      (bestColumnList ((p.1, p.2.2), projectorBatch (p.1, p.2.1))).getD j 0) =
      bestColumn (readQuadraticRows p.1 p.2.2)
        (readConstraints p.1 (projectorBatch (p.1, p.2.1))) :=
    bestColumnList_spec ((p.1, p.2.2), projectorBatch (p.1, p.2.1))
  rw [hb, projectorBatch_spec, read_projectorTable]

/-- A polynomial shared-denominator bound, uniform in the point used for
orientation. Coordinate denominator growth is therefore not fed back into
the arithmetic bound for subsequent directions. -/
theorem direction_commonDen_polyBounded (h : CanonicalProjectorDenominatorHypothesis) :
    ∃ bound : DirectionInput → ℕ,
      PolyBounded (fun p => (encDirectionInput p).length) bound ∧
      ∀ p : DirectionInput, ∃ E : ℕ, 0 < E ∧ E.size ≤ bound p ∧
        ∀ x : Vec p.1,
          CommonDen E (orient x
            (PartialColoringAlg.normalize (bestColumn (readQuadraticRows p.1 p.2.2)
              (cachedColumns (readConstraints p.1 p.2.1))))) := by
  let size (p : DirectionInput) := (encList encColoringRational (unorientedDirection p)).length
  have hs : PolyBounded (fun p => (encDirectionInput p).length) size :=
    (unorientedDirection_polytime h).polyBounded_length
  have hr : PolyBounded (fun p => (encDirectionInput p).length)
      (fun p : DirectionInput => p.1) := by
    have ht : ComputableTidilyInPolyTime (fun p : DirectionInput => p.1)
        encDirectionInput encUnary := by unfold encDirectionInput; fun_prop
    simpa only [encUnary_apply, List.length_replicate] using ht.polyBounded_length
  refine ⟨fun p => 1 + p.1 * size p, (PolyBounded.const 1).add (hr.mul hs), ?_⟩
  intro p
  let z := PartialColoringAlg.normalize (bestColumn (readQuadraticRows p.1 p.2.2)
    (cachedColumns (readConstraints p.1 p.2.1)))
  have hz : ∀ j, (z j).den.size ≤ size p := by
    intro j
    have hm : z j ∈ unorientedDirection p := by
      rw [unorientedDirection_spec]
      exact List.mem_ofFn.mpr ⟨j, rfl⟩
    have he := length_le_encList_of_mem encColoringRational hm
    have hd : (z j).den.size ≤ (encColoringRational (z j)).length := by
      simp only [encColoringRational, Function.Embedding.coeFn_mk, length_encPair,
        length_encIntBin, encNat_apply, Nat.size_eq_bits_len]
      omega
    exact hd.trans he
  refine ⟨vectorDen z, vectorDen_pos z, vectorDen_size z hz, ?_⟩
  intro x
  change CommonDen (vectorDen z) (orient x z)
  unfold orient
  split_ifs
  · exact vectorDen_commonDen z
  · intro j
    simpa only [Pi.neg_apply, Rat.neg_den] using vectorDen_commonDen z j

/-- Reification of the exact constraints and quadratic rows of a walk state. -/
def walkDirectionInput {r m : ℕ} (a : Fin m → Row r) (s : State r m) : DirectionInput :=
  (r, ((constraints a s).map List.ofFn,
    (quadraticRows a s).map fun row => (row.1, List.ofFn row.2)))

private theorem readConstraints_reify {r : ℕ} (C : List (Vec r)) :
    readConstraints r (C.map List.ofFn) = C := by
  simp [readConstraints, List.map_map, Function.comp_def, List.getD_eq_getElem?_getD]

private theorem readQuadraticRows_reify {r : ℕ} (a : List (ℚ × Vec r)) :
    readQuadraticRows r (a.map fun row => (row.1, List.ofFn row.2)) = a := by
  simp [readQuadraticRows, List.map_map, Function.comp_def, List.getD_eq_getElem?_getD]

/-- Apply the data-level bound to the original, unchanged walk direction.
The bound is a polynomial of the constraint/weight data, excluding the
starting point's rational numerators and denominators. -/
theorem walk_direction_commonDen_of_projector
    (h : CanonicalProjectorDenominatorHypothesis) :
    ∃ c d : ℕ, ∀ (r m : ℕ) (a : Fin m → Row r) (s : State r m),
      ∃ E : ℕ, 0 < E ∧ CommonDen E (direction a s) ∧
        E.size ≤ c * ((encDirectionInput (walkDirectionInput a s)).length + 1) ^ d := by
  obtain ⟨bound, hp, hb⟩ := direction_commonDen_polyBounded h
  obtain ⟨c, d, hcd⟩ := hp.exists_le
  refine ⟨c, d, fun r m a s => ?_⟩
  obtain ⟨E, hE, hsize, hden⟩ := hb (walkDirectionInput a s)
  refine ⟨E, hE, ?_, hsize.trans (hcd _)⟩
  have hd := hden s.x
  simpa only [walkDirectionInput, readConstraints_reify, readQuadraticRows_reify,
    direction] using hd

end Power2ModuleSVP.ColoringRuntime
