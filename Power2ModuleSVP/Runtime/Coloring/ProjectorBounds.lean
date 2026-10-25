import Power2ModuleSVP.Runtime.Coloring.CachedProjector
import Power2ModuleSVP.Runtime.Coloring.Weights

/-!
# Projector Bounds

Reduce the projector machine obligation to canonical denominator bits.
Numerators are bounded by contraction, including all rank-deficient cases.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open PartialColoringAlg ColoringNative

theorem projector_entry_abs_le_one {r : ℕ} (C : List (Vec r)) (j k : Fin r) :
    |tableEntry (projectorTable C) j k| ≤ 1 := by
  rw [projectorTable_spec]
  apply coordinate_abs_le_of_dot_self_le
  have h := project_norm_le C (coordinate j)
  simpa [dot, coordinate] using h

theorem numerator_size_le_den_size_of_abs_le_one (q : ℚ) (hq : |q| ≤ 1) :
    q.num.natAbs.size ≤ q.den.size := by
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hnum : (|q.num| : ℚ) ≤ q.den := by
    have hn := hq
    conv_lhs at hn => rw [← q.num_div_den]
    rw [abs_div, abs_of_pos hd, div_le_one hd] at hn
    exact_mod_cast hn
  have hn' : q.num.natAbs ≤ q.den := by
    have hi : (|q.num| : ℤ) ≤ (q.den : ℤ) := by exact_mod_cast hnum
    rw [← Int.natCast_natAbs] at hi
    exact_mod_cast hi
  exact Nat.size_le_size hn'

theorem rational_encoding_le_of_den_bound (q : ℚ) (hq : |q| ≤ 1) {B : ℕ}
    (hB : q.den.size ≤ B) : (encColoringRational q).length ≤ 4 * B + 3 := by
  have hn := numerator_size_le_den_size_of_abs_le_one q hq
  simp only [encColoringRational, Function.Embedding.coeFn_mk, length_encPair,
    length_encIntBin, encNat_apply, Nat.size_eq_bits_len]
  omega

private theorem projectorTable_shape {r : ℕ} (C : List (Vec r)) :
    projectorTable C = List.ofFn (fun j : Fin r =>
      List.ofFn (fun k : Fin r => tableEntry (projectorTable C) j k)) := by
  cases C <;> simp [projectorTable, tableEntry, List.getD_eq_getElem?_getD]

/-- A denominator bound controls the complete framed table encoding.
No determinant nonvanishing or constraint independence is required here. -/
theorem projector_encoding_le_of_den_bound {r B : ℕ} (C : List (Vec r))
    (hB : ∀ j k : Fin r, (tableEntry (projectorTable C) j k).den.size ≤ B) :
    (encList (encList encColoringRational) (projectorTable C)).length ≤
      (2 * ((8 * B + 7) * r) + 1) * r := by
  rw [projectorTable_shape]
  apply (length_encList_le (encList encColoringRational) _ (b := (8 * B + 7) * r) ?_).trans
  · simp [Nat.mul_comm]
  · intro row hrow
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hrow
    have h := length_encList_le encColoringRational
      (List.ofFn fun k : Fin r => tableEntry (projectorTable C) j k)
      (b := 4 * B + 3) (by
        intro q hq
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hq
        exact rational_encoding_le_of_den_bound _ (projector_entry_abs_le_one C j k) (hB j k))
    simp only [List.length_ofFn] at h
    convert h using 1; ring

/-- Pure arithmetic boundary: polynomially many denominator bits for every
canonical projector associated to a sublist of the raw input constraints.
This is strictly more local than a machine certificate for the projector. -/
structure CanonicalProjectorDenominatorHypothesis : Prop where
  denominator_bound : ∃ coefficient degree : ℕ,
    ∀ (p : ProjectorBatchInput) (rows : List (List ℚ)), rows.Sublist p.2 →
      ∀ j k : Fin p.1,
        (tableEntry (projectorTable (readConstraints p.1 rows)) j k).den.size ≤
          coefficient * ((encProjectorBatch p).length + 1) ^ degree

/-- A canonical denominator bound gives a polynomial projector encoding bound. -/
theorem canonicalProjectorSize_of_denominator
    (h : CanonicalProjectorDenominatorHypothesis) : CanonicalProjectorSizeHypothesis := by
  obtain ⟨c, d, hb⟩ := h.denominator_bound
  let B (p : ProjectorBatchInput) := c * ((encProjectorBatch p).length + 1) ^ d
  have hB : PolyBounded (fun p => (encProjectorBatch p).length) B :=
    PolyBounded.of_forall_le c d (fun _ => le_rfl)
  have hdim : PolyBounded (fun p => (encProjectorBatch p).length)
      (fun p : ProjectorBatchInput => p.1) := by
    have hp : ComputableTidilyInPolyTime (fun p : ProjectorBatchInput => p.1)
        encProjectorBatch encUnary := by unfold encProjectorBatch; fun_prop
    simpa only [encUnary_apply, List.length_replicate] using hp.polyBounded_length
  have hfinal : PolyBounded (fun p => (encProjectorBatch p).length)
      (fun p : ProjectorBatchInput => (2 * ((8 * B p + 7) * p.1) + 1) * p.1) :=
    (((PolyBounded.const 2).mul
      ((((PolyBounded.const 8).mul hB).add (.const 7)).mul hdim)).add (.const 1)).mul hdim
  obtain ⟨c', d', hf⟩ := hfinal.exists_le
  refine ⟨⟨c', d', fun p rows hs => ?_⟩⟩
  exact (projector_encoding_le_of_den_bound (readConstraints p.1 rows) (hb p rows hs)).trans
    (hf p)

/-- Complete native projector construction from the local arithmetic bound. -/
theorem projectorBatch_polytime_of_denominator
    (h : CanonicalProjectorDenominatorHypothesis) :
    ComputableTidilyInPolyTime projectorBatch encProjectorBatch
      (encList (encList encColoringRational)) :=
  projectorBatch_polytime_of_size (canonicalProjectorSize_of_denominator h)

end Power2ModuleSVP.ColoringRuntime
