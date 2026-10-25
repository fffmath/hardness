import Power2ModuleSVP.Runtime.Coloring.ProjectorBounds
import Complexity.Computability.Circuit.Rational.Runtime.Determinant

/-!
# Determinant Bounds

Integer Gram determinants as polynomial-size certificates for canonical
projector denominators. Only the algebraic projector-to-Gram identification
is retained as an explicit local premise.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open PartialColoringAlg
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Clear every denominator in a raw row once. Extra columns are harmless. -/
def rowDenominator (row : List ℚ) : ℤ := (row.map fun q => (q.den : ℤ)).prod

/-- Clear row denominators to obtain integral coefficients. -/
def scaledIntegerRow (row : List ℚ) : List ℤ :=
  row.map fun q => q.num * ((rowDenominator row).natAbs / q.den : ℕ)

/-- The scale is positive even for an empty raw row. -/
theorem rowDenominator_pos (row : List ℚ) : 0 < rowDenominator row := by
  apply List.prod_pos
  intro z hz
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hz
  exact_mod_cast q.den_pos

/-- Each denominator occurs as a factor of the chosen scale. -/
theorem denominator_dvd_rowDenominator (row : List ℚ) (q : ℚ) (hq : q ∈ row) :
    (q.den : ℤ) ∣ rowDenominator row := by
  apply List.dvd_prod
  exact List.mem_map.mpr ⟨q, hq, rfl⟩

/-- The integer list program is exact row scaling, rather than rounding. -/
theorem scaledIntegerRow_entry (row : List ℚ) (q : ℚ) (hq : q ∈ row) :
    ((q.num * ((rowDenominator row).natAbs / q.den : ℕ) : ℤ) : ℚ) =
      (rowDenominator row : ℚ) * q := by
  have hd : q.den ∣ (rowDenominator row).natAbs := by
    simpa using Int.natAbs_dvd_natAbs.mpr (denominator_dvd_rowDenominator row q hq)
  have he := Nat.div_mul_cancel hd
  have he' : (((rowDenominator row).natAbs / q.den : ℕ) : ℚ) * q.den =
      (rowDenominator row : ℚ) := by
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) he
    rw [Nat.cast_mul, Int.natCast_natAbs, abs_of_pos (rowDenominator_pos row)] at hcast
    have hcastQ := congrArg (fun z : ℤ => (z : ℚ)) hcast
    simpa only [Int.cast_mul, Int.cast_natCast] using hcastQ
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  conv_rhs => rw [← q.num_div_den, ← mul_div_assoc]
  rw [Int.cast_mul, Int.cast_natCast]
  apply (eq_div_iff hden).mpr
  calc
    (q.num : ℚ) * (((rowDenominator row).natAbs / q.den : ℕ) : ℚ) * q.den =
        (q.num : ℚ) * ((((rowDenominator row).natAbs / q.den : ℕ) : ℚ) * q.den) := by ring
    _ = (rowDenominator row : ℚ) * q.num := by rw [he']; ring

/-- Native polynomial-time certificate for `rowDenominator`. -/
@[fun_prop] theorem rowDenominator_polytime :
    ComputableTidilyInPolyTime rowDenominator (encList encColoringRational) encIntBin := by
  unfold rowDenominator
  fun_prop

/-- Native polynomial-time certificate for `scaledIntegerRow`. -/
@[fun_prop] theorem scaledIntegerRow_polytime :
    ComputableTidilyInPolyTime scaledIntegerRow (encList encColoringRational)
      (encList encIntBin) := by
  unfold scaledIntegerRow
  apply mapWithInput (id' (encIn := encList encColoringRational))
  fun_prop

/-- Integral dot product, with the same truncation/padding as `readConstraints`. -/
def integerDot (p : ℕ × (List ℤ × List ℤ)) : ℤ :=
  ((List.range p.1).map fun j => p.2.1.getD j 0 * p.2.2.getD j 0).sum

private theorem range_map_ofFn {α : Type} (r : ℕ) (f : ℕ → α) :
    (List.range r).map f = List.ofFn (fun j : Fin r => f j) := by
  apply List.ext_getElem <;> simp

theorem integerDot_eq_sum (p : ℕ × (List ℤ × List ℤ)) :
    integerDot p = ∑ j : Fin p.1, p.2.1.getD j 0 * p.2.2.getD j 0 := by
  simp [integerDot, range_map_ofFn, List.sum_ofFn]

/-- Native polynomial-time certificate for `integerDot`. -/
@[fun_prop] theorem integerDot_polytime :
    ComputableTidilyInPolyTime integerDot
      (encPair encUnary (encPair (encList encIntBin) (encList encIntBin))) encIntBin := by
  unfold integerDot
  apply intBin_sum.comp
  apply mapWithInput (range.comp (fst _ _))
  fun_prop

/-- The square Gram matrix of the integer-scaled rows. -/
def integerGramRows (p : ProjectorBatchInput) : List (List ℤ) :=
  let rows := p.2.map scaledIntegerRow
  rows.map fun a => rows.map fun b => integerDot (p.1, (a, b))

/-- The computed integer Gram rows agree with finite sums of cleared coefficients. -/
theorem integerGramRows_spec (p : ProjectorBatchInput) :
    integerGramRows p = List.ofFn (fun i : Fin p.2.length =>
      List.ofFn (fun j : Fin p.2.length =>
        integerDot (p.1, (scaledIntegerRow (p.2.get i), scaledIntegerRow (p.2.get j))))) := by
  calc
    integerGramRows p = p.2.map (fun a => p.2.map (fun b =>
        integerDot (p.1, (scaledIntegerRow a, scaledIntegerRow b)))) := by
      simp [integerGramRows, List.map_map, Function.comp_def]
    _ = _ := by
      rw [← List.ofFn_getElem_eq_map p.2 (fun a => p.2.map (fun b =>
        integerDot (p.1, (scaledIntegerRow a, scaledIntegerRow b))))]
      apply congrArg List.ofFn
      funext i
      rw [← List.ofFn_getElem_eq_map p.2 (fun b =>
        integerDot (p.1, (scaledIntegerRow p.2[i.val], scaledIntegerRow b)))]
      rfl

/-- Explicit mathematical Gram matrix of the padded/truncated integer rows. -/
def integerGramMatrix (p : ProjectorBatchInput) :
    Matrix (Fin p.2.length) (Fin p.2.length) ℤ := fun i j =>
  ∑ k : Fin p.1,
    (scaledIntegerRow (p.2.get i)).getD k 0 *
      (scaledIntegerRow (p.2.get j)).getD k 0

/-- Native polynomial-time certificate for `integerGramRows`. -/
@[fun_prop] theorem integerGramRows_polytime :
    ComputableTidilyInPolyTime integerGramRows encProjectorBatch
      (encList (encList encIntBin)) := by
  have hr : ComputableTidilyInPolyTime
      (fun p : ProjectorBatchInput => p.2.map scaledIntegerRow)
      encProjectorBatch (encList (encList encIntBin)) := by
    unfold encProjectorBatch
    fun_prop
  unfold integerGramRows
  apply mapWithInput hr
  apply mapWithInput (hr.comp (fst _ _))
  apply integerDot_polytime.comp
  unfold encProjectorBatch
  fun_prop

/-- Empty Gram matrices have determinant one, covering a zero-dimensional
row span without a separate exceptional certificate. -/
def integerGramDet (p : ProjectorBatchInput) : ℤ :=
  Cslib.Circuits.Rational.detRows (integerGramRows p)

/-- The certificate is the mathematical determinant of the integral Gram
matrix, computed by the imported division-free algorithm. -/
theorem integerGramDet_eq_det (p : ProjectorBatchInput) :
    integerGramDet p =
      (Cslib.Circuits.Rational.ofRows (integerGramRows p)).det :=
  Cslib.Circuits.Rational.detRows_eq_det_ofRows _

theorem integerGramDet_eq_gramDet (p : ProjectorBatchInput) :
    integerGramDet p = (integerGramMatrix p).det := by
  have hrows : integerGramRows p = Cslib.Circuits.Rational.rowsOf (integerGramMatrix p) := by
    rw [integerGramRows_spec]
    simp only [Cslib.Circuits.Rational.rowsOf, List.finRange, List.map_ofFn,
      Function.comp_def]
    apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext j
    exact integerDot_eq_sum _
  unfold integerGramDet
  rw [hrows, Cslib.Circuits.Rational.detRows_eq]

/-- Native polynomial-time certificate for `integerGramDet`. -/
@[fun_prop] theorem integerGramDet_polytime :
    ComputableTidilyInPolyTime integerGramDet encProjectorBatch encIntBin := by
  unfold integerGramDet
  fun_prop

/-- The determinant's bit size is uniformly polynomial in the raw encoding.
This follows from the certified division-free determinant, so no numerical
Hadamard estimate is needed for the quantitative part of the argument. -/
theorem integerGramDet_bits_polyBounded :
    PolyBounded (fun p => (encProjectorBatch p).length)
      (fun p => (integerGramDet p).natAbs.size) := by
  have h := integerGramDet_polytime.polyBounded_length
  apply h.mono
  intro p
  simp only [length_encIntBin]
  omega

private theorem encList_length_mono_sublist {α : Type} (enc : α ↪ List Bool)
    {xs ys : List α} (h : xs.Sublist ys) :
    (encList enc xs).length ≤ (encList enc ys).length := by
  exact (h.flatMap (frame ∘ enc)).length_le

/-- Uniformity also covers the independent-row sublist chosen by algebra. -/
theorem integerGramDet_sublist_bits_bound :
    ∃ c d : ℕ, ∀ (p : ProjectorBatchInput) (rows : List (List ℚ)),
      rows.Sublist p.2 →
      (integerGramDet (p.1, rows)).natAbs.size ≤
        c * ((encProjectorBatch p).length + 1) ^ d := by
  obtain ⟨c, d, hb⟩ := integerGramDet_bits_polyBounded.exists_le
  refine ⟨c, d, fun p rows hs => (hb (p.1, rows)).trans ?_⟩
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have hl := encList_length_mono_sublist (encList encColoringRational) hs
  simp only [encProjectorBatch, length_encPair]
  omega

/-- Pure algebraic obligation: select independent rows spanning the same
row space, and use their integer Gram determinant as a common denominator
of the orthogonal projector. This premise contains no bit or runtime bound. -/
structure GramProjectorDivisibilityHypothesis : Prop where
  gram_divisibility : ∀ (p : ProjectorBatchInput),
    ∃ rows : List (List ℚ), rows.Sublist p.2 ∧
      integerGramDet (p.1, rows) ≠ 0 ∧
      ∀ j k : Fin p.1,
        (tableEntry (projectorTable (readConstraints p.1 p.2)) j k).den ∣
          (integerGramDet (p.1, rows)).natAbs

/-- All quantitative projector denominator bounds reduce to the one
algebraic Gram divisibility statement above. -/
theorem canonicalProjectorDenominator_of_gram
    (h : GramProjectorDivisibilityHypothesis) : CanonicalProjectorDenominatorHypothesis := by
  obtain ⟨c, d, hb⟩ := integerGramDet_sublist_bits_bound
  refine ⟨⟨c, d, fun p rows hs j k => ?_⟩⟩
  obtain ⟨basisRows, hsub, hnonzero, hdiv⟩ := h.gram_divisibility (p.1, rows)
  have hpos : 0 < (integerGramDet (p.1, basisRows)).natAbs := Int.natAbs_pos.mpr hnonzero
  exact (Nat.size_le_size (Nat.le_of_dvd hpos (hdiv j k))).trans
    (hb p basisRows (hsub.trans hs))

/-- The complete cached-projector machine certificate now has a purely
algebraic premise. -/
theorem projectorBatch_polytime_of_gram (h : GramProjectorDivisibilityHypothesis) :
    ComputableTidilyInPolyTime projectorBatch encProjectorBatch
      (encList (encList encColoringRational)) :=
  projectorBatch_polytime_of_denominator (canonicalProjectorDenominator_of_gram h)

end Power2ModuleSVP.ColoringRuntime
