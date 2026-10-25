import Power2ModuleSVP.Runtime.Coloring.DirectionBounds
import Power2ModuleSVP.Runtime.Coloring.Preparation

/-!
# Partial Denominators

A partial call adds polynomially many common-denominator bits. Its
increment depends on the matrix, thresholds and dimension, excluding the
starting coordinates' encodings.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open PartialColoringAlg ColoringNative
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD

/-- Pair the ambient dimension with its prepared coloring rows. -/
def preparedParameter (p : PreparationInput) : WalkParameter := (p.1, prepareList p)

/-- Native polynomial-time certificate for `preparedParameter`. -/
theorem preparedParameter_polytime :
    ComputableTidilyInPolyTime preparedParameter encPreparation encWalkParameter := by
  have hp := (fst encUnary
    (encPair (encList (encList encColoringRational)) (encList encColoringRational))).prod
      prepareList_polytime
  exact hp.of_enc_eq fun p => congrArg encWalkParameter (by rfl)

/-- Reading the prepared list parameters recovers the mathematical prepared rows. -/
theorem preparedParameter_read (r : ℕ) (V : List (List ℚ)) (c : List ℚ) :
    preparedParameter (r, (V, c)) = walkParameter
      (prepareRows (fun i : Fin V.length => fun j : Fin r => (V.getD i []).getD j 0)
        (fun i => c.getD i 0)).get := by
  unfold preparedParameter walkParameter
  rw [prepareList_read]
  congr 1
  let rows := prepareRows (fun i : Fin V.length => fun j : Fin r => (V.getD i []).getD j 0)
    (fun i => c.getD i 0)
  have h : List.ofFn rows.get = rows := by
    apply List.ext_getElem <;> simp
  simpa only [List.map_ofFn, Function.comp_def] using
    (congrArg (List.map (fun row : Row r => (row.threshold, List.ofFn row.a))) h).symm

private theorem raw_input_bounds (input : PartialColoringInput)
    (hv : validInput input = true) :
    RationalCube (fun j : Fin input.2.1.length => input.2.1.getD j 0) ∧
      ∀ i : Fin input.1.length, 0 ≤ input.2.2.getD i 0 := by
  simp only [validInput, Bool.and_eq_true] at hv
  have hx : input.2.1.all (fun q => decide (|q| ≤ 1)) = true := by tauto
  have hc : input.2.2.all (fun q => decide (0 ≤ q)) = true := by tauto
  have hl : decide (input.2.2.length = input.1.length) = true := by tauto
  have hlen := of_decide_eq_true hl
  constructor
  · intro j
    have hj : input.2.1.getD j 0 ∈ input.2.1 := by
      simp [List.getD_eq_getElem?_getD, j.isLt]
    exact_mod_cast (of_decide_eq_true (List.all_eq_true.mp hx _ hj) :
      |input.2.1.getD j 0| ≤ 1)
  · intro i
    have hi : i.val < input.2.2.length := by omega
    have hm : input.2.2.getD i 0 ∈ input.2.2 := by
      simp [List.getD_eq_getElem?_getD, hi]
    exact of_decide_eq_true (List.all_eq_true.mp hc _ hm)

private theorem sign_den_dvd (D : ℕ) {q : ℚ} (hq : q = -1 ∨ q = 1) : q.den ∣ D := by
  rcases hq with rfl | rfl <;> simp

/-- Explicit polynomial size of the row-dependent additive increment. -/
theorem partial_denominator_stride_polyBounded (c d : ℕ) :
    PolyBounded (fun p : PreparationInput => (encPreparation p).length)
      (fun p => stepBudget p.1 * ((stepSize p.1).den.size +
        c * ((encWalkParameter (preparedParameter p)).length + 1) ^ d)) := by
  have hr : ComputableTidilyInPolyTime (fun p : PreparationInput => p.1)
      encPreparation encUnary := fst encUnary
        (encPair (encList (encList encColoringRational)) (encList encColoringRational))
  have hbudget := (stepBudget_polytime.comp hr).polyBounded_length
  simp only [encUnary_apply, List.length_replicate] at hbudget
  have hcast := natCast_polytime.comp unary_to_binary
  have hscalar := div_polytime.comp ((const (1 : ℚ)).prod
    (mul_polytime.comp ((const (16 : ℚ)).prod hcast)))
  have hdelta : ComputableTidilyInPolyTime (fun p : PreparationInput => stepSize p.1)
      encPreparation encColoringRational := by
    have ht := hscalar.comp hr
    exact ht.of_enc_eq fun p => congrArg encColoringRational (by rfl)
  have hd := hdelta.polyBounded_length.mono (u := fun p => (stepSize p.1).den.size) (by
    intro p
    simp only [encColoringRational, Function.Embedding.coeFn_mk, length_encPair,
      length_encIntBin, encNat_apply, Nat.size_eq_bits_len]
    omega)
  obtain ⟨cb, db, hb⟩ := hbudget.exists_le
  obtain ⟨cd, dd, hd⟩ := hd.exists_le
  obtain ⟨cp, dp, hp⟩ := preparedParameter_polytime.polyBounded_length.exists_le
  let B (n : ℕ) := cb * (n + 1) ^ db *
    (cd * (n + 1) ^ dd + c * (cp * (n + 1) ^ dp + 1) ^ d)
  have hB : PolyBounded id B := ⟨B, by unfold B; fun_prop, fun _ => le_rfl⟩
  obtain ⟨cB, dB, hbound⟩ := hB.exists_le
  apply PolyBounded.of_forall_le cB dB
  intro p
  apply le_trans (b := B (encPreparation p).length)
  · exact Nat.mul_le_mul (hb p) (Nat.add_le_add (hd p)
      (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right (hp p) 1) d)))
  · exact hbound _

/-- A uniform additive bound for the actual partial-coloring call. -/
theorem partialColor_commonDen_increment
    (h : CanonicalProjectorDenominatorHypothesis) :
    ∃ c d : ℕ, ∀ (input : PartialColoringInput) (D : ℕ), 0 < D →
      (∀ q ∈ input.2.1, q.den ∣ D) →
      ∃ E : ℕ, 0 < E ∧ (∀ q ∈ partialColor input, q.den ∣ E) ∧
        E.size ≤ D.size + c * ((encPreparation
          (input.2.1.length, (input.1, input.2.2))).length + 1) ^ d := by
  obtain ⟨c₀, d₀, hb⟩ := walk_initial_commonDen_uniform h
  obtain ⟨c, d, hpoly⟩ := (partial_denominator_stride_polyBounded c₀ d₀).exists_le
  refine ⟨c, d, fun input D hD hden => ?_⟩
  by_cases hz : input.2.1.length = 0
  · refine ⟨D, hD, ?_, by omega⟩
    have hl : partialColor input = [] := List.length_eq_zero_iff.mp (by
      rw [partialColor_length, hz])
    simp [hl]
  have hr : 0 < input.2.1.length := by omega
  by_cases hv : validInput input = true
  · let r := input.2.1.length
    let m := input.1.length
    let V : Fin m → Vec r := fun i j => (input.1.getD i []).getD j 0
    let x : Vec r := fun j => input.2.1.getD j 0
    let lam : Fin m → ℚ := fun i => input.2.2.getD i 0
    let rows := prepareRows V lam
    have hout : partialColor input = partialColorCore r m V x lam := by
      unfold partialColor
      rw [ite_eq_left hv]
    by_cases he : rows.isEmpty = true
    · refine ⟨D, hD, ?_, by omega⟩
      intro q hq
      rw [hout] at hq
      change q ∈ (if rows.isEmpty then List.ofFn (fun j => nearestRationalSign (x j))
        else List.ofFn (run rows.get x).x) at hq
      rw [ite_eq_left he] at hq
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
      exact sign_den_dvd D (nearestRationalSign_isSign _)
    · obtain ⟨hxc, hlc⟩ := raw_input_bounds input hv
      have hrow (i : Fin rows.length) := prepareRows_row_properties V lam hlc
        (rows.get i) (List.get_mem _ _)
      have hxden : CommonDen D x := by
        intro j
        apply hden
        change input.2.1.getD j 0 ∈ input.2.1
        have hj : j.val < input.2.1.length := j.isLt
        simp [List.getD_eq_getElem?_getD, hj]
      obtain ⟨E, hE, hEx, hsize⟩ := hb r rows.length D (stepBudget r) hr rows.get
        (fun i => (hrow i).2.1) (fun i => (hrow i).2.2) le_rfl hD x hxc hxden
      refine ⟨E, hE, ?_, ?_⟩
      · intro q hq
        rw [hout] at hq
        change q ∈ (if rows.isEmpty then List.ofFn (fun j => nearestRationalSign (x j))
          else List.ofFn (run rows.get x).x) at hq
        rw [ite_eq_right he] at hq
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
        exact hEx j
      · have hp := hpoly (r, (input.1, input.2.2))
        rw [preparedParameter_read] at hp
        exact hsize.trans (Nat.add_le_add_left hp D.size)
  · refine ⟨D, hD, ?_, by omega⟩
    intro q hq
    unfold partialColor at hq
    rw [ite_eq_right hv] at hq
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hq
    exact sign_den_dvd D (nearestRationalSign_isSign _)

end Power2ModuleSVP.ColoringRuntime
