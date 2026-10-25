import Power2ModuleSVP.FlatFrontend.Rational

/-!
# Inputs

Framed-list identities for the concrete frontend. In particular, the
semantic finite matrices below are extracted from the actual program output.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators

structure InputShape (P : PartialColoringInput) (r m : ℕ) : Prop where
  rows : P.1.length = m
  columns : ∀ row ∈ P.1, row.length = r
  starting : P.2.1.length = r
  thresholds : P.2.2.length = m

def inputMatrix (P : PartialColoringInput) {r m : ℕ} (i : Fin m) (j : Fin r) : ℚ :=
  (P.1.getD i []).getD j 0

def inputStart (P : PartialColoringInput) {r : ℕ} (j : Fin r) : ℚ := P.2.1.getD j 0

def inputThreshold (P : PartialColoringInput) {m : ℕ} (i : Fin m) : ℚ := P.2.2.getD i 0

theorem ofFn_getD_length {α : Type*} (l : List α) (a : α) {n : ℕ} (hl : l.length = n) :
    List.ofFn (fun i : Fin n => l.getD i a) = l := by
  subst n
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.getD_eq_getElem?_getD]

theorem getD_mem {α : Type*} (l : List α) (a : α) {i : ℕ} (hi : i < l.length) :
    l.getD i a ∈ l := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem input_pack {P : PartialColoringInput} {r m : ℕ} (hP : InputShape P r m) :
    P = partialColoringInput (inputMatrix P (r := r) (m := m))
      (inputStart P) (inputThreshold P) := by
  have hx := ofFn_getD_length P.2.1 0 hP.starting
  have hc := ofFn_getD_length P.2.2 0 hP.thresholds
  have hm : List.ofFn (fun i : Fin m => List.ofFn (inputMatrix P i : Fin r → ℚ)) = P.1 := by
    have hh : ∀ i : Fin m, List.ofFn (inputMatrix P i : Fin r → ℚ) = P.1.getD i [] := by
      intro i
      apply ofFn_getD_length
      apply hP.columns
      exact getD_mem P.1 [] (by rw [hP.rows]; exact i.isLt)
    simp_rw [hh]
    exact ofFn_getD_length P.1 [] hP.rows
  exact Prod.ext hm.symm (Prod.ext hx.symm hc.symm)

theorem intervalInput_shape (d : ℕ) :
    InputShape (intervalInput d) (intervals (seedN d)).length
      (seedIntervalRows (seedN d) (intervals (seedN d)).length) := by
  dsimp only [intervalInput]
  split_ifs with h
  · simp only [seedIntervalRows, h, ↓reduceIte]
    constructor <;> simp
  · simp only [seedIntervalRows, h, ↓reduceIte]
    constructor
    · simp
    · intro row hr
      simp only [List.mem_map] at hr
      obtain ⟨i, _, rfl⟩ := hr
      simp
    · simp
    · simp

theorem coefficientInput_shape (a : ℕ × List ℚ) :
    InputShape (coefficientInput a) (seedN a.1) (seedDerivativeRows a.1) := by
  constructor
  · simp [coefficientInput, seedDerivativeRows]
  · intro row hr
    simp only [coefficientInput, List.mem_map] at hr
    obtain ⟨i, _, rfl⟩ := hr
    simp
  · simp [coefficientInput]
  · simp [coefficientInput, seedDerivativeRows]

theorem first_cube (d : ℕ) :
    RationalCube (inputStart (intervalInput d) (r := (intervals (seedN d)).length)) := by
  intro j
  simp only [inputStart, intervalInput]
  split_ifs with h
  · exact False.elim (by have := j.isLt; omega)
  · simp [List.getD_eq_getElem?_getD]

theorem first_threshold_nonnegative (d : ℕ) :
    ∀ i : Fin (seedIntervalRows (seedN d) (intervals (seedN d)).length),
      0 ≤ inputThreshold (intervalInput d) i := by
  intro i
  dsimp only [inputThreshold, intervalInput]
  split_ifs with h
  · have := i.isLt
    simp [seedIntervalRows, h] at this
  · have hi : i.val < seedN d := by simpa [seedIntervalRows, h] using i.isLt
    simpa [List.getD_eq_getElem?_getD, hi] using
      firstThreshold_nonnegative (seedN d) (intervals (seedN d)).length

theorem first_entropy (d : ℕ) :
    coloringEntropy (inputThreshold (intervalInput d)
      (m := seedIntervalRows (seedN d) (intervals (seedN d)).length)) ≤
        ((intervals (seedN d)).length : ℝ) / 64 := by
  by_cases h : (intervals (seedN d)).length = 0
  · have : IsEmpty (Fin (seedIntervalRows (seedN d) (intervals (seedN d)).length)) := by
      rw [seedIntervalRows, ite_eq_left h]
      infer_instance
    simp [coloringEntropy, h]
  · have ht : inputThreshold (intervalInput d)
        (m := seedIntervalRows (seedN d) (intervals (seedN d)).length) =
        fun _ => firstThreshold (seedN d) (intervals (seedN d)).length := by
      funext i
      have hi : i.val < seedN d := by simpa [seedIntervalRows, h] using i.isLt
      simp [inputThreshold, intervalInput, h, List.getD_eq_getElem?_getD, hi]
    rw [ht]
    rw [seedIntervalRows, ite_eq_right h]
    exact first_threshold_entropy (seedN d) (intervals (seedN d)).length (by omega)

theorem second_cube (a : ℕ × List ℚ) :
    RationalCube (inputStart (coefficientInput a) (r := seedN a.1)) := by
  intro j
  have hm : (coefficientInput a).2.1.getD j 0 ∈ (coefficientInput a).2.1 :=
    getD_mem _ _ (by rw [(coefficientInput_shape a).starting]; exact j.isLt)
  exact (second_starting_cube a _ hm).trans (by norm_num)

theorem second_threshold (a : ℕ × List ℚ) (i : Fin (seedDerivativeRows a.1)) :
    inputThreshold (coefficientInput a) i = 12 + (i.val / (16 * seedN a.1) : ℕ) := by
  have hi : i.val < 16 * seedN a.1 * (seedN a.1 + 1) := i.isLt
  simp [inputThreshold, coefficientInput, List.getD_eq_getElem?_getD, hi]

theorem second_threshold_nonnegative (a : ℕ × List ℚ) :
    ∀ i : Fin (seedDerivativeRows a.1), 0 ≤ inputThreshold (coefficientInput a) i := by
  intro i
  rw [second_threshold]
  positivity

theorem second_matrix (a : ℕ × List ℚ) (i : Fin (seedDerivativeRows a.1))
    (j : Fin (seedN a.1)) :
    inputMatrix (coefficientInput a) i j =
      derivativeEntry (seedN a.1) (i % (16 * seedN a.1)) (i / (16 * seedN a.1)) j := by
  have hi : i.val < 16 * seedN a.1 * (seedN a.1 + 1) := i.isLt
  simp [inputMatrix, coefficientInput, List.getD_eq_getElem?_getD, hi]

theorem second_start (a : ℕ × List ℚ) (j : Fin (seedN a.1)) :
    inputStart (coefficientInput a) j = clamp (-(4 / 5)) (4 / 5)
      (fractionalCoefficient (seedN a.1) (intervals (seedN a.1)) a.2 j) := by
  simp [inputStart, coefficientInput, List.getD_eq_getElem?_getD]

theorem derivative_entropy_flat (N : ℕ) :
    (∑ i : Fin (16 * N * (N + 1)),
      Real.exp (-((12 + (i.val / (16 * N) : ℕ) : ℝ) ^ 2) / 16)) ≤ (N : ℝ) / 64 := by
  by_cases hN : N = 0
  · subst N; simp
  have hNp : 0 < 16 * N := by omega
  let e : (Fin (N + 1) × Fin (16 * N)) ≃ Fin (16 * N * (N + 1)) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm (N + 1) (16 * N)))
  have he : ∀ x : Fin (N + 1) × Fin (16 * N), (e x).val / (16 * N) = x.1.val := by
    intro x
    change (x.2.val + 16 * N * x.1.val) / (16 * N) = x.1.val
    rw [Nat.add_mul_div_left _ _ hNp, Nat.div_eq_of_lt x.2.isLt, zero_add]
  have hs := Fintype.sum_equiv e
    (fun x : Fin (N + 1) × Fin (16 * N) =>
      Real.exp (-((12 + (x.1.val : ℝ)) ^ 2) / 16))
    (fun i => Real.exp (-((12 + (i.val / (16 * N) : ℕ) : ℝ) ^ 2) / 16))
    (fun x => by rw [he])
  rw [← hs, Fintype.sum_prod_type]
  exact seed_derivative_entropy N

theorem second_entropy (a : ℕ × List ℚ) :
    coloringEntropy (inputThreshold (coefficientInput a) (m := seedDerivativeRows a.1)) ≤
      (seedN a.1 : ℝ) / 64 := by
  simp only [coloringEntropy, second_threshold, Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast]
  exact derivative_entropy_flat (seedN a.1)

end FlatFrontend
end Power2ModuleSVP
