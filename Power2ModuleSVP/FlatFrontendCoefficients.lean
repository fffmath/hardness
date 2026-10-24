import Power2ModuleSVP.FlatFrontendWords

/-! Exact Laurent assembly. The real functions here are proof-side
interpretations of the executable integer word. -/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators

theorem seedN_four (N : ℕ) : seedN (4 * N + 4) = N := by unfold seedN; omega

theorem sum_range_double {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    (∑ i ∈ Finset.range (2 * N), f i) =
      ∑ j ∈ Finset.range N, (f (2 * j) + f (2 * j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [add_assoc]

theorem circle_mode (m k : ℕ) (a b θ : ℝ) (hk : k ≤ m) :
    (a : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ^ (m + k) +
      (b : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ^ (m - k) =
    Complex.exp ((θ : ℂ) * Complex.I) ^ m *
      (((a + b) * Real.cos ((k : ℝ) * θ) : ℝ) +
        Complex.I * (((a - b) * Real.sin ((k : ℝ) * θ) : ℝ) : ℂ)) := by
  have hp : Complex.exp ((θ : ℂ) * Complex.I) ^ (m + k) =
      Complex.exp ((θ : ℂ) * Complex.I) ^ m *
        Complex.exp ((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hn : Complex.exp ((θ : ℂ) * Complex.I) ^ (m - k) =
      Complex.exp ((θ : ℂ) * Complex.I) ^ m *
        Complex.exp (((-(k : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add,
      Nat.cast_sub hk]
    congr 1
    push_cast
    ring
  rw [hp, hn, Complex.exp_ofReal_mul_I ((k : ℝ) * θ),
    Complex.exp_ofReal_mul_I (-(k : ℝ) * θ)]
  simp only [neg_mul, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add]
  ring

theorem centered_sum (m : ℕ) (a : ℕ → ℤ) (θ : ℝ) :
    (∑ i ∈ Finset.range (2 * m + 1),
      (a i : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ^ i) =
    Complex.exp ((θ : ℂ) * Complex.I) ^ m *
      ((a m : ℂ) + ∑ j ∈ Finset.range m,
        ((((a (m + (j + 1)) : ℝ) + a (m - (j + 1))) *
          Real.cos (((j + 1 : ℕ) : ℝ) * θ) : ℝ) +
        Complex.I * ((((a (m + (j + 1)) : ℝ) - a (m - (j + 1))) *
          Real.sin (((j + 1 : ℕ) : ℝ) * θ) : ℝ)))) := by
  let f := fun i => (a i : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ^ i
  have hl := Finset.sum_range_reflect f m
  rw [show 2 * m + 1 = m + (m + 1) by omega, Finset.sum_range_add,
    Finset.sum_range_succ', ← hl]
  have hm : ∀ j, m - 1 - j = m - (j + 1) := by omega
  simp only [hm, show m + 0 = m by omega]
  rw [show (∑ x ∈ Finset.range m, f (m - (x + 1))) +
        ((∑ k ∈ Finset.range m, f (m + (k + 1))) + f m) =
      f m + ∑ j ∈ Finset.range m, (f (m + (j + 1)) + f (m - (j + 1))) by
        rw [Finset.sum_add_distrib]; abel]
  rw [mul_add, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · dsimp [f]; ring
  · apply Finset.sum_congr rfl
    intro j hj
    exact circle_mode m (j + 1) (a (m + (j + 1))) (a (m - (j + 1))) θ
      (by have := Finset.mem_range.mp hj; omega)

noncomputable def cosine (d : ℕ) (θ : ℝ) : ℝ :=
  let N := seedN d
  let b := background d
  ∑ j ∈ Finset.range N,
    (((seedIntegerSign (b.getD (2 * N + (2 * j + 2)) 1) : ℤ) : ℝ) +
      seedIntegerSign (b.getD (2 * N - (2 * j + 2)) 1)) / 2 *
        Real.cos ((2 * (j : ℝ) + 2) * θ)

noncomputable def evenPart (d : ℕ) (θ : ℝ) : ℝ :=
  let N := seedN d
  let b := background d
  ∑ j ∈ Finset.range N,
    (((seedIntegerSign (b.getD (2 * N + (2 * j + 2)) 1) : ℤ) : ℝ) -
      seedIntegerSign (b.getD (2 * N - (2 * j + 2)) 1)) / 2 *
        Real.sin ((2 * (j : ℝ) + 2) * θ)

noncomputable def oddPart {N : ℕ} (y : Fin N → ℚ) (θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, ((List.ofFn y).getD j 0 : ℝ) *
    Real.sin ((2 * (j : ℝ) + 1) * θ)

theorem background_center (N : ℕ) :
    (background (4 * N + 4)).getD (2 * N) 1 = 1 := by
  simp [background, seedN_four, List.getD_eq_getElem?_getD,
    show 2 * N < 4 * N + 4 by omega]

theorem background_tail (N k : ℕ) (hk : k < 3) :
    (background (4 * N + 4)).getD (4 * N + 1 + k) 1 = 1 := by
  simp [background, seedN_four, List.getD_eq_getElem?_getD,
    show 4 * N + 1 + k < 4 * N + 4 by omega,
    show 4 * N + 1 + k ≠ 2 * N by omega,
    show ¬ 4 * N + 1 + k ≤ 4 * N by omega]

def assembledCoefficient (N : ℕ) (y : Fin N → ℚ) (i : ℕ) : ℤ :=
  (seedAssemble (4 * N + 4) (background (4 * N + 4)) (List.ofFn y)).getD i 0

theorem assembled_even (N : ℕ) (y : Fin N → ℚ) {i : ℕ}
    (hi : i < 4 * N + 4) (he : i % 2 = 0) :
    assembledCoefficient N y i =
      seedIntegerSign ((background (4 * N + 4)).getD i 1) := by
  simp [assembledCoefficient, seedAssemble, seedN_four, seedOddPosition,
    List.getD_eq_getElem?_getD, hi, he]

theorem assembled_center (N : ℕ) (y : Fin N → ℚ) :
    assembledCoefficient N y (2 * N) = 1 := by
  rw [assembled_even N y (by omega) (by omega), background_center]
  norm_num [seedIntegerSign]

theorem assembled_tail (N : ℕ) (y : Fin N → ℚ) {k : ℕ} (hk : k < 3) :
    assembledCoefficient N y (4 * N + 1 + k) = 1 := by
  simp only [assembledCoefficient, seedAssemble, seedN_four]
  have hi : 4 * N + 1 + k < 4 * N + 4 := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]
  rw [ite_eq_right (by unfold seedOddPosition; omega)]
  change seedIntegerSign ((background (4 * N + 4)).getD (4 * N + 1 + k) 1) = 1
  rw [background_tail N k hk]
  norm_num [seedIntegerSign]

theorem assembled_odd_high (N : ℕ) (y : Fin N → ℚ) (j : Fin N)
    (hy : ∀ j, y j = -1 ∨ y j = 1) :
    (assembledCoefficient N y (2 * N + (2 * j + 1)) : ℝ) = (y j : ℝ) := by
  have hi : 2 * N + (2 * j + 1) < 4 * N + 4 := by omega
  have hp : seedOddPosition N (2 * N + (2 * j + 1)) := by
    unfold seedOddPosition
    omega
  have hind : seedOddIndex N (2 * N + (2 * j + 1)) = j := by
    unfold seedOddIndex
    split_ifs <;> omega
  simp only [assembledCoefficient, seedAssemble, seedN_four,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, hp, ↓reduceIte, hind,
    show ¬ 2 * N + (2 * j + 1) < 2 * N by omega]
  have hget : (List.ofFn y)[j.val]? = some (y j) := by simp
  rw [hget]
  exact_mod_cast seedRationalSign_cast (hy j)

theorem assembled_odd_low (N : ℕ) (y : Fin N → ℚ) (j : Fin N)
    (hy : ∀ j, y j = -1 ∨ y j = 1) :
    (assembledCoefficient N y (2 * N - (2 * j + 1)) : ℝ) = -(y j : ℝ) := by
  have hi : 2 * N - (2 * j + 1) < 4 * N + 4 := by omega
  have hp : seedOddPosition N (2 * N - (2 * j + 1)) := by
    unfold seedOddPosition
    omega
  have hind : seedOddIndex N (2 * N - (2 * j + 1)) = j := by
    unfold seedOddIndex
    split_ifs <;> omega
  simp only [assembledCoefficient, seedAssemble, seedN_four,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, hp, ↓reduceIte, hind,
    show 2 * N - (2 * j + 1) < 2 * N by omega]
  have hget : (List.ofFn y)[j.val]? = some (y j) := by simp
  rw [hget]
  push_cast
  exact congrArg Neg.neg (by exact_mod_cast seedRationalSign_cast (hy j) :
    (seedRationalSign (y j) : ℝ) = (y j : ℝ))

theorem assembled_core (N : ℕ) (y : Fin N → ℚ)
    (hy : ∀ j, y j = -1 ∨ y j = 1) (θ : ℝ) :
    (∑ i ∈ Finset.range (4 * N + 1),
      (assembledCoefficient N y i : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ^ i) =
    Complex.exp ((θ : ℂ) * Complex.I) ^ (2 * N) *
      (((1 + 2 * cosine (4 * N + 4) θ : ℝ) : ℂ) +
        2 * Complex.I * ((evenPart (4 * N + 4) θ + oddPart y θ : ℝ) : ℂ)) := by
  rw [show 4 * N + 1 = 2 * (2 * N) + 1 by omega, centered_sum,
    assembled_center, Int.cast_one, sum_range_double]
  congr 1
  simp only [cosine, evenPart, seedN_four, oddPart]
  simp only [
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  conv_rhs => rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjN := Finset.mem_range.mp hj
  have hhigh := assembled_odd_high N y ⟨j, hjN⟩ hy
  have hlow := assembled_odd_low N y ⟨j, hjN⟩ hy
  have hehigh := assembled_even N y (i := 2 * N + (2 * j + 2)) (by omega) (by omega)
  have helow := assembled_even N y (i := 2 * N - (2 * j + 2)) (by omega) (by omega)
  simp only [show 2 * j + 1 + 1 = 2 * j + 2 by omega, hehigh, helow,
    hhigh, hlow]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dite_eq_left hjN, Option.getD_some]
  push_cast
  ring

/-- The exact evaluation identity, with the final three coefficients
included. No interval, rounding, or spectral hypothesis is used. -/
theorem assembled_evaluation (N : ℕ) (y : Fin N → ℚ)
    (hy : ∀ j, y j = -1 ∨ y j = 1) (θ : ℝ) :
    ∃ u tail : ℂ, ‖u‖ = 1 ∧ ‖tail‖ ≤ 3 ∧
      coeffEval (IdealCVP.ofList (d := 4 * N + 4)
        (seedAssemble (4 * N + 4) (background (4 * N + 4)) (List.ofFn y)))
        (Complex.exp ((θ : ℂ) * Complex.I)) =
      u * (((1 + 2 * cosine (4 * N + 4) θ : ℝ) : ℂ) +
        2 * Complex.I * ((evenPart (4 * N + 4) θ + oddPart y θ : ℝ) : ℂ)) + tail := by
  let z := Complex.exp ((θ : ℂ) * Complex.I)
  refine ⟨z ^ (2 * N), ∑ k ∈ Finset.range 3, z ^ (4 * N + 1 + k), ?_, ?_, ?_⟩
  · simp [z, norm_pow, Complex.norm_exp_ofReal_mul_I]
  · calc
      _ ≤ ∑ k ∈ Finset.range 3, ‖z ^ (4 * N + 1 + k)‖ := norm_sum_le _ _
      _ = 3 := by simp [z, norm_pow, Complex.norm_exp_ofReal_mul_I]
  · have he : coeffEval (IdealCVP.ofList (d := 4 * N + 4)
          (seedAssemble (4 * N + 4) (background (4 * N + 4)) (List.ofFn y))) z =
        ∑ i ∈ Finset.range (4 * N + 4), (assembledCoefficient N y i : ℂ) * z ^ i := by
      exact Fin.sum_univ_eq_sum_range
        (fun i => (assembledCoefficient N y i : ℂ) * z ^ i) (4 * N + 4)
    rw [he]
    rw [show 4 * N + 4 = (4 * N + 1) + 3 by omega, Finset.sum_range_add]
    change (∑ i ∈ Finset.range (4 * N + 1), (assembledCoefficient N y i : ℂ) * z ^ i) +
      (∑ k ∈ Finset.range 3, (assembledCoefficient N y (4 * N + 1 + k) : ℂ) *
        z ^ (4 * N + 1 + k)) = _
    rw [assembled_core N y hy θ]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [assembled_tail N y (Finset.mem_range.mp hk), Int.cast_one, one_mul]

end FlatFrontend
end Power2ModuleSVP
