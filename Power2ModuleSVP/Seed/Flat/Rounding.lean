module
public import Power2ModuleSVP.Coloring.Full
public import Power2ModuleSVP.Seed.Flat.Taylor
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Rounding

Error transfer from rational coloring rows, and the finite derivative grid.
The integer thresholds `12 + ell` are upper enclosures sufficient for the
second coloring and avoid computing logarithms for that step.

Paper: `paper/power2svp.pdf`, Appendix A (Theorem 5, the deterministic flat seed).
-/
@[expose] public section
namespace Power2ModuleSVP
open scoped BigOperators

/-- A supplied full-coloring program has exactly the semantic contract
proved in `Coloring/Full.lean`; a runtime certificate is a separate premise. -/
def FullColoringCorrect (F : PartialColoringInput → List ℚ) : Prop :=
  ∀ (r m : ℕ) (V : Fin m → Fin r → ℚ) (x : Fin r → ℚ) (c : Fin m → ℚ),
    RationalCube x → (∀ i, 0 ≤ c i) → coloringEntropy c ≤ (r : ℝ) / 64 →
    ∃ y : Fin r → ℚ, F (partialColoringInput V x c) = List.ofFn y ∧
      FullColoringSpec V x y c

theorem fullColoringCorrect_of_partial (P : PartialColoringInput → List ℚ)
    (hP : PartialColoringCorrect P) : FullColoringCorrect (fullColor P) := by
  intro r m V x c hx hc he
  exact fullColor_spec P hP r m V x c hx hc he

/-- The empty interval branch has zero rows as well as zero columns. Its
entropy is zero, and every correct full-coloring routine returns the empty
word. This avoids an impossible positive-entropy premise in dimension zero. -/
theorem fullColoringCorrect_empty (F : PartialColoringInput → List ℚ)
    (hF : FullColoringCorrect F) : F ([], ([], [])) = [] := by
  let V : Fin 0 → Fin 0 → ℚ := fun i => Fin.elim0 i
  let x : Fin 0 → ℚ := fun i => Fin.elim0 i
  obtain ⟨y, hy, _⟩ := hF 0 0 V x x (by intro i; exact Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) (by simp [coloringEntropy])
  simpa [partialColoringInput] using hy

/-- A real row and its rational approximation, with a separately rounded
starting point. This charges both matrix error and starting-point error. -/
theorem seed_rational_row_transfer {r : ℕ} (v b : Fin r → ℝ)
    (q x y : Fin r → ℚ) {ε D : ℝ}
    (hv : ∀ j, |v j| ≤ 1) (hq : ∀ j, |v j - q j| ≤ ε)
    (hx : RationalCube x) (hy : RationalCube y)
    (hb : ∀ j, |(x j : ℝ) - b j| ≤ ε)
    (hdisc : coloringDiscrepancy q x y ≤ D) :
    |∑ j, v j * ((y j : ℝ) - b j)| ≤ D + 3 * r * ε := by
  by_cases hr : r = 0
  · subst r
    simpa [coloringDiscrepancy] using hdisc
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hq ⟨0, Nat.pos_of_ne_zero hr⟩)
  have hstep (j : Fin r) : |(y j : ℝ) - x j| ≤ 2 := by
    exact (abs_sub _ _).trans (by linarith [hx j, hy j])
  have herr : |∑ j, (v j - q j) * ((y j : ℝ) - x j)| ≤ 2 * r * ε := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j : Fin r, ε * 2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hq j) (hstep j) (abs_nonneg _) hε
      _ = _ := by simp; ring
  have hstart : |∑ j, v j * ((x j : ℝ) - b j)| ≤ r * ε := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j : Fin r, 1 * ε := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hv j) (hb j) (abs_nonneg _) (by norm_num)
      _ = _ := by simp
  have heq : (∑ j, v j * ((y j : ℝ) - b j)) =
      (∑ j, (q j : ℝ) * ((y j : ℝ) - x j)) +
      (∑ j, (v j - q j) * ((y j : ℝ) - x j)) +
      ∑ j, v j * ((x j : ℝ) - b j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  have hh := abs_add_le
    ((∑ j, (q j : ℝ) * ((y j : ℝ) - x j)) +
      ∑ j, (v j - q j) * ((y j : ℝ) - x j))
    (∑ j, v j * ((x j : ℝ) - b j))
  have hh' := abs_add_le (∑ j, (q j : ℝ) * ((y j : ℝ) - x j))
    (∑ j, (v j - q j) * ((y j : ℝ) - x j))
  unfold coloringDiscrepancy at hdisc
  linarith

/-- Sample centers for the second coloring, with zero-based indexing. -/
noncomputable def seedDerivativeAngle (N k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 1) * Real.pi / (64 * N)

/-- Every point of the closed first quadrant is close to an actual sample,
including both endpoints. -/
theorem seed_derivative_grid_covers {N : ℕ} (hN : 0 < N) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    ∃ k : Fin (16 * N),
      (2 * (N : ℝ)) * |θ - seedDerivativeAngle N k| ≤ 1 / 10 := by
  let u : ℝ := 32 * N * θ / Real.pi
  have hu : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg (mul_nonneg (by positivity) hθ.1) Real.pi_pos.le
  have hu' : u ≤ 16 * N := by
    dsimp [u]
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [hθ.2]
  let k : ℕ := min ⌊u⌋₊ (16 * N - 1)
  have hk : k < 16 * N := by dsimp [k]; omega
  have hkl : (k : ℝ) ≤ u := by
    have hh : (k : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast (min_le_left ⌊u⌋₊ (16 * N - 1))
    exact hh.trans (Nat.floor_le hu)
  have hkr : u ≤ (k : ℝ) + 1 := by
    by_cases hf : ⌊u⌋₊ ≤ 16 * N - 1
    · dsimp [k]
      rw [min_eq_left hf]
      exact (Nat.lt_floor_add_one u).le
    · have he : k + 1 = 16 * N := by dsimp [k]; omega
      have he' : (k : ℝ) + 1 = 16 * N := by exact_mod_cast he
      linarith
  refine ⟨⟨k, hk⟩, ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hcenter : |u - ((k : ℝ) + 1 / 2)| ≤ 1 / 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hid : 2 * (N : ℝ) * (θ - seedDerivativeAngle N k) =
      (Real.pi / 16) * (u - ((k : ℝ) + 1 / 2)) := by
    dsimp [seedDerivativeAngle, u]
    field_simp
    ring
  change 2 * (N : ℝ) * |θ - seedDerivativeAngle N k| ≤ 1 / 10
  rw [show 2 * (N : ℝ) * |θ - seedDerivativeAngle N k| =
      |2 * (N : ℝ) * (θ - seedDerivativeAngle N k)| by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * N)], hid,
    abs_mul, abs_of_pos (by positivity : 0 < Real.pi / 16)]
  have hh := mul_le_mul_of_nonneg_left hcenter
    (by positivity : 0 ≤ Real.pi / 16)
  linarith [Real.pi_lt_d2]

/-- The rational integer thresholds have the requisite exponential decay. -/
theorem seed_derivative_threshold (ell : ℕ) :
    Real.exp (-((12 + (ell : ℝ)) ^ 2) / 16) ≤ (1 / 2 : ℝ) ^ (11 + ell) := by
  have he : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [← he, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have hm := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ 11 + ell by positivity)
  push_cast
  nlinarith [sq_nonneg (ell : ℝ)]

/-- The complete finite derivative-grid entropy budget, including all
`16*N` samples and every derivative from zero through `N`. -/
theorem seed_derivative_entropy (N : ℕ) :
    (∑ ell : Fin (N + 1), ∑ _k : Fin (16 * N),
      Real.exp (-((12 + (ell : ℝ)) ^ 2) / 16)) ≤ (N : ℝ) / 64 := by
  have hg : HasSum (fun ell : ℕ => (1 / 2 : ℝ) ^ (11 + ell)) (1 / 1024) := by
    have hh := (hasSum_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left (1 / 2048)
    convert hh using 1
    · funext ell
      rw [pow_add]
      norm_num
    · norm_num
  have hsum : (∑ ell : Fin (N + 1),
      Real.exp (-((12 + (ell : ℝ)) ^ 2) / 16)) ≤ 1 / 1024 := by
    calc
      _ ≤ ∑ ell : Fin (N + 1), (1 / 2 : ℝ) ^ (11 + ell.val) :=
        Finset.sum_le_sum (fun ell _ => seed_derivative_threshold ell)
      _ = ∑ ell ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ (11 + ell) :=
        Fin.sum_univ_eq_sum_range (fun ell : ℕ => (1 / 2 : ℝ) ^ (11 + ell)) (N + 1)
      _ ≤ _ := (hg.summable.sum_le_tsum _ (fun _ _ => by positivity)).trans_eq hg.tsum_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat]
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 16 * N)
  nlinarith

/-- A fixed rational precision sufficient for derivative rounding. Its bit
length is logarithmic in `N`, and it leaves a whole unit in the jet constant. -/
def seedRoundingError (N : ℕ) : ℚ := 1 / (2 ^ 20 * ((N : ℚ) + 1) ^ 2)

theorem seed_rounding_allowance {N ell : ℕ} (hN : 1 ≤ N) (hell : ell ≤ N) :
    (5280 + 240 * (ell : ℝ)) * (1 + (seedRoundingError N : ℝ)) * Real.sqrt N +
      3 * N * (seedRoundingError N : ℝ) ≤
    (5281 + 240 * (ell : ℝ)) * Real.sqrt N := by
  have he : (seedRoundingError N : ℝ) = 1 / (2 ^ 20 * ((N : ℝ) + 1) ^ 2) := by
    simp [seedRoundingError]
  have hpos : (0 : ℝ) < 2 ^ 20 * ((N : ℝ) + 1) ^ 2 := by positivity
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : (ell : ℝ) ≤ N := by exact_mod_cast hell
  have hs : 1 ≤ Real.sqrt (N : ℝ) :=
    (Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)).mpr (by simpa using hn)
  have hε : 0 ≤ (seedRoundingError N : ℝ) := by rw [he]; positivity
  have hc : (5280 + 243 * (N : ℝ)) * (seedRoundingError N : ℝ) ≤ 1 := by
    rw [he, mul_one_div]
    apply (div_le_iff₀ hpos).mpr
    norm_num
    nlinarith [sq_nonneg (N : ℝ)]
  have hm := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg N)
  have htail : 3 * N * (seedRoundingError N : ℝ) ≤
      3 * N * (seedRoundingError N : ℝ) * Real.sqrt N := by
    have hh := mul_le_mul_of_nonneg_left hs
      (show (0 : ℝ) ≤ 3 * N * (seedRoundingError N : ℝ) by positivity)
    simpa using hh
  have hl' := mul_le_mul_of_nonneg_right hl
    (show (0 : ℝ) ≤ 240 * (seedRoundingError N : ℝ) * Real.sqrt N by positivity)
  nlinarith

/-- The full rational rounding estimate for one normalized derivative row.
The output vector is a sign vector, the initial vector is in the cube, and
both enclosures use the explicit rational precision above. -/
theorem seed_rounding_row_bound {N ell : ℕ} (hN : 1 ≤ N) (hell : ell ≤ N)
    (v b : Fin N → ℝ) (q x y : Fin N → ℚ)
    (hv : ∀ j, |v j| ≤ 1)
    (hq : ∀ j, |v j - q j| ≤ (seedRoundingError N : ℝ))
    (hx : RationalCube x) (hy : ∀ j, y j = -1 ∨ y j = 1)
    (hb : ∀ j, |(x j : ℝ) - b j| ≤ (seedRoundingError N : ℝ))
    (hd : coloringDiscrepancy q x y ≤
      (5280 + 240 * (ell : ℝ)) * Real.sqrt N * coloringRowSup q) :
    |∑ j, v j * ((y j : ℝ) - b j)| ≤
      (5281 + 240 * (ell : ℝ)) * Real.sqrt N := by
  have hε : 0 ≤ (seedRoundingError N : ℝ) := by
    simp only [seedRoundingError, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_ofNat, Rat.cast_add, Rat.cast_natCast]
    positivity
  have hsup : coloringRowSup q ≤ 1 + (seedRoundingError N : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    rw [Real.norm_eq_abs]
    have hh := abs_add_le (v j) ((q j : ℝ) - v j)
    rw [add_sub_cancel, abs_sub_comm] at hh
    linarith [hv j, hq j]
  have hy' : RationalCube y := by
    intro j
    rcases hy j with h | h <;> simp [h]
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hsup
    (by positivity : 0 ≤ (5280 + 240 * (ell : ℝ)) * Real.sqrt N))
  have hrow := seed_rational_row_transfer v b q x y hv hq hx hy' hb hd'
  have hallow := seed_rounding_allowance hN hell
  nlinarith

end Power2ModuleSVP
