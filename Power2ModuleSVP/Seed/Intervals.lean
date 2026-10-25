module

public import Power2ModuleSVP.Seed.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Intervals

Certified sampling estimates for `lem:seed-intervals`. The exact integer
Chebyshev polynomial and rational comparison are kept separate from the real
angle used in the proof. The seven-cell exclusion and the multiplicity-aware
component count are not asserted by this file.

Paper: `paper/power2svp.pdf`, Appendix A.1 (Lemma 9, Rudin–Shapiro waves and small intervals).
-/

@[expose] public section

namespace Power2ModuleSVP

open Polynomial
open scoped BigOperators

noncomputable section

/-- Sparse cosine data with at most `N` terms and frequencies at most `2N`.
Zeros are permitted in order to represent an omitted frequency. -/
structure SeedCosineData (N : ℕ) where
  support : Finset ℕ
  coeff : ℕ → ℤ
  card_le : support.card ≤ N
  frequency_le : ∀ j ∈ support, j ≤ 2 * N
  coeff_le : ∀ j ∈ support, |(coeff j : ℝ)| ≤ 1

namespace SeedCosineData

def integerPolynomial {N : ℕ} (c : SeedCosineData N) : ℤ[X] :=
  ∑ j ∈ c.support, Polynomial.C (c.coeff j) * Chebyshev.T ℤ j

def realPolynomial {N : ℕ} (c : SeedCosineData N) : ℝ[X] :=
  cosinePolynomial c.support (fun j => c.coeff j)

theorem map_integerPolynomial {N : ℕ} (c : SeedCosineData N) :
    c.integerPolynomial.map (Int.castRingHom ℝ) = c.realPolynomial := by
  simp [integerPolynomial, realPolynomial, cosinePolynomial, Polynomial.map_sum,
    Chebyshev.map_T]

/-- Rational evaluations are exact images of the integer polynomial. -/
theorem rational_eval {N : ℕ} (c : SeedCosineData N) (y : ℚ) :
    (((c.integerPolynomial.map (Int.castRingHom ℚ)).eval y : ℚ) : ℝ) =
      c.realPolynomial.eval (y : ℝ) := by
  rw [← c.map_integerPolynomial]
  change (Rat.castHom ℝ) ((c.integerPolynomial.map (Int.castRingHom ℚ)).eval y) = _
  rw [← eval₂_at_apply (Rat.castHom ℝ) y, eval₂_eq_eval_map, Polynomial.map_map]
  rfl

private theorem weighted_square_bound {N : ℕ} (c : SeedCosineData N) :
    (∑ j ∈ c.support, |(c.coeff j : ℝ)| * (j : ℝ) ^ 2) ≤ 4 * (N : ℝ) ^ 3 := by
  calc
    (∑ j ∈ c.support, |(c.coeff j : ℝ)| * (j : ℝ) ^ 2)
        ≤ ∑ _j ∈ c.support, (2 * (N : ℝ)) ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hf : (j : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast c.frequency_le j hj
          have hc := c.coeff_le j hj
          nlinarith [sq_nonneg ((j : ℝ) - 2 * N)]
    _ = (c.support.card : ℝ) * (2 * (N : ℝ)) ^ 2 := by simp
    _ ≤ (N : ℝ) * (2 * (N : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast c.card_le) (sq_nonneg _)
    _ = _ := by ring

theorem polynomial_derivative_bound {N : ℕ} (c : SeedCosineData N)
    {y : ℝ} (hy : y ∈ Set.Icc (-1) 1) :
    |c.realPolynomial.derivative.eval y| ≤ 8 * (N : ℝ) ^ 3 := by
  have h := (cosinePolynomial_derivative_bound c.support (fun j => c.coeff j) hy).trans
    c.weighted_square_bound
  exact h.trans (by nlinarith [pow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) 3])

theorem polynomial_sub_bound {N : ℕ} (c : SeedCosineData N)
    {x y : ℝ} (hx : x ∈ Set.Icc (-1) 1) (hy : y ∈ Set.Icc (-1) 1) :
    |c.realPolynomial.eval y - c.realPolynomial.eval x| ≤
      8 * (N : ℝ) ^ 3 * |y - x| := by
  have h := cosinePolynomial_eval_sub_bound c.support (fun j => c.coeff j) hx hy
  exact h.trans (mul_le_mul_of_nonneg_right
    (c.weighted_square_bound.trans
      (by nlinarith [pow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) 3])) (abs_nonneg _))

/-- The angular estimate uses only the signed support, rather than sharp Bernstein. -/
theorem angle_sub_bound {N : ℕ} (c : SeedCosineData N) (θ φ : ℝ) :
    |c.realPolynomial.eval (Real.cos θ) - c.realPolynomial.eval (Real.cos φ)| ≤
      2 * (N : ℝ) ^ 2 * |θ - φ| := by
  simp only [realPolynomial, cosinePolynomial_eval_cos, ← Finset.sum_sub_distrib,
    ← mul_sub]
  calc
    |∑ j ∈ c.support, (c.coeff j : ℝ) * (Real.cos (j * θ) - Real.cos (j * φ))|
        ≤ ∑ j ∈ c.support, |(c.coeff j : ℝ) *
          (Real.cos (j * θ) - Real.cos (j * φ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ c.support, 2 * (N : ℝ) * |θ - φ| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      have hf : (j : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast c.frequency_le j hj
      have hc := c.coeff_le j hj
      have hcos := Real.abs_cos_sub_cos_le ((j : ℝ) * θ) (j * φ)
      have hjabs : |(j : ℝ)| = j := abs_of_nonneg (Nat.cast_nonneg j)
      rw [← mul_sub, abs_mul, hjabs] at hcos
      calc
        _ ≤ 1 * ((j : ℝ) * |θ - φ|) := mul_le_mul hc hcos (abs_nonneg _) zero_le_one
        _ ≤ 2 * (N : ℝ) * |θ - φ| := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hf (abs_nonneg (θ - φ))
    _ = (c.support.card : ℝ) * (2 * N * |θ - φ|) := by simp
    _ ≤ (N : ℝ) * (2 * N * |θ - φ|) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast c.card_le) (by positivity)
    _ = _ := by ring

end SeedCosineData

/-- Real location of a fine sample. -/
def seedFineAngle (M r : ℕ) : ℝ := r * Real.pi / M

/-- The rational grid contract. Symmetry and endpoints are exact. Its
construction and time bound are separate obligations. -/
structure RationalCosineGrid (M : ℕ) (η : ℝ) where
  sample : ℕ → ℚ
  first : sample 0 = 1
  last : sample M = -1
  decreasing : StrictAntiOn sample (Set.Icc 0 M)
  reflected : ∀ r ≤ M, sample (M - r) = -sample r
  error : ∀ r ≤ M, |(sample r : ℝ) - Real.cos (seedFineAngle M r)| ≤ η

theorem RationalCosineGrid.mem_Icc {M : ℕ} {η : ℝ}
    (g : RationalCosineGrid M η) {r : ℕ} (hr : r ≤ M) :
    (g.sample r : ℝ) ∈ Set.Icc (-1) 1 := by
  have ha := g.decreasing.antitoneOn ⟨Nat.zero_le r, hr⟩ ⟨Nat.zero_le M, le_rfl⟩ hr
  have hb := g.decreasing.antitoneOn ⟨le_rfl, Nat.zero_le M⟩ ⟨Nat.zero_le r, hr⟩
    (Nat.zero_le r)
  rw [g.last] at ha
  rw [g.first] at hb
  constructor
  · exact_mod_cast ha
  · exact_mod_cast hb

/-- A closed coarse cell tests both of its endpoints, inclusively. -/
def seedCellMarked {N M : ℕ} (c : SeedCosineData N) {η : ℝ}
    (g : RationalCosineGrid M η) (R : ℕ) (h : ℚ) (j : ℕ) : Prop :=
  ∃ r : ℕ, j * R ≤ r ∧ r ≤ (j + 1) * R ∧
    |(c.integerPolynomial.map (Int.castRingHom ℚ)).eval (g.sample r)| ≤ 3 * h / 4

/-- Any marked sample supplies the low-value witness used in the seven-cell
argument, with exactly the manuscript's `13/16` margin. -/
theorem seed_marked_sample_bound {N M : ℕ} (c : SeedCosineData N) {η h : ℝ}
    (g : RationalCosineGrid M η) {r : ℕ} (hr : r ≤ M)
    (hη : 8 * (N : ℝ) ^ 3 * η ≤ h / 16)
    (hmark : |c.realPolynomial.eval (g.sample r : ℝ)| ≤ 3 * h / 4) :
    |c.realPolynomial.eval (Real.cos (seedFineAngle M r))| ≤ 13 * h / 16 := by
  have herr := c.polynomial_sub_bound (g.mem_Icc hr)
    (show Real.cos (seedFineAngle M r) ∈ Set.Icc (-1) 1 from
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  have hdiff := herr.trans (mul_le_mul_of_nonneg_left
    (show |Real.cos (seedFineAngle M r) - (g.sample r : ℝ)| ≤ η from
      by simpa only [abs_sub_comm] using g.error r hr) (by positivity))
  have hab := abs_add_le
    (c.realPolynomial.eval (Real.cos (seedFineAngle M r)) -
      c.realPolynomial.eval (g.sample r : ℝ))
    (c.realPolynomial.eval (g.sample r : ℝ))
  simp only [sub_add_cancel] at hab
  linarith

/-- An unmarked sample controls every angle within one fine-grid spacing.
The two error allowances are stated as inequalities, so any certified grid
construction satisfying the prescribed parameters can use the lemma. -/
theorem seed_unmarked_nearby_bound {N M : ℕ} (c : SeedCosineData N) {η h θ : ℝ}
    (g : RationalCosineGrid M η) (hh : 0 < h) {r : ℕ} (hr : r ≤ M)
    (hη : 8 * (N : ℝ) ^ 3 * η ≤ h / 16)
    (hspacing : 2 * (N : ℝ) ^ 2 * |θ - seedFineAngle M r| ≤ Real.pi * h / 64)
    (hgood : 3 * h / 4 < |c.realPolynomial.eval (g.sample r : ℝ)|) :
    5 * h / 8 < |c.realPolynomial.eval (Real.cos θ)| := by
  have hp := c.polynomial_sub_bound (g.mem_Icc hr)
    (show Real.cos (seedFineAngle M r) ∈ Set.Icc (-1) 1 from
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  have hp' := hp.trans (mul_le_mul_of_nonneg_left
    (show |Real.cos (seedFineAngle M r) - (g.sample r : ℝ)| ≤ η from
      by simpa only [abs_sub_comm] using g.error r hr) (by positivity))
  have ha := (c.angle_sub_bound θ (seedFineAngle M r)).trans hspacing
  have hb := abs_sub_abs_le_abs_sub (c.realPolynomial.eval (g.sample r : ℝ))
    (c.realPolynomial.eval (Real.cos (seedFineAngle M r)))
  rw [abs_sub_comm] at hb
  have hc := abs_sub_abs_le_abs_sub (c.realPolynomial.eval (Real.cos (seedFineAngle M r)))
    (c.realPolynomial.eval (Real.cos θ))
  rw [abs_sub_comm] at hc
  have hpi : Real.pi * h < 4 * h := mul_lt_mul_of_pos_right Real.pi_lt_four hh
  linarith

/-- The executable rational marking test implies a witness in the same
closed coarse cell. No approximate real comparison enters the test. -/
theorem seed_marked_cell_witness {N R M : ℕ} (c : SeedCosineData N)
    {η : ℝ} (g : RationalCosineGrid M η) (h : ℚ) (hM : M = N * R)
    (hη : 8 * (N : ℝ) ^ 3 * η ≤ (h : ℝ) / 16) {j : ℕ} (hj : j < N)
    (hmark : seedCellMarked c g R h j) :
    ∃ r : ℕ, j * R ≤ r ∧ r ≤ (j + 1) * R ∧
      |c.realPolynomial.eval (Real.cos (seedFineAngle M r))| ≤ 13 * (h : ℝ) / 16 := by
  obtain ⟨r, hleft, hright, heval⟩ := hmark
  have hr : r ≤ M := by
    rw [hM]
    exact hright.trans (Nat.mul_le_mul_right R (by omega))
  refine ⟨r, hleft, hright, seed_marked_sample_bound c g hr hη ?_⟩
  rw [← c.rational_eval]
  exact_mod_cast heval

/-- The complementary estimate uses the same exact closed-cell test. A
nearby sample inside that cell suffices to certify the `5/8` lower margin. -/
theorem seed_unmarked_cell_bound {N R M : ℕ} (c : SeedCosineData N)
    {η θ : ℝ} (g : RationalCosineGrid M η) (h : ℚ) (hh : 0 < h)
    (hM : M = N * R) (hη : 8 * (N : ℝ) ^ 3 * η ≤ (h : ℝ) / 16)
    {j r : ℕ} (hj : j < N) (hleft : j * R ≤ r) (hright : r ≤ (j + 1) * R)
    (hspacing : 2 * (N : ℝ) ^ 2 * |θ - seedFineAngle M r| ≤ Real.pi * (h : ℝ) / 64)
    (hgood : ¬ seedCellMarked c g R h j) :
    5 * (h : ℝ) / 8 < |c.realPolynomial.eval (Real.cos θ)| := by
  have hr : r ≤ M := by
    rw [hM]
    exact hright.trans (Nat.mul_le_mul_right R (by omega))
  apply seed_unmarked_nearby_bound c g (by exact_mod_cast hh) hr hη hspacing
  rw [← c.rational_eval]
  have htest : 3 * h / 4 <
      |(c.integerPolynomial.map (Int.castRingHom ℚ)).eval (g.sample r)| := by
    apply lt_of_not_ge
    intro hbad
    exact hgood ⟨r, hleft, hright, hbad⟩
  exact_mod_cast htest

/-- Perturbed nodes remain ordered whenever adjacent exact nodes are farther
apart than twice the enclosure error. This includes errors of either sign. -/
theorem rational_samples_strictly_ordered {x y a b η : ℝ}
    (hx : |a - x| ≤ η) (hy : |b - y| ≤ η) (hgap : 2 * η < x - y) : b < a := by
  rcases abs_le.mp hx with ⟨hx₁, hx₂⟩
  rcases abs_le.mp hy with ⟨hy₁, hy₂⟩
  linarith

/-- The unresolved multiplicity-aware component theorem used in the interval
count. Isolated tangencies are allowed (`left i = right i`). Endpoint
avoidance rules out the constant-zero threshold polynomial. This is a
mathematical obligation only, with no root-finding or runtime claim. -/
structure PolynomialSublevelComponentsHypothesis : Prop where
  components : ∀ (p : ℝ[X]) (τ : ℝ), 0 < τ →
    τ < |p.eval (-1)| → τ < |p.eval 1| →
    ∃ (k : ℕ) (left right : Fin k → ℝ),
      k ≤ p.natDegree ∧
      (∀ i, -1 < left i ∧ left i ≤ right i ∧ right i < 1) ∧
      (∀ i j, i ≠ j → right i < left j ∨ right j < left i) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1,
        |p.eval x| ≤ τ ↔ ∃ i, x ∈ Set.Icc (left i) (right i))

end

end Power2ModuleSVP
