module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Rational partial-coloring specifications

Finite rational contracts, encodings, and elementary potential and progress estimates for the
weighted coloring walk. The concrete semantic and runtime certificates are supplied by
Coloring/Trajectory/Basic.lean and Runtime/Coloring/Certificate.lean.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP

open scoped BigOperators

noncomputable section

def RationalCube {r : ℕ} (x : Fin r → ℚ) : Prop := ∀ j, |(x j : ℝ)| ≤ 1

def signCoordinateCount {r : ℕ} (x : Fin r → ℚ) : ℕ :=
  (Finset.univ.filter fun j => x j = -1 ∨ x j = 1).card

def coloringRowNorm {r : ℕ} (v : Fin r → ℚ) : ℝ :=
  Real.sqrt (∑ j, (v j : ℝ) ^ 2)

def coloringDiscrepancy {r : ℕ} (v x y : Fin r → ℚ) : ℝ :=
  |∑ j, (v j : ℝ) * ((y j : ℝ) - (x j : ℝ))|

def coloringEntropy {m : ℕ} (threshold : Fin m → ℚ) : ℝ :=
  ∑ i, Real.exp (-((threshold i : ℝ) ^ 2) / 16)

/-- The exact semantic output required in the partial-coloring lemma.
`r ≤ 2 * count` is equivalent to fixing at least `ceil(r/2)` coordinates. -/
def PartialColoringSpec {r m : ℕ} (V : Fin m → Fin r → ℚ)
    (x y : Fin r → ℚ) (threshold : Fin m → ℚ) : Prop :=
  RationalCube y ∧ r ≤ 2 * signCoordinateCount y ∧
    ∀ i, coloringDiscrepancy (V i) x y ≤
      68 * (threshold i : ℝ) * coloringRowNorm (V i)

/-- Input lists are an explicit matrix, starting vector and row thresholds. -/
abbrev PartialColoringInput := List (List ℚ) × (List ℚ × List ℚ)

/-- Canonical reduced numerator and denominator, both in existing binary
integer/natural encodings. Pair/list framing is reused from complexitylib. -/
def encColoringRational : ℚ ↪ List Bool :=
  ⟨fun x => Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encIntBin
      Turing.MultiTapeTM.encNat (x.num, x.den), by
    intro x y h
    have hp := (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encIntBin
      Turing.MultiTapeTM.encNat).injective h
    exact Rat.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)⟩

def encPartialColoring : PartialColoringInput ↪ List Bool :=
  Turing.MultiTapeTM.encPair
    (Turing.MultiTapeTM.encList (Turing.MultiTapeTM.encList encColoringRational))
    (Turing.MultiTapeTM.encPair
      (Turing.MultiTapeTM.encList encColoringRational)
      (Turing.MultiTapeTM.encList encColoringRational))

def partialColoringInput {r m : ℕ} (V : Fin m → Fin r → ℚ)
    (x : Fin r → ℚ) (threshold : Fin m → ℚ) : PartialColoringInput :=
  (List.ofFn (fun i => List.ofFn (V i)), (List.ofFn x, List.ofFn threshold))

/-- Unproved deterministic partial-coloring obligation, with the exact
constant 68 and the stated entropy budget. A single total algorithm works
for every matrix size; malformed inputs may have arbitrary outputs. -/
structure DeterministicPartialColoringHypothesis : Prop where
  exists_algorithm : ∃ F : PartialColoringInput → List ℚ,
    Turing.MultiTapeTM.ComputableTidilyInPolyTime F encPartialColoring
      (Turing.MultiTapeTM.encList encColoringRational) ∧
    ∀ (r m : ℕ) (V : Fin m → Fin r → ℚ) (x : Fin r → ℚ) (threshold : Fin m → ℚ),
      64 ≤ r → RationalCube x → (∀ i, 0 ≤ threshold i) →
      coloringEntropy threshold ≤ (r : ℝ) / 64 →
      ∃ y : Fin r → ℚ,
        F (partialColoringInput V x threshold) = List.ofFn y ∧
        PartialColoringSpec V x y threshold

/-- The quadratic update majorizes its exponential, on the full closed
range of step sizes used by the algorithm. -/
theorem coloring_quadratic_ge_exp {t : ℝ} (ht : |t| ≤ 1) :
    Real.exp t ≤ 1 + t + t ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le ht
  have h' := le_abs_self (Real.exp t - 1 - t)
  linarith

/-- The damping factor pays at most twice its exponent on the permitted range. -/
theorem coloring_damping_ge_exp {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1 / 2) :
    Real.exp (-2 * b) ≤ 1 - b := by
  have hpos : 0 < 1 - b := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hinv : (1 - b)⁻¹ ≤ 1 + 2 * b := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hpos).2
    nlinarith
  apply (Real.le_log_iff_exp_le hpos).1
  linarith

/-- The entropy budget leaves fewer than `r/16` small-threshold constraints,
as required in the dimension count for the rational subspace. -/
theorem coloring_small_threshold_count {r m : ℕ} (hr : 0 < r)
    (threshold : Fin m → ℚ) (hnonneg : ∀ i, 0 ≤ threshold i)
    (hbudget : coloringEntropy threshold ≤ (r : ℝ) / 32) :
    16 * (Finset.univ.filter fun i => threshold i ≤ 1).card < r := by
  let s := Finset.univ.filter fun i => threshold i ≤ 1
  have hsmall : (s.card : ℝ) * (15 / 16) ≤ coloringEntropy threshold := by
    calc
      (s.card : ℝ) * (15 / 16) = ∑ _i ∈ s, (15 / 16 : ℝ) := by simp
      _ ≤ ∑ i ∈ s, Real.exp (-((threshold i : ℝ) ^ 2) / 16) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : threshold i ≤ 1 := (Finset.mem_filter.mp hi).2
        have ha : (0 : ℝ) ≤ threshold i := by exact_mod_cast hnonneg i
        have hb : (threshold i : ℝ) ≤ 1 := by exact_mod_cast hi'
        have he := Real.add_one_le_exp (-((threshold i : ℝ) ^ 2) / 16)
        nlinarith [mul_nonneg ha (sub_nonneg.mpr hb)]
      _ ≤ coloringEntropy threshold := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
          (fun i hi his => (Real.exp_pos _).le)
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hcard : 16 * (s.card : ℝ) < r := by linarith
  exact_mod_cast hcard

/-- The unrounded potential does not increase when the linear term cancels
and the quadratic increase is paid for by the damping terms. -/
theorem coloring_potential_step {ι : Type*} [Fintype ι]
    (w b t : ι → ℝ)
    (hlinear : ∑ i, w i * (1 - b i) * t i = 0)
    (hquadratic : (∑ i, w i * (1 - b i) * (t i) ^ 2) ≤ ∑ i, w i * b i) :
    (∑ i, w i * (1 - b i) * (1 + t i + (t i) ^ 2)) ≤ ∑ i, w i := by
  have hid : (∑ i, w i * (1 - b i) * (1 + t i + (t i) ^ 2)) =
      (∑ i, w i) - (∑ i, w i * b i) + (∑ i, w i * (1 - b i) * t i) +
        ∑ i, w i * (1 - b i) * (t i) ^ 2 := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hid, hlinear]
  linarith

/-- Upward rounding contributes at most one mesh unit per row per step. -/
theorem coloring_rounded_potential_step {ι : Type*} [Fintype ι]
    (w b t w' : ι → ℝ) (η : ℝ)
    (hlinear : ∑ i, w i * (1 - b i) * t i = 0)
    (hquadratic : (∑ i, w i * (1 - b i) * (t i) ^ 2) ≤ ∑ i, w i * b i)
    (hround : ∀ i, w' i ≤ w i * (1 - b i) * (1 + t i + (t i) ^ 2) + η) :
    (∑ i, w' i) ≤ (∑ i, w i) + Fintype.card ι * η := by
  calc
    (∑ i, w' i) ≤ ∑ i, (w i * (1 - b i) * (1 + t i + (t i) ^ 2) + η) :=
      Finset.sum_le_sum (fun i _ => hround i)
    _ = (∑ i, w i * (1 - b i) * (1 + t i + (t i) ^ 2)) + Fintype.card ι * η := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by
      linarith [coloring_potential_step w b t hlinear hquadratic]

/-- The progress estimate behind the cubic bound on the number of full steps. -/
theorem coloring_full_step_progress {ι : Type*} [Fintype ι]
    (x z : ι → ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (horient : 0 ≤ ∑ j, x j * z j) (hz : (1 : ℝ) / 4 < ∑ j, (z j) ^ 2) :
    (∑ j, (x j) ^ 2) + Δ ^ 2 / 4 < ∑ j, (x j + Δ * z j) ^ 2 := by
  have hid : (∑ j, (x j + Δ * z j) ^ 2) =
      (∑ j, (x j) ^ 2) + 2 * Δ * (∑ j, x j * z j) + Δ ^ 2 * ∑ j, (z j) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hid]
  have hpos := mul_pos (sq_pos_of_pos hΔ) (sub_pos.mpr hz)
  have hnonneg := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Δ) horient
  nlinarith

/-- Rational nearest-sign rounding used at the terminal recursion level. -/
def nearestRationalSign (x : ℚ) : ℚ := if 0 ≤ x then 1 else -1

theorem nearestRationalSign_isSign (x : ℚ) :
    nearestRationalSign x = -1 ∨ nearestRationalSign x = 1 := by
  unfold nearestRationalSign
  split_ifs <;> simp

theorem nearestRationalSign_error {x : ℚ} (hx : |(x : ℝ)| ≤ 1) :
    |(nearestRationalSign x : ℝ) - (x : ℝ)| ≤ 1 := by
  rcases abs_le.mp hx with ⟨hx₁, hx₂⟩
  unfold nearestRationalSign
  split_ifs with h
  · have h' : (0 : ℝ) ≤ x := by exact_mod_cast h
    norm_num
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have h' : (x : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge h)
    norm_num
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem nearestRationalSign_discrepancy {r : ℕ} (v x : Fin r → ℚ)
    (hx : RationalCube x) {B : ℝ} (hB : 0 ≤ B) (hv : ∀ j, |(v j : ℝ)| ≤ B) :
    coloringDiscrepancy v x (fun j => nearestRationalSign (x j)) ≤ r * B := by
  unfold coloringDiscrepancy
  calc
    _ ≤ ∑ j, |(v j : ℝ) * ((nearestRationalSign (x j) : ℝ) - (x j : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin r, B := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      simpa using mul_le_mul (hv j) (nearestRationalSign_error (hx j)) (abs_nonneg _) hB
    _ = _ := by simp

theorem nearestRationalSign_count {r : ℕ} (x : Fin r → ℚ) :
    signCoordinateCount (fun j => nearestRationalSign (x j)) = r := by
  simp [signCoordinateCount, nearestRationalSign_isSign]

/-- The small-dimension terminal case used by the full-coloring recursion. -/
theorem nearestRationalSign_small_discrepancy {r : ℕ} (hr : r ≤ 64)
    (v x : Fin r → ℚ) (hx : RationalCube x) {B : ℝ}
    (hB : 0 ≤ B) (hv : ∀ j, |(v j : ℝ)| ≤ B) :
    coloringDiscrepancy v x (fun j => nearestRationalSign (x j)) ≤
      8 * Real.sqrt r * B := by
  have hsq := Real.sq_sqrt (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have hs := Real.sqrt_nonneg (r : ℝ)
  have hr' : (r : ℝ) ≤ 64 := by exact_mod_cast hr
  have hs' : Real.sqrt r ≤ 8 := by nlinarith
  have hcoeff : (r : ℝ) ≤ 8 * Real.sqrt r := by nlinarith
  exact (nearestRationalSign_discrepancy v x hx hB hv).trans
    (mul_le_mul_of_nonneg_right hcoeff hB)

/-- The constants in the full-coloring induction close without a decimal
approximation to the square root. -/
theorem fullColoring_constant_recurrence {c : ℝ} (hc : 0 ≤ c) :
    68 * c + (240 * (c + 4) + 2400) / Real.sqrt 2 ≤ 240 * c + 2400 := by
  have hspos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs : (7 : ℝ) / 5 ≤ Real.sqrt 2 := by nlinarith
  have hratio : (240 * (c + 4) + 2400) / Real.sqrt 2 ≤ 172 * c + 2400 := by
    apply (div_le_iff₀ hspos).2
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hs)]
  linarith

end

end Power2ModuleSVP
