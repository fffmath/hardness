module

public import Power2ModuleSVP.Coloring.Partial.Specification
public import Mathlib.Data.Finset.Sort

/-!
# Full Bookkeeping

Finite bookkeeping for the full-coloring recursion. The executable routines
use rational equality, sorted finite coordinate sets, and list operations.
The entropy comparison is used only in their correctness proofs.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP

open scoped BigOperators

namespace Coloring

/-- The coordinates already equal to one or minus one. -/
def signSet {r : ℕ} (x : Fin r → ℚ) : Finset (Fin r) :=
  Finset.univ.filter fun j => x j = -1 ∨ x j = 1

/-- Retain exactly the requested number of sign coordinates when enough
are available. The order is the ordinary coordinate order. -/
def fixedSet {r : ℕ} (x : Fin r → ℚ) : Finset (Fin r) :=
  (((signSet x).sort (· ≤ ·)).take (r - r / 2)).toFinset

/-- The coordinates left available after selecting the fixed sign coordinates. -/
def activeSet {r : ℕ} (x : Fin r → ℚ) : Finset (Fin r) :=
  Finset.univ \ fixedSet x

theorem fixedSet_subset {r : ℕ} (x : Fin r → ℚ) : fixedSet x ⊆ signSet x := by
  intro j hj
  apply (Finset.mem_sort (· ≤ ·)).mp
  exact List.mem_of_mem_take (List.mem_toFinset.mp hj)

theorem activeSet_card {r : ℕ} (x : Fin r → ℚ)
    (hx : r ≤ 2 * signCoordinateCount x) : (activeSet x).card = r / 2 := by
  have hs : r - r / 2 ≤ (signSet x).card := by
    change r ≤ 2 * (signSet x).card at hx
    omega
  have hf : (fixedSet x).card = r - r / 2 := by
    unfold fixedSet
    rw [List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).take),
      List.length_take, Finset.length_sort, Nat.min_eq_left hs]
  rw [activeSet, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, hf]
  omega

/-- Enumerate a finite set of coordinates in increasing order. -/
def embed {r : ℕ} (A : Finset (Fin r)) : Fin A.card ↪o Fin r := A.orderEmbOfFin rfl

/-- Replace the coordinates in `A` by an enumerated vector, keeping the others from `y`. -/
def extend {r : ℕ} (A : Finset (Fin r)) (y : Fin r → ℚ)
    (z : Fin A.card → ℚ) : Fin r → ℚ := fun j =>
  if h : j ∈ A then z ((A.orderIsoOfFin rfl).symm ⟨j, h⟩) else y j

@[simp] theorem extend_embed {r : ℕ} (A : Finset (Fin r)) (y : Fin r → ℚ)
    (z : Fin A.card → ℚ) (j : Fin A.card) : extend A y z (embed A j) = z j := by
  simp only [extend, embed, Finset.orderEmbOfFin_mem, ↓reduceDIte]
  congr 1
  exact (A.orderIsoOfFin rfl).symm_apply_apply j

theorem extend_outside {r : ℕ} (A : Finset (Fin r)) (y : Fin r → ℚ)
    (z : Fin A.card → ℚ) (j : Fin r) (hj : j ∉ A) : extend A y z j = y j := by
  simp [extend, hj]

theorem extend_signs {r : ℕ} (y : Fin r → ℚ) (z : Fin (activeSet y).card → ℚ)
    (hz : ∀ j, z j = -1 ∨ z j = 1) :
    ∀ j, extend (activeSet y) y z j = -1 ∨ extend (activeSet y) y z j = 1 := by
  intro j
  by_cases hj : j ∈ activeSet y
  · simp only [extend, hj, ↓reduceDIte]
    exact hz _
  · rw [extend_outside _ _ _ j hj]
    have hf : j ∈ fixedSet y := by simpa [activeSet] using hj
    exact (Finset.mem_filter.mp (fixedSet_subset y hf)).2

theorem sum_embed {r : ℕ} (A : Finset (Fin r)) (f : Fin r → ℝ) :
    (∑ j : Fin A.card, f (embed A j)) = ∑ j ∈ A, f j := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ A rfl, Finset.sum_map]
  rfl

theorem sum_supported {r : ℕ} (A : Finset (Fin r)) (f : Fin r → ℝ)
    (hf : ∀ j ∉ A, f j = 0) :
    (∑ j, f j) = ∑ j : Fin A.card, f (embed A j) := by
  rw [sum_embed]
  exact (Finset.sum_subset (Finset.subset_univ A) fun j _ hj => hf j hj).symm

theorem discrepancy_extend {r : ℕ} (A : Finset (Fin r)) (v y : Fin r → ℚ)
    (z : Fin A.card → ℚ) :
    coloringDiscrepancy v y (extend A y z) =
      coloringDiscrepancy (fun j => v (embed A j)) (fun j => y (embed A j)) z := by
  unfold coloringDiscrepancy
  congr 1
  rw [sum_supported A _ (by
    intro j hj
    rw [extend_outside _ _ _ j hj, sub_self, mul_zero])]
  simp only [extend_embed]

end Coloring

theorem coloringDiscrepancy_triangle {r : ℕ} (v x y z : Fin r → ℚ) :
    coloringDiscrepancy v x z ≤
      coloringDiscrepancy v x y + coloringDiscrepancy v y z := by
  unfold coloringDiscrepancy
  have hid : (∑ j, (v j : ℝ) * ((z j : ℝ) - (x j : ℝ))) =
      (∑ j, (v j : ℝ) * ((y j : ℝ) - (x j : ℝ))) +
      ∑ j, (v j : ℝ) * ((z j : ℝ) - (y j : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hid]
  exact abs_add_le _ _

theorem coloringRowNorm_le_sqrt_mul {r : ℕ} (v : Fin r → ℚ) {B : ℝ}
    (hB : 0 ≤ B) (hv : ∀ j, |(v j : ℝ)| ≤ B) :
    coloringRowNorm v ≤ Real.sqrt r * B := by
  have hh : (∑ j, (v j : ℝ) ^ 2) ≤ (r : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin r, B ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hv j)
      _ = _ := by simp
  unfold coloringRowNorm
  calc
    _ ≤ Real.sqrt ((r : ℝ) * B ^ 2) := Real.sqrt_le_sqrt hh
    _ = Real.sqrt r * B := by rw [Real.sqrt_mul (Nat.cast_nonneg r), Real.sqrt_sq hB]

/-- Adding four to each threshold pays for a floor-halving of the dimension.
The dimension premise explicitly handles odd dimensions. -/
theorem coloringEntropy_add_four {r m : ℕ} (hr : 5 ≤ r) (c : Fin m → ℚ)
    (hc : ∀ i, 0 ≤ c i) (he : coloringEntropy c ≤ (r : ℝ) / 64) :
    coloringEntropy (fun i => c i + 4) ≤ ((r / 2 : ℕ) : ℝ) / 64 := by
  have hexp : Real.exp (-1) ≤ (2 : ℝ) / 5 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 3
    norm_num [Finset.sum_range_succ] at h
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
    linarith
  have hrow (i : Fin m) : Real.exp (-(((c i + 4 : ℚ) : ℝ) ^ 2) / 16) ≤
      (2 / 5 : ℝ) * Real.exp (-((c i : ℝ) ^ 2) / 16) := by
    have hi : (0 : ℝ) ≤ c i := by exact_mod_cast hc i
    calc
      _ ≤ Real.exp (-1 + (-((c i : ℝ) ^ 2) / 16)) := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith
      _ = Real.exp (-1) * Real.exp (-((c i : ℝ) ^ 2) / 16) := Real.exp_add _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
  have hfloor : (2 / 5 : ℝ) * r ≤ ((r / 2 : ℕ) : ℝ) := by
    have hnat : 2 * r ≤ 5 * (r / 2) := by omega
    have hcast : (2 : ℝ) * r ≤ 5 * ((r / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  calc
    _ ≤ (2 / 5 : ℝ) * coloringEntropy c := by
      simpa [coloringEntropy, Finset.mul_sum] using Finset.sum_le_sum (fun i _ => hrow i)
    _ ≤ (2 / 5 : ℝ) * ((r : ℝ) / 64) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ ≤ _ := by nlinarith

end Power2ModuleSVP
