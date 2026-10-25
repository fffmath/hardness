module

public import Power2ModuleSVP.Coloring.Partial.Invariants

/-!
# Bounds

Analytic extraction of discrepancy from terminal rational weights, and the
unconditional discrepancy estimate used to discard large-threshold rows.
These lemmas do not assume that the concrete walk has those terminal bounds.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

open scoped BigOperators

theorem discrepancy_eq_abs_dot {r : ℕ} (v x y : Vec r) :
    coloringDiscrepancy v x y = |(dot v (y - x) : ℝ)| := by
  simp [coloringDiscrepancy, dot]

theorem coloringRowNorm_sq {r : ℕ} (v : Vec r) :
    coloringRowNorm v ^ 2 = (dot v v : ℝ) := by
  rw [coloringRowNorm, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp [dot, pow_two]

theorem normScale_lt_two_rowNorm {r : ℕ} (v : Vec r) (hv : v ≠ 0) :
    (normScale (dot v v) : ℝ) < 2 * coloringRowNorm v := by
  have hd : 0 < dot v v := lt_of_le_of_ne (dot_self_nonneg v)
    (Ne.symm ((dot_self_eq_zero v).not.mpr hv))
  obtain ⟨hq, _, hq'⟩ := normScale_bounds hd
  have hq₁ : (0 : ℝ) < normScale (dot v v) := by exact_mod_cast hq
  have hq₂ : (normScale (dot v v) : ℝ) ^ 2 < 4 * (dot v v : ℝ) := by exact_mod_cast hq'
  have hn : 0 ≤ coloringRowNorm v := Real.sqrt_nonneg _
  have hn' := coloringRowNorm_sq v
  nlinarith

theorem discrepancy_normalize {r : ℕ} (v x y : Vec r) (hv : v ≠ 0) :
    coloringDiscrepancy v x y =
      (normScale (dot v v) : ℝ) * coloringDiscrepancy (normalize v) x y := by
  have hd : 0 < dot v v := lt_of_le_of_ne (dot_self_nonneg v)
    (Ne.symm ((dot_self_eq_zero v).not.mpr hv))
  have hq := (normScale_bounds hd).1
  have hq' : (0 : ℝ) < normScale (dot v v) := by exact_mod_cast hq
  rw [discrepancy_eq_abs_dot, discrepancy_eq_abs_dot, normalize, dot_smul_left]
  push_cast
  rw [abs_mul, abs_inv, abs_of_pos hq']
  field_simp

/-- Cube-to-cube discrepancy is at most twice the row norm times sqrt(r). -/
theorem cube_discrepancy_le {r : ℕ} (v x y : Vec r)
    (hx : RationalCube x) (hy : RationalCube y) :
    coloringDiscrepancy v x y ≤ 2 * Real.sqrt r * coloringRowNorm v := by
  have hdiff : (∑ j, ((y j : ℝ) - (x j : ℝ)) ^ 2) ≤ 4 * (r : ℝ) := by
    calc
      _ ≤ ∑ _j : Fin r, (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        obtain ⟨hx₁, hx₂⟩ := abs_le.mp (hx j)
        obtain ⟨hy₁, hy₂⟩ := abs_le.mp (hy j)
        nlinarith
      _ = _ := by simp; ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => (v j : ℝ)) (fun j => (y j : ℝ) - (x j : ℝ))
  have hsum : (∑ j, (v j : ℝ) ^ 2) = coloringRowNorm v ^ 2 := by
    rw [coloringRowNorm, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  rw [hsum] at hcs
  have hcs' := hcs.trans (mul_le_mul_of_nonneg_left hdiff (sq_nonneg _))
  have hs := Real.sq_sqrt (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have hs₀ := Real.sqrt_nonneg (r : ℝ)
  have hn₀ := Real.sqrt_nonneg (∑ j, (v j : ℝ) ^ 2)
  have hnon : 0 ≤ 2 * Real.sqrt r * coloringRowNorm v := by unfold coloringRowNorm; positivity
  unfold coloringDiscrepancy
  apply (sq_le_sq₀ (abs_nonneg _) hnon).mp
  rw [sq_abs]
  nlinarith

theorem large_threshold_discrepancy {r : ℕ} (v x y : Vec r) (lam : ℚ)
    (hx : RationalCube x) (hy : RationalCube y) (hl : 0 ≤ lam)
    (hlarge : 4 * (r : ℚ) < lam ^ 2) :
    coloringDiscrepancy v x y ≤ 68 * (lam : ℝ) * coloringRowNorm v := by
  have hlarge' : 4 * (r : ℝ) < (lam : ℝ) ^ 2 := by exact_mod_cast hlarge
  have hl' : (0 : ℝ) ≤ lam := by exact_mod_cast hl
  have hs := Real.sq_sqrt (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have hs₀ := Real.sqrt_nonneg (r : ℝ)
  have hcoeff : 2 * Real.sqrt r ≤ 68 * (lam : ℝ) := by nlinarith
  exact (cube_discrepancy_le v x y hx hy).trans
    (mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg _))

/-- Terminal weights below two give the one-sided normalized bound 34.
The strict estimate exp(3/4)>2 leaves room for the step-size correction. -/
theorem linear_bound_of_terminal_weight {r : ℕ} (hr : 0 < r)
    {lam d w : ℝ} (hl : 1 < lam)
    (hlower : Real.exp (lam * d - (33 + 8 * (stepSize r : ℝ) ^ 2) * lam ^ 2) ≤ w)
    (hupper : w < 2) : d ≤ 34 * lam := by
  have he : 2 < Real.exp ((3 : ℝ) / 4) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) 3
    norm_num [Finset.sum_range_succ] at h
    linarith
  have ha : lam * d - (33 + 8 * (stepSize r : ℝ) ^ 2) * lam ^ 2 < 3 / 4 := by
    apply Real.exp_lt_exp.mp
    exact (hlower.trans_lt hupper).trans he
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hΔ : (0 : ℝ) ≤ stepSize r := by exact_mod_cast (stepSize_pos hr).le
  have hΔ' : (stepSize r : ℝ) ≤ 1 / 16 := by
    simp only [stepSize, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * r)).mpr
    linarith
  have hpay : 0 ≤ (1 / 4 - 8 * (stepSize r : ℝ) ^ 2) * lam ^ 2 := by
    apply mul_nonneg _ (sq_nonneg _)
    nlinarith
  have htotal : lam * d < 34 * lam ^ 2 := by nlinarith
  nlinarith

end Power2ModuleSVP.PartialColoringAlg
