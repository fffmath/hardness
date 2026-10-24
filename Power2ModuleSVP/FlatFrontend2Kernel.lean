import Power2ModuleSVP.FlatFrontend2Derivative

/-! The first coloring and coefficient recomputation use the same rational
row. A uniform entry enclosure suffices for both coefficient obligations. -/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators
noncomputable section

/-- The actual real integral entry corresponding to a rational kernel row. -/
def realKernelEntry {N J : ℕ} (I : SeedKernelIntervals N J) (i : Fin J) (j : ℕ) : ℝ :=
  36000 * Real.sqrt N *
    ∫ u in I.leftAngle i..I.rightAngle i, Real.sin ((2 * (j : ℝ) + 1) * u)

theorem fractional_eq_sum {d : ℕ}
    (I : SeedKernelIntervals (seedN d) (intervalCount d))
    (α : Fin (intervalCount d) → ℚ) (j : Fin (seedN d)) :
    fractional I α j = ∑ i, (α i : ℝ) * realKernelEntry I i j := by
  unfold fractional SeedKernelIntervals.sineCoefficient realKernelEntry
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fractionalCoefficient_eq_sum {d : ℕ}
    (α : Fin (intervalCount d) → ℚ) (j : ℕ) :
    fractionalCoefficient (seedN d) (intervals (seedN d)) (List.ofFn α) j =
      ∑ i : Fin (intervalCount d), α i *
        kernelEntry (seedN d) ((intervals (seedN d)).getD i (0, 0)) j := by
  unfold fractionalCoefficient
  rw [list_sum_range, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val < intervalCount d := i.isLt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dite_eq_left hi]
  rfl

/-- Entrywise enclosures accumulate only linearly in the number of intervals.
No discrepancy or geometric estimate is needed for this transfer. -/
theorem fractional_error_of_entries {d : ℕ}
    (I : SeedKernelIntervals (seedN d) (intervalCount d))
    (α : Fin (intervalCount d) → ℚ) (hα : ∀ i, α i = -1 ∨ α i = 1)
    {ε : ℝ} (hentry : ∀ i : Fin (intervalCount d), ∀ j : Fin (seedN d),
      |(kernelEntry (seedN d) ((intervals (seedN d)).getD i (0, 0)) j : ℝ) -
        realKernelEntry I i j| ≤ ε) (j : Fin (seedN d)) :
    |(fractionalCoefficient (seedN d) (intervals (seedN d)) (List.ofFn α) j : ℝ) -
      fractional I α j| ≤ intervalCount d * ε := by
  rw [fractionalCoefficient_eq_sum, fractional_eq_sum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin (intervalCount d), ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul]
      have hs : |(α i : ℝ)| = 1 := by rcases hα i with h | h <;> simp [h]
      rw [hs, one_mul]
      exact hentry i j
    _ = _ := by simp

/-- The width-six geometry bounds each real entry independently of frequency. -/
theorem realKernelEntry_bound {N J : ℕ} (I : SeedKernelIntervals N J)
    (hN : 0 < N) (i : Fin J) (j : ℕ) :
    |realKernelEntry I i j| ≤ 216000 * Real.sqrt N * Real.pi / N := by
  unfold realKernelEntry
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 36000 * Real.sqrt (N : ℝ))]
  have hh := mul_le_mul_of_nonneg_left (I.sine_integral_abs_le hN i (2 * (j : ℝ) + 1))
    (by positivity : 0 ≤ 36000 * Real.sqrt (N : ℝ))
  convert hh using 1
  ring

/-- Exact identification of the first starting vector. -/
theorem first_start_zero (d : ℕ) (i : Fin (intervalCount d)) :
    inputStart (intervalInput d) i = 0 := by
  have hi := i.isLt
  unfold intervalCount at hi
  simp only [inputStart, intervalInput]
  split_ifs with h
  · omega
  · simp [List.getD_eq_getElem?_getD, hi]

def firstRowIndex {d : ℕ} (hJ : 0 < intervalCount d) (j : Fin (seedN d)) :
    Fin (seedIntervalRows (seedN d) (intervalCount d)) :=
  ⟨j, by simp [seedIntervalRows, Nat.ne_of_gt hJ]⟩

/-- Exact identification of a nonempty first row. -/
theorem first_matrix {d : ℕ} (hJ : 0 < intervalCount d)
    (j : Fin (seedN d)) (i : Fin (intervalCount d)) :
    inputMatrix (intervalInput d)
      (firstRowIndex hJ j) i =
      kernelEntry (seedN d) ((intervals (seedN d)).getD i (0, 0)) j := by
  have hi := i.isLt
  unfold intervalCount at hJ hi
  simp [inputMatrix, intervalInput, Nat.ne_of_gt hJ,
    List.getD_eq_getElem?_getD, j.isLt, hi, firstRowIndex]

theorem first_threshold {d : ℕ} (hJ : 0 < intervalCount d)
    (j : Fin (seedN d)) :
    inputThreshold (intervalInput d)
      (firstRowIndex hJ j) =
      firstThreshold (seedN d) (intervalCount d) := by
  unfold intervalCount at hJ ⊢
  simp [inputThreshold, intervalInput, Nat.ne_of_gt hJ,
    List.getD_eq_getElem?_getD, j.isLt, firstRowIndex]

/-- First-round discrepancy directly bounds the recomputed rational
coefficient; all real analysis is confined to entry enclosures. -/
theorem fractionalCoefficient_discrepancy {d : ℕ}
    (I : SeedKernelIntervals (seedN d) (intervalCount d))
    (α : Fin (intervalCount d) → ℚ) (hα : (analyticData d I).FirstSpec α)
    (hJ : 0 < intervalCount d) (j : Fin (seedN d)) :
    |(fractionalCoefficient (seedN d) (intervals (seedN d)) (List.ofFn α) j : ℝ)| ≤
      (240 * (firstThreshold (seedN d) (intervalCount d) : ℝ) + 2400) *
        Real.sqrt (intervalCount d) *
          coloringRowSup (fun i : Fin (intervalCount d) =>
            kernelEntry (seedN d) ((intervals (seedN d)).getD i (0, 0)) j) := by
  dsimp only [FlatSeedAnalyticData.FirstSpec, analyticData] at hα
  have hh := hα.2 (firstRowIndex hJ j)
  change coloringDiscrepancy (inputMatrix (intervalInput d) _) (inputStart (intervalInput d)) α ≤ _ at hh
  have hm : inputMatrix (intervalInput d) (firstRowIndex hJ j) =
      fun i : Fin (intervalCount d) =>
        kernelEntry (seedN d) ((intervals (seedN d)).getD i (0, 0)) j :=
    funext (first_matrix hJ j)
  rw [hm, first_threshold hJ] at hh
  unfold coloringDiscrepancy at hh
  simp_rw [first_start_zero, Rat.cast_zero, sub_zero] at hh
  rw [fractionalCoefficient_eq_sum]
  push_cast
  simpa [mul_comm] using hh

/-- A scalar first-threshold margin, separated from all coefficients and
coloring outputs. -/
def FirstThresholdMargin (N J : ℕ) (ε : ℝ) : Prop :=
  (240 * (firstThreshold N J : ℝ) + 2400) * Real.sqrt J *
    (216000 * Real.sqrt N * Real.pi / N + ε) + J * ε ≤ 3 / 4

/-- The first fractional-coefficient bound follows from uniform entry error
and a single scalar threshold margin. -/
theorem fractional_bound_of_entries {d : ℕ}
    (I : SeedKernelIntervals (seedN d) (intervalCount d)) (hN : 0 < seedN d)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hentry : ∀ i : Fin (intervalCount d), ∀ j : Fin (seedN d),
      |(kernelEntry (seedN d) ((intervals (seedN d)).getD i (0, 0)) j : ℝ) -
        realKernelEntry I i j| ≤ ε)
    (hmargin : FirstThresholdMargin (seedN d) (intervalCount d) ε)
    (α : Fin (intervalCount d) → ℚ) (hα : (analyticData d I).FirstSpec α)
    (j : Fin (seedN d)) : |fractional I α j| ≤ 3 / 4 := by
  by_cases hJ : 0 < intervalCount d
  · have hsup : coloringRowSup (fun i : Fin (intervalCount d) =>
        kernelEntry (seedN d) ((intervals (seedN d)).getD i (0, 0)) j) ≤
        216000 * Real.sqrt (seedN d) * Real.pi / seedN d + ε := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      intro i
      change |(kernelEntry (seedN d) ((intervals (seedN d)).getD i (0, 0)) j : ℝ)| ≤ _
      have ht := abs_sub_le
        (kernelEntry (seedN d) ((intervals (seedN d)).getD i (0, 0)) j : ℝ)
        (realKernelEntry I i j) 0
      simp only [sub_zero] at ht
      have hb := realKernelEntry_bound I hN i j
      linarith [hentry i j]
    have hc : 0 ≤ (240 * (firstThreshold (seedN d) (intervalCount d) : ℝ) + 2400) *
        Real.sqrt (intervalCount d) := by
      have hh : (0 : ℝ) ≤ firstThreshold (seedN d) (intervalCount d) := by
        exact_mod_cast firstThreshold_nonnegative (seedN d) (intervalCount d)
      positivity
    have hq := (fractionalCoefficient_discrepancy I α hα hJ j).trans
      (mul_le_mul_of_nonneg_left hsup hc)
    have herr := fractional_error_of_entries I α hα.1 hentry j
    have ht := abs_sub_le (fractional I α j)
      (fractionalCoefficient (seedN d) (intervals (seedN d)) (List.ofFn α) j : ℝ) 0
    rw [sub_zero, sub_zero, abs_sub_comm] at ht
    exact (ht.trans (add_le_add herr hq)).trans (by simpa [FirstThresholdMargin, add_comm] using hmargin)
  · let : IsEmpty (Fin (intervalCount d)) := ⟨fun i => by have := i.isLt; omega⟩
    norm_num [fractional_eq_sum]

end
end FlatFrontend
end Power2ModuleSVP
