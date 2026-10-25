module

public import Power2ModuleSVP.Coloring.Partial.Bounds
public import Power2ModuleSVP.Coloring.Full

/-!
# Correctness interfaces for the rational walk

Extract discrepancy bounds from terminal progress and weight estimates. The trajectory contract
is discharged in Coloring/Trajectory/Basic.lean; the native certificate is proved in
Runtime/Coloring/Certificate.lean.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

open scoped BigOperators

noncomputable def rowEntropy {r : ℕ} (rows : List (Row r)) : ℝ :=
  (rows.map fun row => Real.exp (-((row.threshold : ℝ) ^ 2) / 16)).sum

theorem rowEntropy_eq {r : ℕ} (rows : List (Row r)) :
    rowEntropy rows = coloringEntropy (fun i : Fin rows.length => rows[i].threshold) := by
  unfold rowEntropy coloringEntropy
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map rows
    (fun row => Real.exp (-((row.threshold : ℝ) ^ 2) / 16))).symm

theorem prepareRows_entropy {r m : ℕ} (V : Fin m → Vec r) (c : Fin m → ℚ) :
    rowEntropy (prepareRows V c) ≤ 2 * coloringEntropy c := by
  unfold rowEntropy prepareRows
  simp only [List.flatMap_def, List.map_flatten, List.sum_flatten,
    List.map_ofFn, List.sum_ofFn,
    Function.comp_def]
  calc
    _ ≤ ∑ i : Fin m, 2 * Real.exp (-((c i : ℝ) ^ 2) / 16) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hd : dot (V i) (V i) = 0 ∨ 4 * (r : ℚ) < c i ^ 2
      · simp only [ite_eq_left hd, List.map_nil, List.sum_nil]
        positivity
      · simp only [ite_eq_right hd, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero]
        linarith
    _ = _ := by simp [coloringEntropy, Finset.mul_sum, two_mul]

theorem prepareRows_mem {r m : ℕ} (V : Fin m → Vec r) (c : Fin m → ℚ)
    (i : Fin m) (hv : V i ≠ 0) (hl : c i ^ 2 ≤ 4 * (r : ℚ)) :
    Row.mk (normalize (V i)) (c i) ∈ prepareRows V c ∧
      Row.mk (-normalize (V i)) (c i) ∈ prepareRows V c := by
  have hzero : dot (V i) (V i) ≠ 0 := (dot_self_eq_zero _).not.mpr hv
  constructor <;> apply List.mem_flatMap.mpr <;>
    refine ⟨i, by simp, ?_⟩ <;> simp [hzero, not_lt.mpr hl]

theorem prepareRows_row_properties {r m : ℕ} (V : Fin m → Vec r) (c : Fin m → ℚ)
    (hc : ∀ i, 0 ≤ c i) (row : Row r) (hrow : row ∈ prepareRows V c) :
    0 ≤ row.threshold ∧ row.threshold ^ 2 ≤ 4 * (r : ℚ) ∧ dot row.a row.a ≤ 1 := by
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hrow
  by_cases hdel : dot (V i) (V i) = 0 ∨ 4 * (r : ℚ) < c i ^ 2
  · simp only [ite_eq_left hdel, List.not_mem_nil] at hi
  · have hnorm := (normalize_bounds (V i) ((dot_self_eq_zero _).not.mp (not_or.mp hdel).1)).2
    have hthr : c i ^ 2 ≤ 4 * (r : ℚ) := le_of_not_gt (not_or.mp hdel).2
    simp only [hdel, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hc i, hthr, hnorm⟩
    · exact ⟨hc i, hthr, by simpa [dot] using hnorm⟩

structure WalkPremises {r m : ℕ} (a : Fin m → Row r) (x : Vec r) : Prop where
  dimension : 64 ≤ r
  cube : RationalCube x
  threshold_nonneg : ∀ i, 0 ≤ (a i).threshold
  threshold_sq_le : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ)
  row_norm_le : ∀ i, dot (a i).a (a i).a ≤ 1
  entropy : coloringEntropy (fun i => (a i).threshold) ≤ (r : ℝ) / 32

theorem prepareRows_premises {r m : ℕ} (hr : 64 ≤ r) (V : Fin m → Vec r) (x : Vec r)
    (c : Fin m → ℚ) (hx : RationalCube x) (hc : ∀ i, 0 ≤ c i)
    (he : coloringEntropy c ≤ (r : ℝ) / 64) :
    WalkPremises (fun i : Fin (prepareRows V c).length => (prepareRows V c)[i]) x := by
  refine ⟨hr, hx, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (prepareRows_row_properties V c hc _ (List.getElem_mem _)).1
  · intro i
    exact (prepareRows_row_properties V c hc _ (List.getElem_mem _)).2.1
  · intro i
    exact (prepareRows_row_properties V c hc _ (List.getElem_mem _)).2.2
  · rw [← rowEntropy_eq]
    exact (prepareRows_entropy V c).trans (by linarith)

/-- The progress and terminal-weight contract for `run`. The initial exponential
enclosures, low-Rayleigh directions, heavy-row argument, and cubic progress
count are proved in Coloring/Trajectory and assembled in its Basic module. -/
structure PartialColoringTrajectoryHypothesis : Prop where
  terminal_half : ∀ (r m : ℕ) (a : Fin m → Row r) (x : Vec r),
    WalkPremises a x → r ≤ 2 * signCoordinateCount (run a x).x
  terminal_weight_upper : ∀ (r m : ℕ) (a : Fin m → Row r) (x : Vec r),
    WalkPremises a x → ∀ i, ((run a x).w i : ℝ) < 2
  terminal_weight_lower : ∀ (r m : ℕ) (a : Fin m → Row r) (x : Vec r),
    WalkPremises a x → ∀ i,
    Real.exp ((a i).threshold * (dot (a i).a ((run a x).x - x) : ℝ) -
      (33 + 8 * (stepSize r : ℝ) ^ 2) * ((a i).threshold : ℝ) ^ 2) ≤ ((run a x).w i : ℝ)

theorem run_cube {r m : ℕ} (hr : 0 < r) (a : Fin m → Row r) (x : Vec r)
    (hx : RationalCube x) : RationalCube (run a x).x :=
  walk_cube hr a _ _ hx

theorem run_small_row {r m : ℕ} (a : Fin m → Row r) (x : Vec r) (i : Fin m)
    (hi : (a i).threshold ≤ 1) : dot (a i).a ((run a x).x - x) = 0 := by
  unfold run
  rw [dot_sub_right, walk_small_row a _ _ i hi]
  simp [initialState]

theorem retained_normalized_discrepancy (h : PartialColoringTrajectoryHypothesis)
    {r m : ℕ} (hr : 64 ≤ r) (V : Fin m → Vec r) (x : Vec r) (c : Fin m → ℚ)
    (hx : RationalCube x) (hc : ∀ i, 0 ≤ c i)
    (he : coloringEntropy c ≤ (r : ℝ) / 64)
    (i : Fin m) (hv : V i ≠ 0) (hl : c i ^ 2 ≤ 4 * (r : ℚ)) :
    coloringDiscrepancy (normalize (V i)) x
      (run (fun j : Fin (prepareRows V c).length => (prepareRows V c)[j]) x).x ≤
        34 * (c i : ℝ) := by
  let rows := prepareRows V c
  let a : Fin rows.length → Row r := fun j => rows[j]
  have hp : WalkPremises a x := prepareRows_premises hr V x c hx hc he
  obtain ⟨hplus, hminus⟩ := prepareRows_mem V c i hv hl
  obtain ⟨ip, hip⟩ := List.mem_iff_get.mp hplus
  obtain ⟨im, him⟩ := List.mem_iff_get.mp hminus
  have hip' : a ip = Row.mk (normalize (V i)) (c i) := hip
  have him' : a im = Row.mk (-normalize (V i)) (c i) := him
  change coloringDiscrepancy (normalize (V i)) x (run a x).x ≤ _
  rw [discrepancy_eq_abs_dot]
  by_cases hsmall : c i ≤ 1
  · have hs := run_small_row a x ip (by simpa only [hip'] using hsmall)
    simp only [hip'] at hs
    rw [hs]
    simp only [Rat.cast_zero, abs_zero]
    have hc' : (0 : ℝ) ≤ c i := by exact_mod_cast hc i
    positivity
  · have hc' : (1 : ℝ) < c i := by exact_mod_cast (lt_of_not_ge hsmall)
    have hpLow := h.terminal_weight_lower r rows.length a x hp ip
    have hmLow := h.terminal_weight_lower r rows.length a x hp im
    simp only [hip'] at hpLow
    simp only [him'] at hmLow
    have hneg : (dot (-normalize (V i)) ((run a x).x - x) : ℝ) =
        -(dot (normalize (V i)) ((run a x).x - x) : ℝ) := by simp [dot]
    rw [hneg] at hmLow
    have hpBound := linear_bound_of_terminal_weight (by omega : 0 < r) hc'
      hpLow (h.terminal_weight_upper r rows.length a x hp ip)
    have hmBound := linear_bound_of_terminal_weight (by omega : 0 < r) hc'
      hmLow (h.terminal_weight_upper r rows.length a x hp im)
    exact abs_le.mpr ⟨by linarith, hpBound⟩

theorem retained_discrepancy (h : PartialColoringTrajectoryHypothesis)
    {r m : ℕ} (hr : 64 ≤ r) (V : Fin m → Vec r) (x : Vec r) (c : Fin m → ℚ)
    (hx : RationalCube x) (hc : ∀ i, 0 ≤ c i)
    (he : coloringEntropy c ≤ (r : ℝ) / 64)
    (i : Fin m) (hv : V i ≠ 0) (hl : c i ^ 2 ≤ 4 * (r : ℚ)) :
    coloringDiscrepancy (V i) x
      (run (fun j : Fin (prepareRows V c).length => (prepareRows V c)[j]) x).x ≤
        68 * (c i : ℝ) * coloringRowNorm (V i) := by
  rw [discrepancy_normalize _ _ _ hv]
  have hscale : (0 : ℝ) ≤ normScale (dot (V i) (V i)) := by
    have hd : 0 < dot (V i) (V i) := lt_of_le_of_ne (dot_self_nonneg _)
      (Ne.symm ((dot_self_eq_zero _).not.mpr hv))
    exact_mod_cast (normScale_bounds hd).1.le
  have hc' : (0 : ℝ) ≤ c i := by exact_mod_cast hc i
  calc
    _ ≤ (normScale (dot (V i) (V i)) : ℝ) * (34 * (c i : ℝ)) :=
      mul_le_mul_of_nonneg_left (retained_normalized_discrepancy h hr V x c hx hc he i hv hl) hscale
    _ ≤ (2 * coloringRowNorm (V i)) * (34 * (c i : ℝ)) :=
      mul_le_mul_of_nonneg_right (normScale_lt_two_rowNorm _ hv).le (by positivity)
    _ = _ := by ring

/-- Semantic correctness of the concrete list algorithm, with its remaining
trajectory estimates exposed as a named argument. The machine-time gap is
not used in this theorem. -/
theorem partialColor_correct_of_trajectory (h : PartialColoringTrajectoryHypothesis) :
    PartialColoringCorrect partialColor := by
  intro r m V x c hr hx hc he
  let rows := prepareRows V c
  let a : Fin rows.length → Row r := fun j => rows[j]
  by_cases hempty : rows.isEmpty = true
  · refine ⟨fun j => nearestRationalSign (x j), ?_, ?_⟩
    · rw [partialColor_on_input V x c hx hc, ite_eq_left hempty]
    · have hy : RationalCube (fun j => nearestRationalSign (x j)) := by
        intro j
        change |(nearestRationalSign (x j) : ℝ)| ≤ 1
        rcases nearestRationalSign_isSign (x j) with hj | hj <;> rw [hj] <;> norm_num
      refine ⟨hy, ?_, ?_⟩
      · rw [nearestRationalSign_count]
        omega
      · intro i
        by_cases hv : V i = 0
        · simp [hv, coloringDiscrepancy, coloringRowNorm]
        · have hlarge : 4 * (r : ℚ) < c i ^ 2 := by
            by_contra hn
            have hmem := (prepareRows_mem V c i hv (le_of_not_gt hn)).1
            have hnrows : rows = [] := List.isEmpty_iff.mp hempty
            change Row.mk (normalize (V i)) (c i) ∈ rows at hmem
            simp only [hnrows, List.not_mem_nil] at hmem
          exact large_threshold_discrepancy (V i) x _ (c i) hx hy (hc i) hlarge
  · refine ⟨(run a x).x, ?_, ?_⟩
    · rw [partialColor_on_input V x c hx hc, ite_eq_right hempty]
      have ha : (prepareRows V c).get = a := by
        funext j
        simp [a, rows, List.get_eq_getElem]
      rw [ha]
    · have hp : WalkPremises a x := prepareRows_premises hr V x c hx hc he
      have hy := run_cube (by omega : 0 < r) a x hx
      refine ⟨hy, h.terminal_half r rows.length a x hp, ?_⟩
      intro i
      by_cases hv : V i = 0
      · simp [hv, coloringDiscrepancy, coloringRowNorm]
      · by_cases hlarge : 4 * (r : ℚ) < c i ^ 2
        · exact large_threshold_discrepancy (V i) x _ (c i) hx hy (hc i) hlarge
        · exact retained_discrepancy h hr V x c hx hc he i hv (le_of_not_gt hlarge)

/-- Independent native-machine obligation for the concrete program. It
includes all rational elimination, enclosure and intermediate-size bounds. -/
structure PartialColoringNativeHypothesis : Prop where
  polytime : Turing.MultiTapeTM.ComputableTidilyInPolyTime partialColor encPartialColoring
    (Turing.MultiTapeTM.encList encColoringRational)

theorem deterministicPartialColoring_of_trajectory_and_native
    (h : PartialColoringTrajectoryHypothesis) (hN : PartialColoringNativeHypothesis) :
    DeterministicPartialColoringHypothesis :=
  ⟨⟨partialColor, hN.polytime, partialColor_correct_of_trajectory h⟩⟩

theorem fullColor_partialColor_spec_of_trajectory (h : PartialColoringTrajectoryHypothesis)
    (r m : ℕ) (V : Fin m → Vec r) (x : Vec r) (c : Fin m → ℚ)
    (hx : RationalCube x) (hc : ∀ i, 0 ≤ c i)
    (he : coloringEntropy c ≤ (r : ℝ) / 64) :
    ∃ y : Vec r, fullColor partialColor (partialColoringInput V x c) = List.ofFn y ∧
      FullColoringSpec V x y c :=
  fullColor_spec partialColor (partialColor_correct_of_trajectory h) r m V x c hx hc he

end Power2ModuleSVP.PartialColoringAlg
