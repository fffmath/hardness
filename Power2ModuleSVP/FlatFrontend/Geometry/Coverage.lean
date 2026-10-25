import Power2ModuleSVP.FlatFrontend.Geometry.Margin

/-!
# Coverage

Fine-grid coverage and the complementary cosine estimate.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
noncomputable section

/-- A fine sample inside the same closed coarse cell is at most one fine
spacing away, including either coarse-cell endpoint. -/
theorem fineSample_in_cell {N R j : ℕ} (hN : 0 < N) (hR : 0 < R) {θ : ℝ}
    (hθ : θ ∈ Set.Icc ((j : ℝ) * Real.pi / N) (((j : ℝ) + 1) * Real.pi / N)) :
    ∃ r, j * R ≤ r ∧ r ≤ (j + 1) * R ∧
      |θ - seedFineAngle (N * R) r| ≤ Real.pi / (N * R : ℕ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : (0 : ℝ) < R := by exact_mod_cast hR
  have hm : (0 : ℝ) < (N * R : ℕ) := by exact_mod_cast Nat.mul_pos hN hR
  let z := θ * (N * R : ℕ) / Real.pi
  have hθ0 : 0 ≤ θ := (by positivity : (0 : ℝ) ≤ j * Real.pi / N).trans hθ.1
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hfl : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz
  have hfu : z < (⌊z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z
  have hlo : ((j * R : ℕ) : ℝ) ≤ z := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    have hh := (div_le_iff₀ hn).mp hθ.1
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_right hh hr.le]
  have hhi : z ≤ (((j + 1) * R : ℕ) : ℝ) := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    have hh := (le_div_iff₀ hn).mp hθ.2
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_right hh hr.le]
  refine ⟨⌊z⌋₊, (Nat.le_floor_iff hz).mpr hlo, ?_, ?_⟩
  · exact_mod_cast hfl.trans hhi
  · have hl : (⌊z⌋₊ : ℝ) * Real.pi ≤ θ * (N * R : ℕ) :=
      (le_div_iff₀ Real.pi_pos).mp hfl
    have hu : θ * (N * R : ℕ) < ((⌊z⌋₊ : ℝ) + 1) * Real.pi :=
      (div_lt_iff₀ Real.pi_pos).mp hfu
    unfold seedFineAngle
    rw [abs_of_nonneg (by exact sub_nonneg.mpr ((div_le_iff₀ hm).mpr hl))]
    apply (le_div_iff₀ hm).mpr
    field_simp
    nlinarith only [hu]

theorem gridRatio_spacing {N : ℕ} (hN : 0 < N) :
    128 * (N : ℝ) ≤ gridRatio N * (height N : ℝ) := by
  have hh := height_positive hN
  have hc := Nat.le_ceil (64 * (N : ℚ) / height N)
  have hr : 128 * (N : ℚ) ≤ (gridRatio N : ℚ) * height N := by
    unfold gridRatio
    push_cast
    have h := (div_le_iff₀ hh).mp hc
    linarith
  exact_mod_cast hr

theorem cell_spacing_bound {N j : ℕ} (hN : 0 < N) {θ : ℝ}
    (hθ : θ ∈ Set.Icc ((j : ℝ) * Real.pi / N) (((j : ℝ) + 1) * Real.pi / N)) :
    ∃ r, j * gridRatio N ≤ r ∧ r ≤ (j + 1) * gridRatio N ∧
      2 * (N : ℝ) ^ 2 * |θ - seedFineAngle (gridSize N) r| ≤
        Real.pi * (height N : ℝ) / 64 := by
  obtain ⟨r, hl, hr, he⟩ := fineSample_in_cell hN (gridRatio_positive hN) hθ
  refine ⟨r, hl, hr, ?_⟩
  apply (mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ) ^ 2)).trans
  have hnp : (0 : ℝ) < N := by exact_mod_cast hN
  have hrp : (0 : ℝ) < gridRatio N := by exact_mod_cast gridRatio_positive hN
  have hh := gridRatio_spacing hN
  push_cast
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
  field_simp
  nlinarith only [hh]

theorem runContains_of_marked {d j : ℕ} (hN : 0 < seedN d) (hj : j < seedN d / 2)
    (hm : markedCell (seedN d) j = true) {θ : ℝ}
    (hθ : θ ∈ Set.Icc ((j : ℝ) * Real.pi / seedN d) (((j : ℝ) + 1) * Real.pi / seedN d)) :
    runContains d θ := by
  obtain ⟨I, hI, hl, hr⟩ := intervals_cover hj hm
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hI
  have hd : (intervals (seedN d)).getD i (0, 0) = I := by
    simpa [List.getD_eq_getElem?_getD, hi] using he
  refine ⟨⟨i, hi⟩, ?_, ?_⟩
  · change (((intervals (seedN d)).getD i (0, 0)).1 : ℝ) * Real.pi / seedN d ≤ θ
    rw [hd]
    apply le_trans _ hθ.1
    gcongr
  · change θ ≤ (((intervals (seedN d)).getD i (0, 0)).2 : ℝ) * Real.pi / seedN d
    rw [hd]
    apply hθ.2.trans
    gcongr
    exact_mod_cast (show j + 1 ≤ I.2 by omega)

theorem cosine_fold {d : ℕ} (hd : d = 4 * seedN d + 4) (θ : ℝ) :
    |cosine d θ| = |cosine d (foldAngle θ)| := by
  apply foldAngle_preserves
  · intro x
    dsimp only
    rw [cosine_eq_reducedPolynomial hd, cosine_eq_reducedPolynomial hd]
    have he : 2 * (x + Real.pi) = 2 * x + 2 * Real.pi := by ring
    rw [he, Real.cos_add_two_pi]
  · intro x
    rw [cosine_eq_reducedPolynomial hd, cosine_eq_reducedPolynomial hd]
    have he : 2 * (Real.pi - x) = -(2 * x) + 2 * Real.pi := by ring
    rw [he, Real.cos_add_two_pi, Real.cos_neg]

end
end FlatFrontend
end Power2ModuleSVP
