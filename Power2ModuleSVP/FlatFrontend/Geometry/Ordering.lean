import Power2ModuleSVP.FlatFrontend.Geometry.Budget

/-!
# Ordering

Quantitative ordering of the implemented cosine grid.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
noncomputable section
set_option exponentiation.threshold 1024

/-- A uniform exact-node gap on the first quadrant. -/
theorem cosine_grid_gap {M : ℕ} (hM : 0 < M) {x y : ℝ}
    (hx : 0 ≤ x) (hy : y ≤ Real.pi / 2) (hgap : Real.pi / M ≤ y - x) :
    2 / (M : ℝ) ^ 2 ≤ Real.cos x - Real.cos y := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hxy : x ≤ y := by
    have : (0 : ℝ) < Real.pi / M := by positivity
    linarith
  have hu0 : 0 ≤ (x + y) / 2 := by linarith
  have hu1 : (x + y) / 2 ≤ Real.pi / 2 := by linarith
  have hv0 : 0 ≤ (y - x) / 2 := by linarith
  have hv1 : (y - x) / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hlow : (1 : ℝ) / M ≤ 2 / Real.pi * ((y - x) / 2) := by
    have hh := (div_le_iff₀ hm).mp hgap
    apply (div_le_iff₀ hm).mpr
    field_simp
    nlinarith only [hh]
  have hlow' : (1 : ℝ) / M ≤ 2 / Real.pi * ((x + y) / 2) := by
    have hh : 2 / Real.pi * ((y - x) / 2) ≤ 2 / Real.pi * ((x + y) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    exact hlow.trans hh
  have hs₁ := hlow'.trans (Real.mul_le_sin hu0 hu1)
  have hs₂ := hlow.trans (Real.mul_le_sin hv0 hv1)
  have he : Real.cos x - Real.cos y = 2 * Real.sin ((x + y) / 2) * Real.sin ((y - x) / 2) := by
    rw [Real.cos_sub_cos, show (x - y) / 2 = -((y - x) / 2) by ring, Real.sin_neg]
    ring
  rw [he]
  have hh := mul_le_mul hs₁ hs₂ (by positivity : (0 : ℝ) ≤ 1 / M)
    ((by positivity : (0 : ℝ) ≤ 1 / M).trans hs₁)
  have he' : 2 / (M : ℝ) ^ 2 = 2 * ((1 : ℝ) / M * (1 / M)) := by ring
  rw [he']
  nlinarith only [hh]

theorem gridSize_upper {N : ℕ} (hN : 0 < N) :
    (gridSize N : ℚ) ≤ 2 ^ 221 * ((N : ℚ) + 1) ^ 2 := by
  have hh := height_lower_constant hN
  have hn : (0 : ℚ) ≤ N := by positivity
  have hceil := (Nat.ceil_lt_add_one (by positivity : (0 : ℚ) ≤ 64 * N / height N)).le
  have hdiv : 64 * (N : ℚ) / height N ≤ 2 ^ 219 * N := by
    apply (div_le_iff₀ (height_positive hN)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hh (show (0 : ℚ) ≤ 2 ^ 219 * N by positivity)]
  have hr : (gridRatio N : ℚ) ≤ 2 ^ 220 * ((N : ℚ) + 1) := by
    unfold gridRatio
    push_cast
    norm_num at hceil hdiv ⊢
    linarith
  unfold gridSize
  push_cast
  have he := mul_le_mul_of_nonneg_left hr hn
  norm_num at he ⊢
  nlinarith only [he, hn, sq_nonneg (N : ℚ)]

/-- The fixed precision is far smaller than the exact-node gap. -/
theorem sampleError_grid_budget {N : ℕ} (hN : 2 ^ 100 ≤ N) :
    (sampleError N : ℝ) ≤ 1 / (4 * (gridSize N : ℝ) ^ 2) := by
  have hNp : 0 < N := lt_of_lt_of_le (by positivity : 0 < 2 ^ 100) hN
  have hm : (0 : ℚ) < gridSize N := by exact_mod_cast gridSize_positive hNp
  have hx : (0 : ℚ) < (N : ℚ) + 1 := by positivity
  have hpow : (2 ^ 500 : ℚ) ≤ ((N : ℚ) + 1) ^ 5 := by
    have hn : (2 ^ 100 : ℚ) ≤ (N : ℚ) + 1 := by exact_mod_cast (show 2 ^ 100 ≤ N + 1 by omega)
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 2 ^ 100) hn 5
    norm_num at hh ⊢
    exact hh
  have hsize := gridSize_upper hNp
  have hsize2 := pow_le_pow_left₀ hm.le hsize 2
  have hh : (sampleError N : ℚ) ≤ 1 / (4 * (gridSize N : ℚ) ^ 2) := by
    apply (sampleError_bound N).trans
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hbound : (16 : ℚ) * (gridSize N : ℚ) ^ 2 ≤
        16 * (2 ^ 221 * ((N : ℚ) + 1) ^ 2) ^ 2 := by gcongr
    have hnum : (16 : ℚ) * (2 ^ 221) ^ 2 ≤ 2 ^ 80 * ((N : ℚ) + 1) ^ 5 := by
      norm_num at hpow ⊢
      linarith
    have hp := mul_le_mul_of_nonneg_right hnum (pow_nonneg hx.le 4)
    nlinarith only [hbound, hp]
  have hc := (Rat.cast_le (K := ℝ)).mpr hh
  simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_one] using hc

theorem gridSample_nonnegative {N r : ℕ} (hN : 0 < N)
    (hr : 2 * r ≤ gridSize N) : (0 : ℝ) ≤ gridSample N r := by
  have hm := gridSize_positive hN
  unfold gridSample
  dsimp only
  split_ifs with hzero hlast hmid hleft
  · norm_num
  · omega
  · norm_num
  · exact_mod_cast (clamp_lower (a := 0) (b := 1))
  · omega

theorem gridSample_strictAnti_firstHalf {N : ℕ} (hN : 2 ^ 100 ≤ N) :
    StrictAntiOn (fun r => (gridSample N r : ℝ)) (Set.Icc 0 (gridSize N / 2)) := by
  have hNp : 0 < N := lt_of_lt_of_le (by positivity : 0 < 2 ^ 100) hN
  have hM := gridSize_positive hNp
  have hm : (0 : ℝ) < gridSize N := by exact_mod_cast hM
  intro r hr s hs hrs
  rcases hr with ⟨hr0, hr1⟩
  rcases hs with ⟨hs0, hs1⟩
  have hrM : r ≤ gridSize N := by omega
  have hsM : s ≤ gridSize N := by omega
  have hs2 : 2 * (s : ℝ) ≤ gridSize N := by exact_mod_cast (show 2 * s ≤ gridSize N by omega)
  have hsr : (r : ℝ) + 1 ≤ s := by exact_mod_cast hrs
  have hx : (0 : ℝ) ≤ seedFineAngle (gridSize N) r := by unfold seedFineAngle; positivity
  have hy : seedFineAngle (gridSize N) s ≤ Real.pi / 2 := by
    unfold seedFineAngle
    apply (div_le_iff₀ hm).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hs2 Real.pi_pos.le]
  have hg : Real.pi / gridSize N ≤
      seedFineAngle (gridSize N) s - seedFineAngle (gridSize N) r := by
    unfold seedFineAngle
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ hm.le
    nlinarith only [mul_le_mul_of_nonneg_right hsr Real.pi_pos.le]
  have hgap := cosine_grid_gap hM hx hy hg
  have hb := sampleError_grid_budget hN
  have hsmall : 2 * (sampleError N : ℝ) < 2 / (gridSize N : ℝ) ^ 2 := by
    have hi : (0 : ℝ) < 1 / (gridSize N : ℝ) ^ 2 := by positivity
    have he : (1 : ℝ) / (4 * (gridSize N : ℝ) ^ 2) = (1 / (gridSize N : ℝ) ^ 2) / 4 := by ring
    rw [he] at hb
    rw [show (2 : ℝ) / (gridSize N : ℝ) ^ 2 = 2 * (1 / (gridSize N : ℝ) ^ 2) by ring]
    linarith
  exact rational_samples_strictly_ordered
    (gridSample_error hNp hrM hM) (gridSample_error hNp hsM hM) (hsmall.trans_le hgap)

theorem reducedGridNode_antitone {N : ℕ} (hN : 2 ^ 100 ≤ N) :
    AntitoneOn (reducedGridNode N) (Set.Icc 0 ((N / 2) * gridRatio N)) := by
  have hNp : 0 < N := lt_of_lt_of_le (by positivity : 0 < 2 ^ 100) hN
  have hbound : (N / 2) * gridRatio N ≤ gridSize N / 2 := by
    unfold gridSize
    have hh := Nat.mul_le_mul_right (gridRatio N) (show 2 * (N / 2) ≤ N by omega)
    have he : 2 * ((N / 2) * gridRatio N) ≤ N * gridRatio N := by
      simpa only [mul_assoc] using hh
    omega
  intro r hr s hs hrs
  change 0 ≤ r ∧ r ≤ (N / 2) * gridRatio N at hr
  change 0 ≤ s ∧ s ≤ (N / 2) * gridRatio N at hs
  rcases eq_or_lt_of_le hrs with he | he
  · subst s
    rfl
  · have hanti := gridSample_strictAnti_firstHalf hN
      ⟨hr.1, hr.2.trans hbound⟩ ⟨hs.1, hs.2.trans hbound⟩ he
    have hsq := gridSample_nonnegative hNp (r := s) (by omega)
    have hrq := gridSample_nonnegative hNp (r := r) (by omega)
    unfold reducedGridNode
    nlinarith only [hanti, hsq, hrq, mul_nonneg (sub_nonneg.mpr hanti.le) (add_nonneg hrq hsq)]

end
end FlatFrontend
end Power2ModuleSVP
