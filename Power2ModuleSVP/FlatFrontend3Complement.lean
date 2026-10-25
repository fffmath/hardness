import Power2ModuleSVP.FlatFrontend3Coverage

/-! Coverage of the complement, including the terminal unscanned half-cell. -/
namespace Power2ModuleSVP
namespace FlatFrontend
noncomputable section
set_option exponentiation.threshold 1024

theorem cosine_right_tail {d : ℕ} (hd : d = 4 * seedN d + 4)
    (hN : stageWidth 1 * 2 ^ 66 ≤ seedN d) {θ : ℝ}
    (hθ : θ ∈ Set.Icc ((seedN d / 2 : ℕ) * Real.pi / seedN d) (Real.pi / 2)) :
    5 * (height (seedN d) : ℝ) / 8 ≤ |cosine d θ| := by
  have hNp : 0 < seedN d := by
    have := stageWidth_positive 1
    have : 0 < stageWidth 1 * 2 ^ 66 := by positivity
    omega
  have hn : (0 : ℝ) < seedN d := by exact_mod_cast hNp
  have ht : (0 : ℝ) < blockShift (seedN d) := by exact_mod_cast (block_parameters (seedN d)).1
  have ha := waveCellWidth_pos hNp
  have haMax := waveCellWidth_small hN
  have hfit : 2 * blockShift (seedN d) + 2 ^ stage (seedN d) ≤ seedN d + 1 := by
    have := block_fits hN
    have := (block_parameters (seedN d)).1
    omega
  have hdist : |2 * blockShift (seedN d) * θ - blockShift (seedN d) * Real.pi| ≤
      101 * waveCellWidth (seedN d) := by
    have hx : 2 * (blockShift (seedN d) : ℝ) * θ ≤ blockShift (seedN d) * Real.pi := by
      nlinarith only [mul_le_mul_of_nonneg_left hθ.2 ht.le]
    rw [abs_of_nonpos (sub_nonpos.mpr hx)]
    have hlow := (div_le_iff₀ hn).mp hθ.1
    have hfloor : (seedN d : ℝ) ≤ 2 * ((seedN d / 2 : ℕ) + 1 : ℝ) := by
      exact_mod_cast (show seedN d ≤ 2 * (seedN d / 2 + 1) by omega)
    have hphase : (Real.pi / 2 - θ) * seedN d ≤ Real.pi := by
      nlinarith only [hlow, mul_le_mul_of_nonneg_right hfloor Real.pi_pos.le]
    have hangle : Real.pi / 2 - θ ≤ Real.pi / seedN d :=
      (le_div_iff₀ hn).mpr hphase
    have he := mul_le_mul_of_nonneg_left hangle (show (0 : ℝ) ≤ 2 * blockShift (seedN d) by positivity)
    change _ ≤ 101 * (2 * blockShift (seedN d) * Real.pi / seedN d)
    have ha' : (0 : ℝ) ≤ 2 * blockShift (seedN d) * Real.pi / seedN d := by positivity
    have he' : (blockShift (seedN d) : ℝ) * Real.pi - 2 * blockShift (seedN d) * θ ≤
        2 * blockShift (seedN d) * Real.pi / seedN d := by
      convert he using 1 <;> ring
    linarith only [he', ha']
  have hd1 (x : ℝ) : |rudinShapiroWave (stage (seedN d)) 1 x| ≤ 4 := by
    simpa only [pow_one, show (2 : ℝ) + 2 = 4 from by norm_num] using
      rudinShapiroWave_bound (stage (seedN d)) (by norm_num : 1 ≤ 4) x
  have hw := seed_axis_clearance (rudinShapiroWave_hasDerivAt (stage (seedN d)) 0)
    hd1 (wave_right_axis hd hfit) haMax hdist
  rw [cosine_eq_wave hd hfit, stage_sqrt, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (stageIndex (seedN d) + 1))]
  have hAmp : (0 : ℝ) < 2 ^ (stageIndex (seedN d) + 1) := by positivity
  have hsmall := height_wave_budget hNp
  have hpow : waveCellWidth (seedN d) ^ 3 ≤ 1 := pow_le_one₀ ha.le (by linarith)
  have hb := mul_le_mul_of_nonneg_left hpow hAmp.le
  have hw' := mul_le_mul_of_nonneg_left hw.le hAmp.le
  nlinarith only [hsmall, hb, hw', hAmp]

theorem cosine_good {d : ℕ} (hd : Dyadic d) (hlarge : 2 ^ 512 ≤ d)
    (θ : ℝ) (hout : ¬ runContains d (foldAngle θ)) :
    seedCosineMargin * Real.sqrt (seedN d) ≤ |cosine d θ| := by
  have hc := cutoff_seedN hlarge
  have hN : 0 < seedN d := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 24)
    ((by norm_num : 2 ^ 24 ≤ 2 ^ 509).trans hc.1)
  have hshape := dyadic_shape hd ((by norm_num : 4 ≤ 2 ^ 512).trans hlarge)
  have hn : (0 : ℝ) < seedN d := by exact_mod_cast hN
  have hfold := foldAngle_mem θ
  rw [cosine_fold hshape θ]
  apply (height_margin hN).trans
  by_cases hcore : foldAngle θ < (seedN d / 2 : ℕ) * Real.pi / seedN d
  · let z := foldAngle θ * seedN d / Real.pi
    have hz : 0 ≤ z := div_nonneg (mul_nonneg hfold.1 hn.le) Real.pi_pos.le
    have hfl := Nat.floor_le hz
    have hfu := Nat.lt_floor_add_one z
    have hj : ⌊z⌋₊ < seedN d / 2 := by
      apply (Nat.floor_lt hz).mpr
      apply (div_lt_iff₀ Real.pi_pos).mpr
      exact (lt_div_iff₀ hn).mp hcore
    have hcell : foldAngle θ ∈ Set.Icc ((⌊z⌋₊ : ℝ) * Real.pi / seedN d)
        (((⌊z⌋₊ : ℝ) + 1) * Real.pi / seedN d) := by
      constructor
      · apply (div_le_iff₀ hn).mpr
        exact (le_div_iff₀ Real.pi_pos).mp hfl
      · apply (le_div_iff₀ hn).mpr
        exact ((div_lt_iff₀ Real.pi_pos).mp hfu).le
    have hm : markedCell (seedN d) ⌊z⌋₊ = false := by
      cases he : markedCell (seedN d) ⌊z⌋₊ with
      | false => rfl
      | true => exact False.elim (hout (runContains_of_marked hN hj he hcell))
    obtain ⟨r, hl, hr, hspacing⟩ := cell_spacing_bound hN hcell
    exact (unmarkedCell_cosine_bound hshape hN
      (sampleError_height_budget ((by norm_num : 2 ^ 24 ≤ 2 ^ 509).trans hc.1))
      hj hl hr hm hspacing).le
  · exact cosine_right_tail hshape hc.2 ⟨le_of_not_gt hcore, hfold.2⟩

end
end FlatFrontend
end Power2ModuleSVP
