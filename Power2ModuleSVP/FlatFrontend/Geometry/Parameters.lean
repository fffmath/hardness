import Power2ModuleSVP.FlatFrontend.Geometry.Wave
import Power2ModuleSVP.FlatFrontend.Geometry.Sampling

/-!
# Parameters

Normalizations and uniform cell-width estimates for the actual parameters.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
noncomputable section

set_option exponentiation.threshold 1024 in
theorem cutoff_seedN {d : ℕ} (hlarge : 2 ^ 512 ≤ d) :
    2 ^ 509 ≤ seedN d ∧ stageWidth 1 * 2 ^ 66 ≤ seedN d := by
  unfold seedN stageWidth
  norm_num at hlarge ⊢
  omega

theorem waveCellWidth_pos {N : ℕ} (hN : 0 < N) : 0 < waveCellWidth N := by
  have := (block_parameters N).1
  unfold waveCellWidth
  positivity

theorem waveCellWidth_small {N : ℕ} (hN : stageWidth 1 * 2 ^ 66 ≤ N) :
    waveCellWidth N ≤ 1 / 2048 := by
  have hadm := stage_admissible hN
  have hb := (block_parameters N).1
  have hw := stageWidth_block N
  have hm : 0 < 2 ^ stage N := by positivity
  have hw' : 2 * blockShift N ≤ stageWidth (stage N) := by omega
  have hbd : 2 * blockShift N * 2 ^ 66 ≤ N :=
    (Nat.mul_le_mul_right _ hw').trans hadm
  have hNr : (0 : ℝ) < N := by
    have : 0 < N := by nlinarith
    exact_mod_cast this
  have hbr : (0 : ℝ) < blockShift N := by exact_mod_cast hb
  have hbd' : 2 * (blockShift N : ℝ) * 2 ^ 66 ≤ N := by exact_mod_cast hbd
  unfold waveCellWidth
  apply (div_le_iff₀ hNr).mpr
  have hpi := mul_lt_mul_of_pos_left Real.pi_lt_four (by positivity : (0 : ℝ) < 2 * blockShift N)
  norm_num at hbd'
  nlinarith only [hbd', hpi, hbr]

theorem height_real (N : ℕ) :
    (height N : ℝ) = 30 * (2 : ℝ) ^ (stageIndex N + 1) / 128 *
      (2 * (blockShift N : ℝ) / N) ^ 3 := by
  unfold height
  have he : (stage N + 1) / 2 = stageIndex N + 1 := by unfold stage; omega
  rw [he]
  push_cast
  rfl

/-- The `13/16` marked-sample allowance fits strictly within the
seven-cell wave threshold. -/
theorem height_wave_budget {N : ℕ} (hN : 0 < N) :
    13 * (height N : ℝ) / 16 ≤
      (2 : ℝ) ^ (stageIndex N + 1) * waveCellWidth N ^ 3 / 128 := by
  rw [height_real]
  have he : waveCellWidth N = (2 * (blockShift N : ℝ) / N) * Real.pi := by
    unfold waveCellWidth
    ring
  rw [he, mul_pow]
  have hpi : (27 : ℝ) ≤ Real.pi ^ 3 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) Real.pi_gt_three.le 3
    norm_num at hp
    exact hp
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (stageIndex N + 1) * (2 * (blockShift N : ℝ) / N) ^ 3 := by
    positivity
  nlinarith only [mul_le_mul_of_nonneg_left hpi hc, hc]

theorem height_small {N : ℕ} (hN : stageWidth 1 * 2 ^ 66 ≤ N) :
    3 * (height N : ℝ) / 4 < (2 : ℝ) ^ (stageIndex N + 1) := by
  have hb := (block_parameters N).1
  have ha := waveCellWidth_small hN
  have hNp : 0 < N := by
    have := stage_admissible hN
    have := stageWidth_positive (stage N)
    nlinarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hratio : 0 ≤ 2 * (blockShift N : ℝ) / N := by positivity
  have hratio' : 2 * (blockShift N : ℝ) / N ≤ 1 := by
    have hd := block_fits hN
    have hm : 0 < 2 ^ stage N := by positivity
    have hdn : 2 * blockShift N ≤ N := by omega
    apply (div_le_iff₀ hNr).mpr
    simpa only [one_mul] using (show 2 * (blockShift N : ℝ) ≤ N by exact_mod_cast hdn)
  have hpow := pow_le_one₀ hratio hratio' (n := 3)
  rw [height_real]
  have hAmp : (0 : ℝ) < (2 : ℝ) ^ (stageIndex N + 1) := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left hpow hAmp.le, hAmp]

/-- A certified sample budget now gives the wave witnesses, without any
additional analytic identification premise. -/
theorem markedWaveWitness_of_budget {d : ℕ} (hd : d = 4 * seedN d + 4)
    (hN : stageWidth 1 * 2 ^ 66 ≤ seedN d)
    (hbudget : 8 * (seedN d : ℝ) ^ 3 * (sampleError (seedN d) : ℝ) ≤
      (height (seedN d) : ℝ) / 16) : MarkedWaveWitness (seedN d) := by
  have hNp : 0 < seedN d := by
    have := stageWidth_positive 1
    have : 0 < stageWidth 1 * 2 ^ 66 := by positivity
    omega
  have hNr : (0 : ℝ) < seedN d := by exact_mod_cast hNp
  have hfit : 2 * blockShift (seedN d) + 2 ^ stage (seedN d) ≤ seedN d + 1 := by
    have := block_fits hN
    have := (block_parameters (seedN d)).1
    omega
  intro j hj hm
  obtain ⟨r, hl, hr, hs⟩ := markedCell_cosine_witness hd hNp hbudget hj hm
  let θ := seedFineAngle (gridSize (seedN d)) r
  refine ⟨2 * blockShift (seedN d) * θ, ?_, ?_⟩
  · have hR : (0 : ℝ) < gridRatio (seedN d) := by exact_mod_cast gridRatio_positive hNp
    have hl' : (j : ℝ) * gridRatio (seedN d) ≤ r := by exact_mod_cast hl
    have hr' : (r : ℝ) ≤ ((j : ℝ) + 1) * gridRatio (seedN d) := by exact_mod_cast hr
    have hlo : (j : ℝ) * Real.pi / seedN d ≤ θ := by
      dsimp [θ, seedFineAngle, gridSize]
      push_cast
      apply (le_div_iff₀ (mul_pos hNr hR)).mpr
      field_simp
      exact hl'
    have hhi : θ ≤ ((j : ℝ) + 1) * Real.pi / seedN d := by
      dsimp [θ, seedFineAngle, gridSize]
      push_cast
      apply (div_le_iff₀ (mul_pos hNr hR)).mpr
      field_simp
      exact hr'
    have hscale : (0 : ℝ) ≤ 2 * blockShift (seedN d) := by positivity
    constructor
    · convert mul_le_mul_of_nonneg_left hlo hscale using 1; dsimp [waveCellWidth]; ring
    · convert mul_le_mul_of_nonneg_left hhi hscale using 1; dsimp [waveCellWidth]; ring
  · rw [cosine_eq_wave hd hfit, stage_sqrt, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (stageIndex (seedN d) + 1))] at hs
    have he := hs.trans (height_wave_budget hNp)
    have hAmp : (0 : ℝ) < (2 : ℝ) ^ (stageIndex (seedN d) + 1) := by positivity
    have he' : (2 : ℝ) ^ (stageIndex (seedN d) + 1) *
        |rudinShapiroWave (stage (seedN d)) 0 (2 * blockShift (seedN d) * θ)| ≤
        (2 : ℝ) ^ (stageIndex (seedN d) + 1) * (waveCellWidth (seedN d) ^ 3 / 128) := by
      simpa only [mul_div_assoc] using he
    nlinarith only [he', hAmp]

end
end FlatFrontend
end Power2ModuleSVP
