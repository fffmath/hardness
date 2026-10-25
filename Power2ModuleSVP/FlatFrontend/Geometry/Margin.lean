import Power2ModuleSVP.FlatFrontend.Geometry.Budget

/-!
# Margin

The numerical complementary cosine margin for the selected stage.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
noncomputable section

theorem blockShift_scale (N : ℕ) : blockShift N = 1024 * 2 ^ stage N := by
  unfold blockShift
  rw [pow_add]
  norm_num
  omega

theorem height_margin {N : ℕ} (hN : 0 < N) :
    seedCosineMargin * Real.sqrt N ≤ 5 * (height N : ℝ) / 8 := by
  have hnq : (0 : ℚ) < N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := stageWidth_block N
  have ht := blockShift_scale N
  have hW : 31 * stageWidth (stage N) ≤ 64 * blockShift N := by omega
  have hg := gamma_lower hN
  have huq : (31 : ℚ) / (32 * 2 ^ 69) ≤ 2 * (blockShift N : ℚ) / N := by
    have hwr : (31 : ℚ) * stageWidth (stage N) ≤ 64 * blockShift N := by exact_mod_cast hW
    have hc := (div_le_div_of_nonneg_right hwr hnq.le)
    have he : 31 * (stageWidth (stage N) : ℚ) / N = 31 * gamma N := by unfold gamma; ring
    have he' : 64 * (blockShift N : ℚ) / N = 32 * (2 * (blockShift N : ℚ) / N) := by ring
    rw [he, he'] at hc
    norm_num at hg ⊢
    linarith
  have hu : (31 : ℝ) / (32 * 2 ^ 69) ≤ 2 * (blockShift N : ℝ) / N := by
    have hh := (Rat.cast_le (K := ℝ)).mpr huq
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_ofNat] using hh
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 31 / (32 * 2 ^ 69)) hu 3
  have hWpow : stageWidth (stage N) ≤ 2 ^ (stage N + 12) := by
    have hh : 2 ^ (stage N + 12) = 4096 * 2 ^ stage N := by rw [pow_add]; norm_num; omega
    unfold stageWidth
    rw [show stage N + 11 = stage N + 11 from rfl, pow_add]
    norm_num
    rw [hh]
    omega
  have hNpow : N ≤ 2 ^ 80 * 2 ^ (stage N + 1) := by
    have hh : N < stageWidth (stage N) * 2 ^ 69 := by
      have hh := (lt_div_iff₀ hnq).mp hg
      have he : (1 : ℚ) / 2 ^ 69 * N < stageWidth (stage N) := by simpa [gamma] using hh
      have he' : (N : ℚ) < stageWidth (stage N) * 2 ^ 69 := by linarith
      exact_mod_cast he'
    have he : 2 ^ (stage N + 12) * 2 ^ 69 = 2 ^ 80 * 2 ^ (stage N + 1) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    exact hh.le.trans ((Nat.mul_le_mul_right _ hWpow).trans he.le)
  have hAmp2 : ((2 : ℝ) ^ (stageIndex N + 1)) ^ 2 = (2 : ℝ) ^ (stage N + 1) := by
    rw [← pow_mul]
    congr 1
    unfold stage
    omega
  have hAmp : (0 : ℝ) < (2 : ℝ) ^ (stageIndex N + 1) := by positivity
  have hsqrt : Real.sqrt N ≤ 2 ^ 40 * (2 : ℝ) ^ (stageIndex N + 1) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    have hh : (N : ℝ) ≤ 2 ^ 80 * (2 : ℝ) ^ (stage N + 1) := by exact_mod_cast hNpow
    rw [mul_pow, hAmp2]
    norm_num at hh ⊢
    exact hh
  rw [height_real]
  have hscaled := mul_le_mul_of_nonneg_left hp hAmp.le
  have hmargin := mul_le_mul_of_nonneg_left hsqrt seedCosineMargin_pos.le
  norm_num [seedCosineMargin] at hscaled hmargin ⊢
  nlinarith only [hscaled, hmargin, hAmp]

end
end FlatFrontend
end Power2ModuleSVP
