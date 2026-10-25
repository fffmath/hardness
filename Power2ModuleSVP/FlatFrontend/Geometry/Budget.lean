import Power2ModuleSVP.FlatFrontend.Geometry.Parameters

/-!
# Budget

Explicit scalar budgets for transferring the rational marker.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
noncomputable section
set_option exponentiation.threshold 1024

theorem height_lower_constant {N : ℕ} (hN : 0 < N) :
    (1 : ℚ) / 2 ^ 213 ≤ height N := by
  have hn : (0 : ℚ) < N := by exact_mod_cast hN
  have hp := block_parameters N
  have hw := stageWidth_block N
  have hW : stageWidth (stage N) ≤ 4 * blockShift N := by omega
  have hW' : (stageWidth (stage N) : ℚ) ≤ 4 * blockShift N := by exact_mod_cast hW
  have hgamma := gamma_lower hN
  have hu : (1 : ℚ) / 2 ^ 70 ≤ 2 * (blockShift N : ℚ) / N := by
    have hh := div_le_div_of_nonneg_right hW' hn.le
    have he : 4 * (blockShift N : ℚ) / N = 2 * (2 * (blockShift N : ℚ) / N) := by ring
    rw [he] at hh
    unfold gamma at hgamma
    norm_num at hgamma ⊢
    linarith
  have hamp : (1 : ℚ) ≤ (2 : ℚ) ^ ((stage N + 1) / 2) := one_le_pow₀ (by norm_num)
  calc
    (1 : ℚ) / 2 ^ 213 ≤ 30 * 1 / 128 * ((1 : ℚ) / 2 ^ 70) ^ 3 := by norm_num
    _ ≤ height N := by
      unfold height
      gcongr

theorem sampleError_bound (N : ℕ) :
    sampleError N ≤ 4 / (2 ^ 80 * ((N : ℚ) + 1) ^ 9) := by
  unfold sampleError fineError
  have hx : (0 : ℚ) < (N : ℚ) + 1 := by positivity
  field_simp
  nlinarith only [pow_pos hx 9]

theorem sampleError_scaled (N : ℕ) :
    8 * (N : ℚ) ^ 3 * sampleError N ≤
      32 / (2 ^ 80 * ((N : ℚ) + 1) ^ 6) := by
  have hx : (0 : ℚ) < (N : ℚ) + 1 := by positivity
  have hp : (N : ℚ) ^ 3 ≤ ((N : ℚ) + 1) ^ 3 := by gcongr; linarith
  have hδ : 0 ≤ sampleError N := by unfold sampleError fineError; positivity
  calc
    _ ≤ 8 * ((N : ℚ) + 1) ^ 3 * (4 / (2 ^ 80 * ((N : ℚ) + 1) ^ 9)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num))
        (sampleError_bound N) hδ (by positivity)
    _ = _ := by field_simp; ring

theorem sampleError_height_budget {N : ℕ} (hN : 2 ^ 24 ≤ N) :
    8 * (N : ℝ) ^ 3 * (sampleError N : ℝ) ≤ (height N : ℝ) / 16 := by
  have hNp : 0 < N := by omega
  have hx : (2 ^ 24 : ℚ) ≤ (N : ℚ) + 1 := by exact_mod_cast (show 2 ^ 24 ≤ N + 1 by omega)
  have hp : (2 ^ 144 : ℚ) ≤ ((N : ℚ) + 1) ^ 6 := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 2 ^ 24) hx 6
    norm_num at hh ⊢
    exact hh
  have hb : (32 : ℚ) / (2 ^ 80 * ((N : ℚ) + 1) ^ 6) ≤ 1 / 2 ^ 217 := by
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num
    nlinarith only [hp]
  have hh := (sampleError_scaled N).trans hb
  have hheight := height_lower_constant hNp
  have hfinal : 8 * (N : ℚ) ^ 3 * sampleError N ≤ height N / 16 := by
    norm_num at hh hheight ⊢
    linarith
  exact_mod_cast hfinal

theorem markedRun_width_clearances {d : ℕ} (hd : Dyadic d) (hlarge : 2 ^ 512 ≤ d) :
    (∀ i, runRight d i ≤ runLeft d i + 6) ∧
    (∀ i, 100 ≤ runLeft d i) ∧
    (∀ i, 2 * (runRight d i + 100) ≤ seedN d) := by
  have hc := cutoff_seedN hlarge
  have hsmall : 2 ^ 24 ≤ seedN d := (by norm_num : 2 ^ 24 ≤ 2 ^ 509).trans hc.1
  have hshape := dyadic_shape hd ((by norm_num : 4 ≤ 2 ^ 512).trans hlarge)
  have hN : 0 < seedN d := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 24) hsmall
  have hfit : 2 * blockShift (seedN d) + 2 ^ stage (seedN d) ≤ seedN d + 1 := by
    have := block_fits hc.2
    have := (block_parameters (seedN d)).1
    omega
  have hw := markedWaveWitness_of_budget hshape hc.2 (sampleError_height_budget hsmall)
  have hseven := seven_unmarked_of_wave (waveCellWidth_pos hN) (waveCellWidth_small hc.2) hw
  have haxis := axis_unmarked_of_wave hshape hfit hN (waveCellWidth_small hc.2) hw
  have hm (i : Fin (intervalCount d)) := getD_mem (intervals (seedN d)) (0, 0) i.isLt
  exact ⟨fun i => intervals_width hseven (hm i),
    fun i => (intervals_clearance haxis (hm i)).1,
    fun i => (intervals_clearance haxis (hm i)).2⟩

end
end FlatFrontend
end Power2ModuleSVP
