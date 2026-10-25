import Power2ModuleSVP.FlatFrontend.Geometry.Polynomial
import Power2ModuleSVP.FlatFrontend.Geometry.Scan

/-!
# Wave

Transfer of local wave witnesses to the computed run geometry.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators
noncomputable section

/-- The width in the wave variable corresponding to one angular grid cell. -/
def waveCellWidth (N : ℕ) : ℝ := 2 * blockShift N * Real.pi / N

theorem cosine_axes {d : ℕ} (hd : d = 4 * seedN d + 4)
    (hfit : 2 * blockShift (seedN d) + 2 ^ stage (seedN d) ≤ seedN d + 1) :
    cosine d 0 = (2 : ℝ) ^ (stageIndex (seedN d) + 1) ∧
    cosine d (Real.pi / 2) = (2 : ℝ) ^ (stageIndex (seedN d) + 1) := by
  have he := rudinShapiro_odd_endpoints (stageIndex (seedN d))
  have hzero : seedCircle 0 = 1 := by simp [seedCircle]
  have hright : seedCircle (Real.pi / 2) = -1 := by
    simp only [seedCircle, mul_div_cancel₀ Real.pi (by norm_num : (2 : ℝ) ≠ 0),
      Complex.exp_ofReal_mul_I]
    simp
  constructor
  · rw [cosine_eq_rudinShapiro hd hfit, rudinShapiroCosinePart, hzero]
    change (1 ^ blockShift (seedN d) * rsEval (rudinShapiroP (2 * stageIndex (seedN d) + 1)) 1 +
      1 ^ (2 * blockShift (seedN d)) *
        rsEval (rudinShapiroQ (2 * stageIndex (seedN d) + 1)) 1).re = _
    simp only [he.1, he.2.1, one_pow, one_mul, add_zero]
    norm_cast
  · rw [cosine_eq_rudinShapiro hd hfit, rudinShapiroCosinePart, hright]
    change ((-1) ^ blockShift (seedN d) *
        rsEval (rudinShapiroP (2 * stageIndex (seedN d) + 1)) (-1) +
      (-1) ^ (2 * blockShift (seedN d)) *
        rsEval (rudinShapiroQ (2 * stageIndex (seedN d) + 1)) (-1)).re = _
    have hp : (-1 : ℂ) ^ (2 * blockShift (seedN d)) = 1 := by
      rw [pow_mul]
      norm_num
    simp only [he.2.2.1, he.2.2.2, mul_zero, zero_add, hp, one_mul]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem stage_sqrt (N : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (stage N + 1)) = (2 : ℝ) ^ (stageIndex N + 1) := by
  rw [show stage N + 1 = (stageIndex N + 1) * 2 by unfold stage; omega,
    pow_mul, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]

theorem wave_right_axis {d : ℕ} (hd : d = 4 * seedN d + 4)
    (hfit : 2 * blockShift (seedN d) + 2 ^ stage (seedN d) ≤ seedN d + 1) :
    rudinShapiroWave (stage (seedN d)) 0 (blockShift (seedN d) * Real.pi) = 1 := by
  have he := (cosine_axes hd hfit).2
  rw [cosine_eq_wave hd hfit, stage_sqrt] at he
  have ha : 2 * (blockShift (seedN d) : ℝ) * (Real.pi / 2) =
      blockShift (seedN d) * Real.pi := by ring
  rw [ha] at he
  exact (mul_left_cancel₀ (by positivity : (2 : ℝ) ^ (stageIndex (seedN d) + 1) ≠ 0)
    (by simpa only [mul_one] using he))

/-- A local premise about each *marked cell*, with no mention of runs,
counts, clearances, or the final preparation statement. -/
def MarkedWaveWitness (N : ℕ) : Prop :=
  ∀ j, j < N / 2 → markedCell N j = true →
    ∃ x ∈ Set.Icc ((j : ℝ) * waveCellWidth N) (((j : ℝ) + 1) * waveCellWidth N),
      |rudinShapiroWave (stage N) 0 x| ≤ (waveCellWidth N) ^ 3 / 128

theorem seven_unmarked_of_wave {N : ℕ} (ha : 0 < waveCellWidth N)
    (haMax : waveCellWidth N ≤ 1 / 2048) (hw : MarkedWaveWitness N) :
    ∀ j, j + 7 ≤ N / 2 → ∃ k < 7, markedCell N (j + k) = false := by
  intro j hj
  by_contra h
  have hm : ∀ k : Fin 7, markedCell N (j + k.val) = true := by
    intro k
    have hn : ¬ markedCell N (j + k.val) = false := by
      intro he
      exact h ⟨k.val, k.isLt, he⟩
    cases he : markedCell N (j + k.val) <;> simp_all
  have hs (k : Fin 7) := hw (j + k.val) (by omega) (hm k)
  choose point hp hsmall using hs
  apply seed_seven_cell_exclusion (b := (j : ℝ) * waveCellWidth N) (rudinShapiroWave (stage N))
    (rudinShapiroWave_hasDerivAt _) (rudinShapiroWave_nondegenerate _)
    (fun _ hr x => rudinShapiroWave_bound _ hr x) ha haMax point _ hsmall
  intro k
  convert hp k using 1; push_cast; ring_nf

theorem axis_unmarked_of_wave {d : ℕ} (hd : d = 4 * seedN d + 4)
    (hfit : 2 * blockShift (seedN d) + 2 ^ stage (seedN d) ≤ seedN d + 1)
    (hN : 0 < seedN d) (haMax : waveCellWidth (seedN d) ≤ 1 / 2048)
    (hw : MarkedWaveWitness (seedN d)) :
    ∀ j, j < seedN d / 2 → markedCell (seedN d) j = true →
      100 ≤ j ∧ 2 * (j + 101) ≤ seedN d := by
  intro j hj hm
  obtain ⟨x, hx, hs⟩ := hw j hj hm
  have ha : 0 < waveCellWidth (seedN d) := by
    unfold waveCellWidth
    have := (block_parameters (seedN d)).1
    positivity
  have hs' : |rudinShapiroWave (stage (seedN d)) 0 x| < 1 / 2 := by
    have hp : waveCellWidth (seedN d) ^ 3 ≤ 1 :=
      pow_le_one₀ ha.le (by linarith)
    linarith
  have hnr : (0 : ℝ) < seedN d := by exact_mod_cast hN
  have haxis : (blockShift (seedN d) : ℝ) * Real.pi =
      (seedN d : ℝ) / 2 * waveCellWidth (seedN d) := by
    unfold waveCellWidth
    field_simp
  have hd1 (y : ℝ) : |rudinShapiroWave (stage (seedN d)) 1 y| ≤ 4 := by
    simpa only [pow_one, show (2 : ℝ) + 2 = 4 from by norm_num] using
      rudinShapiroWave_bound (stage (seedN d)) (by norm_num : 1 ≤ 4) y
  constructor
  · by_contra h
    have hj' : (j : ℝ) + 1 ≤ 100 := by exact_mod_cast (show j + 1 ≤ 100 by omega)
    have hn : |x| ≤ 101 * waveCellWidth (seedN d) := by
      rw [abs_of_nonneg (by nlinarith [hx.1, Nat.cast_nonneg (α := ℝ) j])]
      nlinarith [hx.2]
    have he := rudinShapiroWave_zero_axis_clearance (stageIndex (seedN d)) haMax hn
    exact (not_lt_of_ge he.le) hs'
  · by_contra h
    have hj' : (seedN d : ℝ) / 2 - (j : ℝ) ≤ 101 := by
      have hn : (seedN d : ℝ) < 2 * ((j : ℝ) + 101) := by
        exact_mod_cast (show seedN d < 2 * (j + 101) by omega)
      linarith
    have hcell : (j : ℝ) + 1 ≤ (seedN d : ℝ) / 2 := by
      have hn : 2 * (j + 1) ≤ seedN d := by omega
      have hn' : 2 * ((j : ℝ) + 1) ≤ seedN d := by exact_mod_cast hn
      linarith
    have hn : |x - blockShift (seedN d) * Real.pi| ≤ 101 * waveCellWidth (seedN d) := by
      rw [haxis, abs_of_nonpos (by
        nlinarith only [hx.2, mul_le_mul_of_nonneg_right hcell ha.le])]
      nlinarith only [hx.1, mul_le_mul_of_nonneg_right hj' ha.le]
    have he := seed_axis_clearance (rudinShapiroWave_hasDerivAt (stage (seedN d)) 0)
      hd1 (wave_right_axis hd hfit) haMax hn
    exact (not_lt_of_ge he.le) hs'

end
end FlatFrontend
end Power2ModuleSVP
