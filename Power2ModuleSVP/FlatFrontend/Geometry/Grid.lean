import Power2ModuleSVP.FlatFrontend.Geometry.Cosine
import Power2ModuleSVP.Seed.Intervals

/-!
# Grid

Enclosures for the actual reflected rational grid.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
noncomputable section

theorem gridSample_error {N : ℕ} (hN : 0 < N) {r : ℕ} (hr : r ≤ gridSize N)
    (hM : 0 < gridSize N) :
    |(gridSample N r : ℝ) - Real.cos (seedFineAngle (gridSize N) r)| ≤
      (((4 * (N : ℚ) + 2) * fineError N : ℚ) : ℝ) := by
  let M := gridSize N
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have he0 : (0 : ℝ) ≤ (((4 * (N : ℚ) + 2) * fineError N : ℚ) : ℝ) := by
    exact_mod_cast mul_nonneg (by positivity : (0 : ℚ) ≤ 4 * N + 2) (fineError_pos N).le
  have hhalf {s : ℕ} (hs : 2 * s ≤ M) :
      |(clamp 0 1 (cosTaylor (taylorOrder N)
        ((s : ℚ) * piTaylor (precision N) / M)) : ℝ) - Real.cos (s * Real.pi / M)| ≤
        (((4 * (N : ℚ) + 2) * fineError N : ℚ) : ℝ) := by
    have hsr : (0 : ℝ) ≤ (s : ℝ) * Real.pi / M := by positivity
    have hsr' : (s : ℝ) * Real.pi / M ≤ Real.pi / 2 := by
      apply (div_le_iff₀ hMr).mpr
      have hsc : 2 * (s : ℝ) ≤ M := by exact_mod_cast hs
      nlinarith [Real.pi_pos]
    have hx : (0 : ℝ) ≤ Real.cos (s * Real.pi / M) ∧ Real.cos (s * Real.pi / M) ≤ 1 :=
      ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hsr'⟩, Real.cos_le_one _⟩
    have hsq : (s : ℚ) / M ≤ N := by
      apply (div_le_iff₀ hMq).mpr
      have hsc : 2 * (s : ℚ) ≤ M := by exact_mod_cast hs
      have hnc : (1 : ℚ) ≤ N := by exact_mod_cast hN
      nlinarith
    have hh := phase_error_fine (N := N) (r := (s : ℚ) / M) (by positivity) hsq 1
    have he : ((s : ℚ) / M) * piTaylor (precision N) =
        (s : ℚ) * piTaylor (precision N) / M := by ring
    rw [he] at hh
    have he' : ((s : ℚ) / M : ℚ) * (Real.pi : ℝ) = (s : ℝ) * Real.pi / M := by
      push_cast
      ring
    have hh' : |(cosTaylor (taylorOrder N)
        ((s : ℚ) * piTaylor (precision N) / M) : ℝ) - Real.cos (s * Real.pi / M)| ≤
          (((4 * (N : ℚ) + 2) * fineError N : ℚ) : ℝ) := by
      simpa [jetSin, phase, Nat.zero_mod, Nat.one_mod, ↓reduceIte, zero_mul,
        one_mul, zero_add, phaseTaylor, Rat.cast_div, Rat.cast_natCast,
        div_mul_eq_mul_div, abs_sub_comm] using hh
    exact clamp_error (a := 0) (b := 1) (by simpa using hx) hh'
  unfold gridSample
  dsimp only
  split_ifs with hzero hlast hmid hleft
  · subst r
    simpa [seedFineAngle] using he0
  · have he : r = M := by dsimp [M]; omega
    subst r
    simpa [seedFineAngle, M, ne_of_gt hMr] using he0
  · have he : (r : ℝ) * Real.pi / M = Real.pi / 2 := by
      have hm : 2 * (r : ℝ) = M := by exact_mod_cast hmid
      field_simp
      nlinarith
    simp only [Rat.cast_zero, seedFineAngle]
    change |(0 : ℝ) - Real.cos ((r : ℝ) * Real.pi / M)| ≤ _
    simpa only [he, Real.cos_pi_div_two, sub_zero, abs_zero] using he0
  · simpa only [seedFineAngle] using hhalf (s := r) (by omega)
  · have href : Real.cos (seedFineAngle M r) = -Real.cos ((M - r : ℕ) * Real.pi / M) := by
      have he : (r : ℝ) * Real.pi / M = Real.pi - (M - r : ℕ) * Real.pi / M := by
        rw [Nat.cast_sub hr]
        field_simp
        ring
      rw [seedFineAngle, he, Real.cos_pi_sub]
    rw [href, Rat.cast_neg, neg_sub_neg, abs_sub_comm]
    exact hhalf (by omega)

theorem gridRatio_positive {N : ℕ} (hN : 0 < N) : 0 < gridRatio N := by
  have hh := height_positive hN
  unfold gridRatio
  have : 0 < ⌈64 * (N : ℚ) / height N⌉₊ := Nat.ceil_pos.mpr (by positivity)
  omega

theorem gridSize_positive {N : ℕ} (hN : 0 < N) : 0 < gridSize N :=
  Nat.mul_pos hN (gridRatio_positive hN)

theorem gridSample_mem (N r : ℕ) : (gridSample N r : ℝ) ∈ Set.Icc (-1) 1 := by
  have hl : (0 : ℚ) ≤ clamp 0 1 (cosTaylor (taylorOrder N)
      (((if 2 * r < gridSize N then r else gridSize N - r) : ℕ) *
        piTaylor (precision N) / gridSize N)) := clamp_lower
  have hu : clamp 0 1 (cosTaylor (taylorOrder N)
      (((if 2 * r < gridSize N then r else gridSize N - r) : ℕ) *
        piTaylor (precision N) / gridSize N)) ≤ (1 : ℚ) := clamp_upper (by norm_num)
  have h := (Rat.cast_le (K := ℝ)).mpr hl
  have h' := (Rat.cast_le (K := ℝ)).mpr hu
  unfold gridSample
  dsimp only
  split_ifs <;> (try simp_all only [↓reduceIte]) <;> push_cast at * <;> constructor <;> linarith

end
end FlatFrontend
end Power2ModuleSVP
