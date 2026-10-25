import Power2ModuleSVP.Seed.Algorithm
import Power2ModuleSVP.Seed.Flat.Taylor

/-!
# Bounds

Numerical and complex-norm margins in the final flat-seed assembly.

Paper: `paper/power2svp.pdf`, Appendix A (Theorem 5, the deterministic flat seed).
-/
namespace Power2ModuleSVP

noncomputable def seedCosineMargin : ℝ := 1 / 2 ^ 250

theorem seedCosineMargin_pos : 0 < seedCosineMargin := by
  unfold seedCosineMargin
  positivity

theorem seed_degree_bounds {d : ℕ} (hd : 2 ^ 512 ≤ d) :
    2 ^ 504 ≤ seedN d ∧ d ≤ 5 * seedN d := by
  unfold seedN
  omega

/-- The loss of the center coefficient and all three appended monomials
is included. This arithmetic works for every large degree. -/
theorem seed_final_margin {d : ℕ} (hd : 2 ^ 512 ≤ d) :
    (seedConstant : ℝ) * Real.sqrt d ≤
      2 * seedCosineMargin * Real.sqrt (seedN d) - 4 := by
  obtain ⟨hN, hdim⟩ := seed_degree_bounds hd
  have hNsqrt : (2 : ℝ) ^ 252 ≤ Real.sqrt (seedN d) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    rw [← pow_mul]
    norm_num only [Nat.reduceMul]
    exact_mod_cast hN
  have hc : 4 ≤ seedCosineMargin * Real.sqrt (seedN d) := by
    have hm := mul_le_mul_of_nonneg_left hNsqrt seedCosineMargin_pos.le
    norm_num [seedCosineMargin] at hm ⊢
    exact hm
  have hsqrt : Real.sqrt d ≤ 3 * Real.sqrt (seedN d) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hcast : (d : ℝ) ≤ 5 * seedN d := by exact_mod_cast hdim
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (seedN d))]
  have htarget := mul_le_mul_of_nonneg_left hsqrt
    (show (0 : ℝ) ≤ seedConstant by exact_mod_cast seedConstant_pos.le)
  have heq : 3 * (seedConstant : ℝ) = (3 / 4) * seedCosineMargin := by
    norm_num [seedConstant, seedCosineMargin]
  nlinarith

/-- A rotation preserves norm; a bounded appended tail costs its norm. -/
theorem seed_core_norm_le {u core tail value : ℂ}
    (hu : ‖u‖ = 1) (ht : ‖tail‖ ≤ 3) (he : value = u * core + tail) :
    ‖core‖ ≤ ‖value‖ + 3 := by
  have h := norm_sub_le value tail
  rw [he, add_sub_cancel_right, norm_mul, hu, one_mul] at h
  rw [← he] at h
  linarith

/-- The two real/imaginary alternatives of the construction, after the
kernel and Taylor estimates have been supplied. -/
theorem seed_core_lower {N : ℕ} {c e so sb : ℝ} {u tail value : ℂ}
    (hu : ‖u‖ = 1) (ht : ‖tail‖ ≤ 3)
    (he : value = u * ((1 + 2 * c : ℝ) +
      2 * Complex.I * ((e + so : ℝ) : ℂ)) + tail)
    (heven : |e| ≤ 6 * Real.sqrt N)
    (hcase : seedCosineMargin * Real.sqrt N ≤ |c| ∨
      (6000 * Real.sqrt N ≤ |sb| ∧ |so - sb| ≤ 5900 * Real.sqrt N)) :
    2 * seedCosineMargin * Real.sqrt N - 4 ≤ ‖value‖ := by
  let core : ℂ := (1 + 2 * c : ℝ) + 2 * Complex.I * ((e + so : ℝ) : ℂ)
  have hn := seed_core_norm_le hu ht he
  change ‖core‖ ≤ ‖value‖ + 3 at hn
  rcases hcase with hc | ⟨hb, herr⟩
  · have hr : |1 + 2 * c| ≤ ‖core‖ := by
      simpa [core] using Complex.abs_re_le_norm core
    have htri := abs_add_le (1 + 2 * c) (-1)
    have hcalc : |1 + 2 * c + -1| = 2 * |c| := by
      rw [show 1 + 2 * c + -1 = 2 * c by ring, abs_mul]
      norm_num
    rw [hcalc] at htri
    norm_num at htri
    linarith
  · have him : 2 * |e + so| ≤ ‖core‖ := by
      have hh := Complex.abs_im_le_norm core
      simpa [core, abs_mul] using hh
    have hb' := abs_add_le (sb - so) so
    rw [sub_add_cancel, abs_sub_comm] at hb'
    have hs : 100 * Real.sqrt N ≤ |so| := by linarith
    have hs' := abs_add_le (e + so) (-e)
    rw [show e + so + -e = so by ring, abs_neg] at hs'
    have hC : seedCosineMargin ≤ 1 := by norm_num [seedCosineMargin]
    have hsmall := mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg N)
    nlinarith [Real.sqrt_nonneg (N : ℝ)]

end Power2ModuleSVP
