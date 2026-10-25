module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Jet Separation

Algebraic separation of the first four real jets of a two-frequency wave.
This is the finite-dimensional part of the seven-cell exclusion argument in
`lem:seed-intervals`; it does not assume the analytic interpolation step.

Paper: `paper/power2svp.pdf`, Appendix A.1 (Lemma 9, Rudin–Shapiro waves and small intervals).
-/

@[expose] public section

namespace Power2ModuleSVP

/-- The inverse jet identities force a strict loss of squared norm when
all four real jets have magnitude at most three eighths. -/
theorem seed_two_frequency_jet_norm_bound (a b : ℂ)
    (h0 : |(a + b).re| ≤ 3 / 8)
    (h1 : |(Complex.I * a + (2 * Complex.I) * b).re| ≤ 3 / 8)
    (h2 : |(-a - 4 * b).re| ≤ 3 / 8)
    (h3 : |(-Complex.I * a - (8 * Complex.I) * b).re| ≤ 3 / 8) :
    Complex.normSq a + Complex.normSq b ≤ 55 / 64 := by
  have ha : |a.re| ≤ 5 / 8 := by
    rcases abs_le.mp h0 with ⟨h01, h02⟩
    rcases abs_le.mp h2 with ⟨h21, h22⟩
    simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.neg_im,
      Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at *
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : |b.re| ≤ 1 / 4 := by
    rcases abs_le.mp h0 with ⟨h01, h02⟩
    rcases abs_le.mp h2 with ⟨h21, h22⟩
    simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.neg_im,
      Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at *
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hc : |a.im| ≤ 5 / 8 := by
    rcases abs_le.mp h1 with ⟨h11, h12⟩
    rcases abs_le.mp h3 with ⟨h31, h32⟩
    simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.neg_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero,
      one_mul, mul_one, add_zero, sub_zero, zero_sub] at *
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hd : |b.im| ≤ 1 / 8 := by
    rcases abs_le.mp h1 with ⟨h11, h12⟩
    rcases abs_le.mp h3 with ⟨h31, h32⟩
    simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.neg_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero,
      one_mul, mul_one, add_zero, sub_zero, zero_sub] at *
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hasq := (sq_le_sq₀ (abs_nonneg a.re) (by norm_num : (0 : ℝ) ≤ 5 / 8)).mpr ha
  have hbsq := (sq_le_sq₀ (abs_nonneg b.re) (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hb
  have hcsq := (sq_le_sq₀ (abs_nonneg a.im) (by norm_num : (0 : ℝ) ≤ 5 / 8)).mpr hc
  have hdsq := (sq_le_sq₀ (abs_nonneg b.im) (by norm_num : (0 : ℝ) ≤ 1 / 8)).mpr hd
  simp only [sq_abs] at hasq hbsq hcsq hdsq
  simp only [Complex.normSq_apply]
  nlinarith

/-- Four approximate real jets of a normalized two-frequency wave cannot
all have magnitude strictly below one quarter. -/
theorem seed_two_frequency_jet_separation (a b : ℂ)
    (hnorm : Complex.normSq a + Complex.normSq b = 1)
    (f : Fin 4 → ℝ)
    (h0 : |f 0 - (a + b).re| < 1 / 8)
    (h1 : |f 1 - (Complex.I * a + (2 * Complex.I) * b).re| < 1 / 8)
    (h2 : |f 2 - (-a - 4 * b).re| < 1 / 8)
    (h3 : |f 3 - (-Complex.I * a - (8 * Complex.I) * b).re| < 1 / 8) :
    ∃ r : Fin 4, 1 / 4 ≤ |f r| := by
  by_contra h
  push Not at h
  have hb (r : Fin 4) (e : ℝ) (he : |f r - e| < 1 / 8) : |e| ≤ 3 / 8 := by
    have ht := abs_add_le (e - f r) (f r)
    rw [sub_add_cancel, abs_sub_comm] at ht
    linarith [h r]
  have hn := seed_two_frequency_jet_norm_bound a b
    (hb 0 _ h0) (hb 1 _ h1) (hb 2 _ h2) (hb 3 _ h3)
  linarith

end Power2ModuleSVP
