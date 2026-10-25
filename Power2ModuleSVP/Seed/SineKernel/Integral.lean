module

public import Power2ModuleSVP.Seed.SineKernel.Specification
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Algebra.Field.Periodic
import Mathlib.Tactic

/-!
# Integral

Exact integral and reflection identities for `lem:sine-kernel`. The
continuous sinc convention keeps all statements valid at the removable
singularity. These identities do not assume the quantitative decomposition
contract from `Seed/SineKernel/Specification.lean`.

Paper: `paper/power2svp.pdf`, Appendix A.2 (Lemma 10, filling the small intervals).
-/

@[expose] public section

namespace Power2ModuleSVP

open scoped BigOperators

noncomputable section

namespace SeedKernelIntervals

/-- The normalized odd Fourier coefficients, before the factor `K sqrt N`. -/
def sineCoefficient {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) (j : ℕ) : ℝ :=
  4 * ∑ i, α i * ∫ u in I.leftAngle i..I.rightAngle i,
    Real.sin ((2 * (j : ℝ) + 1) * u)

/-- The reflected integral is exactly the finite odd sine polynomial. -/
theorem transform_eq_sine_sum {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) (θ : ℝ) :
    I.transform α θ = ∑ j ∈ Finset.range N,
      I.sineCoefficient α j * Real.sin ((2 * (j : ℝ) + 1) * θ) := by
  unfold transform sineCoefficient
  simp_rw [← odd_sine_reproducing_identity]
  simp_rw [intervalIntegral.integral_const_mul]
  have hsum (a b : ℝ) :
      (∫ u in a..b, ∑ j ∈ Finset.range N,
        Real.sin ((2 * (j : ℝ) + 1) * u) * Real.sin ((2 * (j : ℝ) + 1) * θ)) =
      ∑ j ∈ Finset.range N, ∫ u in a..b,
        Real.sin ((2 * (j : ℝ) + 1) * u) * Real.sin ((2 * (j : ℝ) + 1) * θ) :=
    intervalIntegral.integral_finsetSum (fun j _ =>
      (by fun_prop : Continuous (fun u : ℝ =>
        Real.sin ((2 * (j : ℝ) + 1) * u) *
          Real.sin ((2 * (j : ℝ) + 1) * θ))).intervalIntegrable a b)
  simp_rw [hsum]
  simp_rw [intervalIntegral.integral_mul_const]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Each coefficient has an exact endpoint formula; the frequency is never
zero. This is the expression to approximate by rational enclosures. -/
theorem sineCoefficient_eq_cos {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) (j : ℕ) :
    I.sineCoefficient α j = 4 * ∑ i, α i *
      ((Real.cos ((2 * (j : ℝ) + 1) * I.leftAngle i) -
        Real.cos ((2 * (j : ℝ) + 1) * I.rightAngle i)) /
          (2 * (j : ℝ) + 1)) := by
  have hf : 2 * (j : ℝ) + 1 ≠ 0 := by positivity
  simp only [sineCoefficient, intervalIntegral.integral_comp_mul_left Real.sin hf,
    integral_sin, smul_eq_mul, div_eq_inv_mul]

/-- The individual matrix entry bound before multiplication by `4 K sqrt N`.
It uses the six-cell width and works for every real frequency. -/
theorem sine_integral_abs_le {N J : ℕ} (I : SeedKernelIntervals N J)
    (hN : 0 < N) (i : Fin J) (m : ℝ) :
    |∫ u in I.leftAngle i..I.rightAngle i, Real.sin (m * u)| ≤
      6 * Real.pi / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hlr : (I.left i : ℝ) ≤ I.right i := by
    exact_mod_cast (I.width_pos i).le
  have hwidth : (I.right i : ℝ) ≤ I.left i + 6 := by
    exact_mod_cast I.width_le i
  have horder : I.leftAngle i ≤ I.rightAngle i := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlr Real.pi_pos.le) hn.le
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := I.leftAngle i) (b := I.rightAngle i) (C := (1 : ℝ))
    (f := fun u : ℝ => Real.sin (m * u))
    (fun u _ => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (m * u))
  rw [Real.norm_eq_abs, one_mul, abs_of_nonneg (sub_nonneg.mpr horder)] at h
  refine h.trans ?_
  unfold leftAngle rightAngle
  rw [← sub_div, div_le_div_iff_of_pos_right hn]
  nlinarith [mul_le_mul_of_nonneg_right hwidth Real.pi_pos.le]

@[simp] theorem transform_neg {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) (θ : ℝ) : I.transform α (-θ) = -I.transform α θ := by
  simp [transform_eq_sine_sum, mul_neg, Real.sin_neg, Finset.sum_neg_distrib]

@[simp] theorem transform_add_pi {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) (θ : ℝ) :
    I.transform α (θ + Real.pi) = -I.transform α θ := by
  simp only [transform_eq_sine_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have harg : (2 * (j : ℝ) + 1) * (θ + Real.pi) =
      (2 * (j : ℝ) + 1) * θ + (2 * j + 1 : ℕ) * Real.pi := by push_cast; ring
  rw [harg, Real.sin_add_nat_mul_pi]
  simp [pow_add, pow_mul]

@[simp] theorem transform_pi_sub {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) (θ : ℝ) :
    I.transform α (Real.pi - θ) = I.transform α θ := by
  rw [show Real.pi - θ = -θ + Real.pi by ring, transform_add_pi, transform_neg,
    neg_neg]

theorem transform_periodic {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) : Function.Periodic (I.transform α) (2 * Real.pi) := by
  intro θ
  rw [show θ + 2 * Real.pi = (θ + Real.pi) + Real.pi by ring,
    transform_add_pi, transform_add_pi, neg_neg]

@[simp] theorem transform_zero {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) : I.transform α 0 = 0 := by
  simp [transform_eq_sine_sum]

@[simp] theorem transform_pi {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) : I.transform α Real.pi = 0 := by
  simpa using I.transform_add_pi α 0

theorem transform_continuous {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) : Continuous (I.transform α) := by
  have heq : I.transform α = fun θ => ∑ j ∈ Finset.range N,
      I.sineCoefficient α j * Real.sin ((2 * (j : ℝ) + 1) * θ) :=
    funext (I.transform_eq_sine_sum α)
  rw [heq]
  fun_prop

/-- Absolute values have period pi, so the first quadrant controls every
real angle. -/
theorem abs_transform_periodic {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) : Function.Periodic (fun θ => |I.transform α θ|) Real.pi := by
  intro θ
  simp

theorem exists_first_quadrant_abs_transform {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) (θ : ℝ) :
    ∃ φ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |I.transform α θ| = |I.transform α φ| := by
  obtain ⟨φ, hφ, heq⟩ := (I.abs_transform_periodic α).exists_mem_Ico₀ Real.pi_pos θ
  by_cases hhalf : φ ≤ Real.pi / 2
  · exact ⟨φ, ⟨hφ.1, hhalf⟩, heq⟩
  · refine ⟨Real.pi - φ, ⟨by linarith [hφ.2], by linarith⟩, ?_⟩
    simpa using heq

/-- The full reflected, pi-periodic union, described without indicators or
a choice of angle representatives. -/
def reflectedContains {N J : ℕ} (I : SeedKernelIntervals N J) (θ : ℝ) : Prop :=
  ∃ φ, I.contains φ ∧ ∃ k : ℤ,
    θ = φ + k * Real.pi ∨ θ = -φ + k * Real.pi

theorem contains_first_quadrant {N J : ℕ} (I : SeedKernelIntervals N J)
    (hN : 0 < N) {θ : ℝ} (hθ : I.contains θ) :
    θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  obtain ⟨i, hleft, hright⟩ := hθ
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : (I.right i : ℝ) ≤ (N : ℝ) / 2 := by
    have h := I.right_clearance i
    have h' : (2 : ℝ) * (I.right i + 100) ≤ N := by exact_mod_cast h
    linarith
  constructor
  · exact le_trans (by unfold leftAngle; positivity) hleft
  · exact hright.trans (by
      unfold rightAngle
      apply (div_le_iff₀ hn).2
      nlinarith [mul_le_mul_of_nonneg_right hr Real.pi_pos.le])

theorem reflectedContains_abs_transform {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) {θ : ℝ} (hθ : I.reflectedContains θ) :
    ∃ φ, I.contains φ ∧ |I.transform α θ| = |I.transform α φ| := by
  obtain ⟨φ, hφ, k, rfl | rfl⟩ := hθ
  · refine ⟨φ, hφ, ?_⟩
    simpa only [zsmul_eq_mul] using (I.abs_transform_periodic α).zsmul k φ
  · refine ⟨φ, hφ, ?_⟩
    simpa only [zsmul_eq_mul, transform_neg, abs_neg] using
      (I.abs_transform_periodic α).zsmul k (-φ)

end SeedKernelIntervals

/-- The global reflection step in the sine-kernel estimate. Only the
quantitative first-quadrant decomposition remains a premise. -/
theorem sine_kernel_global_of_decomposition (h : SineKernelDecompositionHypothesis)
    {N J : ℕ} (I : SeedKernelIntervals N J) (α : Fin J → ℝ)
    (hN : 2 ^ 20 ≤ N) (hα : ∀ i, α i = -1 ∨ α i = 1) (θ : ℝ) :
    |I.transform α θ| < 5 ∧
      (I.reflectedContains θ → 2 / 3 < |I.transform α θ|) := by
  constructor
  · obtain ⟨φ, hφ, heq⟩ := I.exists_first_quadrant_abs_transform α θ
    rw [heq]
    exact (sine_kernel_of_decomposition h I α hN hα hφ).1
  · intro hθ
    obtain ⟨φ, hφ, heq⟩ := I.reflectedContains_abs_transform α hθ
    rw [heq]
    exact (sine_kernel_of_decomposition h I α hN hα
      (I.contains_first_quadrant (by omega) hφ)).2 hφ

theorem sine_kernel_scaled_global_of_decomposition (h : SineKernelDecompositionHypothesis)
    {N J : ℕ} (I : SeedKernelIntervals N J) (α : Fin J → ℝ)
    (hN : 2 ^ 20 ≤ N) (hα : ∀ i, α i = -1 ∨ α i = 1)
    {K : ℝ} (hK : 0 ≤ K) (θ : ℝ) :
    |K * Real.sqrt N * I.transform α θ| ≤ 5 * K * Real.sqrt N ∧
      (I.reflectedContains θ → (2 * K / 3) * Real.sqrt N ≤
        |K * Real.sqrt N * I.transform α θ|) := by
  obtain ⟨hu, hl⟩ := sine_kernel_global_of_decomposition h I α hN hα θ
  have hscale : 0 ≤ K * Real.sqrt N := mul_nonneg hK (Real.sqrt_nonneg _)
  rw [abs_mul, abs_of_nonneg hscale]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hu.le hscale]
  · intro hθ
    nlinarith [mul_le_mul_of_nonneg_left (hl hθ).le hscale]

/-- The sine integral with its continuous integrand at zero. -/
def seedSineIntegral (x : ℝ) : ℝ := ∫ v in 0..x, Real.sinc v

@[simp] theorem seedSineIntegral_zero : seedSineIntegral 0 = 0 := by
  simp [seedSineIntegral]

theorem seedSineIntegral_sub (a b : ℝ) :
    seedSineIntegral b - seedSineIntegral a = ∫ v in a..b, Real.sinc v := by
  unfold seedSineIntegral
  exact intervalIntegral.integral_interval_sub_left (μ := MeasureTheory.volume)
    (Real.continuous_sinc.intervalIntegrable 0 b)
    (Real.continuous_sinc.intervalIntegrable 0 a)

@[simp] theorem seedSineIntegral_neg (x : ℝ) :
    seedSineIntegral (-x) = -seedSineIntegral x := by
  unfold seedSineIntegral
  have h := intervalIntegral.integral_comp_neg Real.sinc (a := 0) (b := x)
  simp only [Real.sinc_neg, neg_zero] at h
  rw [intervalIntegral.integral_symm, ← h]

/-- The exact local sinc expression, including zero and both endpoints. -/
theorem local_sinc_integral (N : ℕ) (θ a b : ℝ) :
    (∫ u in a..b, 2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ))) =
      seedSineIntegral (2 * (N : ℝ) * (b - θ)) -
        seedSineIntegral (2 * (N : ℝ) * (a - θ)) := by
  rw [seedSineIntegral_sub, intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_mul_sub Real.sinc
    (a := a) (b := b) (2 * (N : ℝ)) (2 * (N : ℝ) * θ)
  simp only [smul_eq_mul] at h
  simpa only [mul_sub] using h

/-- When the observation point lies in the interval the two sinc arguments
are nonnegative. Their sum is exactly the scaled interval width. -/
theorem local_sinc_integral_inside (N : ℕ) (θ a b : ℝ)
    (hθ : θ ∈ Set.Icc a b) :
    (∫ u in a..b, 2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ))) =
      seedSineIntegral (2 * (N : ℝ) * (b - θ)) +
        seedSineIntegral (2 * (N : ℝ) * (θ - a)) ∧
      0 ≤ 2 * (N : ℝ) * (b - θ) ∧
      0 ≤ 2 * (N : ℝ) * (θ - a) := by
  constructor
  · rw [local_sinc_integral,
      show 2 * (N : ℝ) * (a - θ) = -(2 * (N : ℝ) * (θ - a)) by ring,
      seedSineIntegral_neg, sub_neg_eq_add]
  · exact ⟨mul_nonneg (by positivity) (sub_nonneg.mpr hθ.2),
      mul_nonneg (by positivity) (sub_nonneg.mpr hθ.1)⟩

/-- The local containing-interval estimate reduced precisely to the three
sine-integral inequalities. The arguments need not individually exceed pi:
their sum is at least `2 pi`, which suffices. -/
theorem local_sinc_integral_inside_bounds
    (hSi_nonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ seedSineIntegral x)
    (hSi_upper : ∀ x : ℝ, 0 ≤ x → seedSineIntegral x ≤ 2)
    (hSi_lower : ∀ x : ℝ, Real.pi ≤ x → 4 / 3 ≤ seedSineIntegral x)
    {N : ℕ} (hN : 0 < N) (θ a b : ℝ) (hθ : θ ∈ Set.Icc a b)
    (hwidth : Real.pi / N ≤ b - a) :
    4 / 3 ≤ (∫ u in a..b,
        2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ))) ∧
      (∫ u in a..b,
        2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ))) ≤ 4 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨heq, hx, hy⟩ := local_sinc_integral_inside N θ a b hθ
  rw [heq]
  have hx0 := hSi_nonneg _ hx
  have hy0 := hSi_nonneg _ hy
  have hx2 := hSi_upper _ hx
  have hy2 := hSi_upper _ hy
  have hsum : 2 * Real.pi ≤
      2 * (N : ℝ) * (b - θ) + 2 * (N : ℝ) * (θ - a) := by
    have hw := (div_le_iff₀ hn).1 hwidth
    nlinarith
  constructor
  · by_cases hlarge : Real.pi ≤ 2 * (N : ℝ) * (b - θ)
    · linarith [hSi_lower _ hlarge]
    · have hlarge' : Real.pi ≤ 2 * (N : ℝ) * (θ - a) := by linarith
      linarith [hSi_lower _ hlarge']
  · linarith

end

end Power2ModuleSVP
