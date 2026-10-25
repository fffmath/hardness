module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# The finite odd-frequency sine kernel

Define the finite kernel and its interval transform, including removable singularities, and
isolate the quantitative local-and-tail estimates. Seed/SineKernel/Decomposition.lean discharges
the decomposition interface unconditionally.

Paper: `paper/power2svp.pdf`, Appendix A.2 (Lemma 10, filling the small intervals).
-/

@[expose] public section

namespace Power2ModuleSVP

open scoped BigOperators

noncomputable section

/-- The continuous odd-frequency Dirichlet kernel, including its removable
singularities at integer multiples of pi. -/
def oddCosineKernel (N : ℕ) (v : ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.range N, Real.cos ((2 * (j : ℝ) + 1) * v)

theorem oddCosineKernel_continuous (N : ℕ) : Continuous (oddCosineKernel N) := by
  unfold oddCosineKernel
  fun_prop

theorem oddCosineKernel_mul_sin (N : ℕ) (v : ℝ) :
    oddCosineKernel N v * Real.sin v = Real.sin (2 * (N : ℝ) * v) := by
  have h := Real.sin_mul_sum_cos N (2 * v) v
  have harg : ((N : ℝ) - 1) * (2 * v) / 2 + v = (N : ℝ) * v := by ring
  have harg' : (N : ℝ) * (2 * v) / 2 = (N : ℝ) * v := by ring
  rw [harg, harg'] at h
  have hsum : (∑ i ∈ Finset.range N, Real.cos (2 * v * i + v)) =
      ∑ i ∈ Finset.range N, Real.cos ((2 * (i : ℝ) + 1) * v) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    ring
  rw [show 2 * v / 2 = v by ring] at h
  rw [hsum] at h
  rw [oddCosineKernel, show 2 * (N : ℝ) * v = 2 * ((N : ℝ) * v) by ring,
    Real.sin_two_mul]
  nlinarith [h]

/-- The quotient formula is used only away from the removable singularities. -/
theorem oddCosineKernel_eq_div (N : ℕ) {v : ℝ} (hv : Real.sin v ≠ 0) :
    oddCosineKernel N v = Real.sin (2 * (N : ℝ) * v) / Real.sin v :=
  (eq_div_iff hv).2 (oddCosineKernel_mul_sin N v)

@[simp] theorem oddCosineKernel_zero (N : ℕ) : oddCosineKernel N 0 = 2 * N := by
  simp [oddCosineKernel]

/-- The factor four in the reflected sine projection. This identity is
valid at all angles, with no exceptional denominator-zero cases. -/
theorem odd_sine_reproducing_identity (N : ℕ) (u θ : ℝ) :
    4 * (∑ j ∈ Finset.range N,
      Real.sin ((2 * (j : ℝ) + 1) * u) * Real.sin ((2 * (j : ℝ) + 1) * θ)) =
      oddCosineKernel N (u - θ) - oddCosineKernel N (u + θ) := by
  simp only [oddCosineKernel, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_sub, mul_add, Real.cos_sub, Real.cos_add]
  ring

/-- The total discarded contribution appearing in the kernel estimate. -/
def sineKernelError (N : ℕ) : ℝ :=
  2 / ((N : ℝ) * Real.sin (100 * Real.pi / N)) + (12 * Real.pi + 2) / N + 2 / Real.pi

/-- A deliberately coarse Jordan bound already leaves enough room for the
stated two-thirds error allowance. -/
theorem sineKernelError_lt (N : ℕ) (hN : 2 ^ 20 ≤ N) : sineKernelError N < 2 / 3 := by
  have hNr : (1048576 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ) < N := by linarith
  have hx₀ : (0 : ℝ) ≤ 100 * Real.pi / N := by positivity
  have hx₁ : 100 * Real.pi / N ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hn).2
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_le_sin hx₀ hx₁
  have hprod : (N : ℝ) * (2 / Real.pi * (100 * Real.pi / N)) = 200 := by
    field_simp
    ring
  have hden : (200 : ℝ) ≤ N * Real.sin (100 * Real.pi / N) := by
    have h := mul_le_mul_of_nonneg_left hsin hn.le
    rwa [hprod] at h
  have hdenpos : (0 : ℝ) < N * Real.sin (100 * Real.pi / N) := by linarith
  have hfirst : 2 / ((N : ℝ) * Real.sin (100 * Real.pi / N)) ≤ 1 / 100 := by
    apply (div_le_iff₀ hdenpos).2
    linarith
  have hsecond : (12 * Real.pi + 2) / (N : ℝ) < 1 / 1000 := by
    apply (div_lt_iff₀ hn).2
    nlinarith [Real.pi_lt_four]
  have hthird : 2 / Real.pi < (13 : ℝ) / 20 := by
    apply (div_lt_iff₀ Real.pi_pos).2
    linarith [Real.pi_gt_d2]
  unfold sineKernelError
  linarith

/-- First-quadrant components, with integer grid endpoints, width between
one and six cells, one-cell gaps and one hundred cells of axis clearance. -/
structure SeedKernelIntervals (N J : ℕ) where
  left : Fin J → ℕ
  right : Fin J → ℕ
  width_pos : ∀ i, left i < right i
  width_le : ∀ i, right i ≤ left i + 6
  left_clearance : ∀ i, 100 ≤ left i
  right_clearance : ∀ i, 2 * (right i + 100) ≤ N
  separated : ∀ i j, i ≠ j → right i + 1 ≤ left j ∨ right j + 1 ≤ left i

namespace SeedKernelIntervals

/-- The left endpoint of a kernel interval expressed as an angle. -/
def leftAngle {N J : ℕ} (I : SeedKernelIntervals N J) (i : Fin J) : ℝ :=
  I.left i * Real.pi / N

/-- The right endpoint of a kernel interval expressed as an angle. -/
def rightAngle {N J : ℕ} (I : SeedKernelIntervals N J) (i : Fin J) : ℝ :=
  I.right i * Real.pi / N

/-- The angle belongs to one of the closed kernel intervals. -/
def contains {N J : ℕ} (I : SeedKernelIntervals N J) (θ : ℝ) : Prop :=
  ∃ i, θ ∈ Set.Icc (I.leftAngle i) (I.rightAngle i)

/-- The normalized first-quadrant formula after the two reflections. -/
def transform {N J : ℕ} (I : SeedKernelIntervals N J) (α : Fin J → ℝ) (θ : ℝ) : ℝ :=
  ∑ i, α i * ∫ u in I.leftAngle i..I.rightAngle i,
    (oddCosineKernel N (u - θ) - oddCosineKernel N (u + θ))

end SeedKernelIntervals

/-- Analytic decomposition contract for `lem:sine-kernel`. The error term
collects the reflected kernel, the cosecant-minus-reciprocal correction,
and distant intervals. The local term is the one or two nearby sinc
integrals. Establishing these bounds requires the sine-integral estimates
and integration-by-parts/variation argument; neither is assumed silently. -/
structure SineKernelDecompositionHypothesis : Prop where
  decompose : ∀ (N J : ℕ) (I : SeedKernelIntervals N J) (α : Fin J → ℝ),
    2 ^ 20 ≤ N → (∀ i, α i = -1 ∨ α i = 1) →
    ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      ∃ localPart errorPart : ℝ,
        I.transform α θ = localPart + errorPart ∧
        |errorPart| ≤ sineKernelError N ∧ |localPart| ≤ 4 ∧
        (I.contains θ → 4 / 3 ≤ |localPart|)

/-- First-quadrant kernel bounds, conditional exactly on the unresolved
local/tail decomposition. Scaling gives the constants in the paper. -/
theorem sine_kernel_of_decomposition (h : SineKernelDecompositionHypothesis)
    {N J : ℕ} (I : SeedKernelIntervals N J) (α : Fin J → ℝ)
    (hN : 2 ^ 20 ≤ N) (hα : ∀ i, α i = -1 ∨ α i = 1)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |I.transform α θ| < 5 ∧ (I.contains θ → 2 / 3 < |I.transform α θ|) := by
  obtain ⟨l, e, heq, he, hl, hlow⟩ := h.decompose N J I α hN hα θ hθ
  have hE := sineKernelError_lt N hN
  rw [heq]
  constructor
  · have hsum := abs_add_le l e
    linarith
  · intro hi
    have hsub := abs_sub_abs_le_abs_sub l (l + e)
    have hs : |l - (l + e)| = |e| := by simp
    rw [hs] at hsub
    have := hlow hi
    linarith

/-- The original scaling constants, on the first quadrant. The global
reflection extension is a separate step in the seed construction. -/
theorem sine_kernel_scaled_of_decomposition (h : SineKernelDecompositionHypothesis)
    {N J : ℕ} (I : SeedKernelIntervals N J) (α : Fin J → ℝ)
    (hN : 2 ^ 20 ≤ N) (hα : ∀ i, α i = -1 ∨ α i = 1)
    {K θ : ℝ} (hK : 0 ≤ K) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |K * Real.sqrt N * I.transform α θ| ≤ 5 * K * Real.sqrt N ∧
      (I.contains θ → (2 * K / 3) * Real.sqrt N ≤
        |K * Real.sqrt N * I.transform α θ|) := by
  obtain ⟨hupper, hlower⟩ := sine_kernel_of_decomposition h I α hN hα hθ
  have hscale : 0 ≤ K * Real.sqrt N := mul_nonneg hK (Real.sqrt_nonneg _)
  have habs : |K * Real.sqrt N * I.transform α θ| =
      (K * Real.sqrt N) * |I.transform α θ| := by
    rw [abs_mul, abs_of_nonneg hscale]
  simp only [habs]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hupper.le hscale]
  · intro hi
    nlinarith [mul_le_mul_of_nonneg_left (hlower hi).le hscale]

end

end Power2ModuleSVP
