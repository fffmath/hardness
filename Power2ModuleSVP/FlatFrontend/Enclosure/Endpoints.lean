import Power2ModuleSVP.FlatFrontend.Enclosure.Precision
import Power2ModuleSVP.FlatFrontend.Enclosure.Kernel

/-!
# Endpoints

Endpoint evaluation bounds for the executable first matrix.

Paper: `paper/power2svp.pdf`, Appendix A.3 (rational enclosures and the two rounding steps).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
noncomputable section

/-- Endpoint phases never exceed the dimension. -/
theorem endpointPhase_bound {N : ℕ} (j : Fin N) {a : ℕ} (ha : 2 * a ≤ N) :
    0 ≤ ((((2 * j.val + 1) * a : ℕ) : ℚ) / N) ∧
      ((((2 * j.val + 1) * a : ℕ) : ℚ) / N) ≤ N := by
  have hn : (0 : ℚ) < N := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hj : (j.val : ℚ) + 1 ≤ N := by exact_mod_cast j.isLt
  have har : 2 * (a : ℚ) ≤ N := by exact_mod_cast ha
  constructor
  · positivity
  · apply (div_le_iff₀ hn).mpr
    push_cast
    nlinarith [mul_nonneg (by positivity : (0 : ℚ) ≤ a)
      (by linarith : (0 : ℚ) ≤ 2 * N - (2 * j.val + 1))]

theorem endpoint_cos_error {N : ℕ} (j : Fin N) {a : ℕ} (ha : 2 * a ≤ N) :
    |Real.cos ((2 * (j : ℝ) + 1) * (a * Real.pi / N)) -
      (cosTaylor (taylorOrder N)
        ((((2 * j.val + 1) * a : ℕ) : ℚ) * piTaylor (precision N) / N) : ℝ)| ≤
      (((4 * (N : ℚ) + 2) * fineError N : ℚ) : ℝ) := by
  have hb := endpointPhase_bound j ha
  have hh := phase_error_fine hb.1 hb.2 1
  have he : (2 * (j : ℝ) + 1) * (a * Real.pi / N) =
      (((((2 * j.val + 1) * a : ℕ) : ℚ) / N : ℚ) : ℝ) * Real.pi := by
    push_cast
    ring
  rw [he]
  have heq : ((((2 * j.val + 1) * a : ℕ) : ℚ) / N) * piTaylor (precision N) =
      (((2 * j.val + 1) * a : ℕ) : ℚ) * piTaylor (precision N) / N := by ring
  rw [heq] at hh
  simpa [jetSin, phaseTaylor, phase] using hh

theorem realKernelEntry_eq_cos {N J : ℕ} (I : SeedKernelIntervals N J)
    (i : Fin J) (j : ℕ) :
    realKernelEntry I i j = 36000 * Real.sqrt N *
      (Real.cos ((2 * (j : ℝ) + 1) * I.leftAngle i) -
        Real.cos ((2 * (j : ℝ) + 1) * I.rightAngle i)) / (2 * (j : ℝ) + 1) := by
  have hf : 2 * (j : ℝ) + 1 ≠ 0 := by positivity
  simp only [realKernelEntry, intervalIntegral.integral_comp_mul_left Real.sin hf,
    integral_sin, smul_eq_mul, div_eq_inv_mul]
  ring

/-- One uniform entry tolerance; the dimension powers leave room for summing
all intervals. It bounds the original frontend, without changing precision. -/
def kernelError (N : ℕ) : ℚ := 432000 * ((N : ℚ) + 1) ^ 2 * fineError N

theorem kernelError_nonnegative (N : ℕ) : 0 ≤ kernelError N := by
  unfold kernelError
  have := (fineError_pos N).le
  positivity

theorem kernelEntry_error {N J : ℕ} (I : SeedKernelIntervals N J)
    (i : Fin J) (j : Fin N) :
    |(kernelEntry N (I.left i, I.right i) j : ℝ) - realKernelEntry I i j| ≤
      (kernelError N : ℝ) := by
  have hleft : 2 * I.left i ≤ N := by
    have := I.right_clearance i
    have := I.width_pos i
    omega
  have hright : 2 * I.right i ≤ N := by have := I.right_clearance i; omega
  have hl := endpoint_cos_error j hleft
  have hr := endpoint_cos_error j hright
  have hs := sqrtApprox_spec (precision N) N
  have hs0 : (0 : ℝ) ≤ sqrtApprox (precision N) N := by
    exact_mod_cast sqrtApprox_nonnegative (precision N) N
  have hf : (1 : ℝ) / 2 ^ precision N ≤ (fineError N : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (precision_fine N)
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, one_div_pow] using hh
  have hsqrt : Real.sqrt N ≤ (N : ℝ) + 1 := by
    have hh := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have := Real.sqrt_nonneg (N : ℝ)
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  let A := Real.cos ((2 * (j : ℝ) + 1) * I.leftAngle i)
  let B := Real.cos ((2 * (j : ℝ) + 1) * I.rightAngle i)
  let a : ℝ := cosTaylor (taylorOrder N)
    ((((2 * j.val + 1) * I.left i : ℕ) : ℚ) * piTaylor (precision N) / N)
  let b : ℝ := cosTaylor (taylorOrder N)
    ((((2 * j.val + 1) * I.right i : ℕ) : ℚ) * piTaylor (precision N) / N)
  let s : ℝ := sqrtApprox (precision N) N
  let t : ℝ := Real.sqrt N
  let δ : ℝ := ((4 * (N : ℚ) + 2) * fineError N : ℚ)
  have hδ : 0 ≤ δ := by dsimp [δ]; exact_mod_cast mul_nonneg (by positivity) (fineError_pos N).le
  have hab : |(a - b) - (A - B)| ≤ 2 * δ := by
    have hh := abs_sub (a - A) (b - B)
    have ha : |a - A| ≤ δ := by
      simpa only [A, a, SeedKernelIntervals.leftAngle, abs_sub_comm] using hl
    have hb : |b - B| ≤ δ := by
      simpa only [B, b, SeedKernelIntervals.rightAngle, abs_sub_comm] using hr
    have he : (a - b) - (A - B) = (a - A) - (b - B) := by ring
    rw [he]
    linarith
  have hAB : |A - B| ≤ 2 := by
    have := abs_sub A B
    have ha := Real.abs_cos_le_one ((2 * (j : ℝ) + 1) * I.leftAngle i)
    have hb := Real.abs_cos_le_one ((2 * (j : ℝ) + 1) * I.rightAngle i)
    dsimp [A, B] at *
    linarith
  have hst : |s - t| ≤ (fineError N : ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hs.1)]
    linarith
  have hprod : |s * (a - b) - t * (A - B)| ≤
      2 * ((N : ℝ) + 1) * δ + 2 * (fineError N : ℝ) := by
    have he : s * (a - b) - t * (A - B) =
        s * ((a - b) - (A - B)) + (s - t) * (A - B) := by ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hs0]
    have h1 := mul_le_mul hab (hs.1.trans hsqrt)
      (by positivity : (0 : ℝ) ≤ s) (by positivity : (0 : ℝ) ≤ 2 * δ)
    have h2 := mul_le_mul hst hAB (abs_nonneg _) (by exact_mod_cast (fineError_pos N).le)
    nlinarith
  have hm : (1 : ℝ) ≤ 2 * (j : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) j.val
    linarith
  rw [realKernelEntry_eq_cos]
  unfold kernelEntry
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_ofNat, Rat.cast_natCast]
  change |36000 * s * (a - b) / ((2 * j.val + 1 : ℕ) : ℝ) -
    36000 * t * (A - B) / (2 * (j : ℝ) + 1)| ≤ _
  push_cast
  have hfactor : 36000 * s * (a - b) - 36000 * t * (A - B) =
      36000 * (s * (a - b) - t * (A - B)) := by ring
  rw [← sub_div, hfactor, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 36000),
    abs_of_pos (by positivity : (0 : ℝ) < 2 * (j : ℝ) + 1)]
  apply (div_le_self (by positivity) hm).trans
  apply (mul_le_mul_of_nonneg_left hprod (by norm_num)).trans
  dsimp [δ, kernelError]
  push_cast
  have hn := Nat.cast_nonneg (α := ℝ) N
  have he0 : (0 : ℝ) ≤ fineError N := by exact_mod_cast (fineError_pos N).le
  nlinarith

/-- Summing as many as N kernel-entry errors still fits the rounding budget. -/
theorem kernelError_budget (N : ℕ) : (N : ℚ) * kernelError N ≤ seedRoundingError N := by
  unfold kernelError fineError seedRoundingError
  have hd : (0 : ℚ) < (N : ℚ) + 1 := by positivity
  field_simp
  apply sub_nonneg.mp
  ring_nf
  positivity

theorem geometry_kernel_entries {d : ℕ} (G : GeometryCertificate d)
    (i : Fin (intervalCount d)) (j : Fin (seedN d)) :
    |(kernelEntry (seedN d) ((intervals (seedN d)).getD i (0, 0)) j : ℝ) -
      realKernelEntry G.kernelIntervals i j| ≤ (kernelError (seedN d) : ℝ) := by
  have hp : (intervals (seedN d)).getD i (0, 0) =
      (G.kernelIntervals.left i, G.kernelIntervals.right i) := by
    apply Prod.ext
    · exact (G.left_eq i).symm
    · exact (G.right_eq i).symm
  rw [hp]
  exact kernelEntry_error G.kernelIntervals i j

/-- Unconditional recomputation error for every geometry certificate of the
actual marked runs. It requires only signs, rather than coloring discrepancy. -/
theorem fractional_error {d : ℕ} (G : GeometryCertificate d)
    (α : Fin (intervalCount d) → ℚ) (hα : ∀ i, α i = -1 ∨ α i = 1)
    (j : Fin (seedN d)) :
    |(fractionalCoefficient (seedN d) (intervals (seedN d)) (List.ofFn α) j : ℝ) -
      fractional G.kernelIntervals α j| ≤ (seedRoundingError (seedN d) : ℝ) := by
  have hc : intervalCount d ≤ seedN d := by have := G.count; omega
  have hcr : (intervalCount d : ℝ) ≤ seedN d := by exact_mod_cast hc
  have he : (0 : ℝ) ≤ kernelError (seedN d) := by
    exact_mod_cast kernelError_nonnegative (seedN d)
  have hb : (seedN d : ℝ) * (kernelError (seedN d) : ℝ) ≤
      (seedRoundingError (seedN d) : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (kernelError_budget (seedN d))
    simpa only [Rat.cast_mul, Rat.cast_natCast] using hh
  exact (fractional_error_of_entries G.kernelIntervals α hα (geometry_kernel_entries G) j).trans
    ((mul_le_mul_of_nonneg_right hcr he).trans hb)

end
end FlatFrontend
end Power2ModuleSVP
