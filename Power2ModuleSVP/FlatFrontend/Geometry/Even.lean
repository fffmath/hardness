import Power2ModuleSVP.FlatFrontend.Geometry.Blocks

/-!
# Even

Identification and unconditional estimate of the even sine part.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators
noncomputable section

/-- The unit-circle point with argument twice the given angle. -/
def seedCircle (θ : ℝ) : ℂ := Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)

theorem seedCircle_norm (θ : ℝ) : ‖seedCircle θ‖ = 1 := by
  simp [seedCircle, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem seedCircle_pow (θ : ℝ) (j : ℕ) :
    seedCircle θ ^ j = Complex.exp ((((2 * (j : ℝ) * θ) : ℝ) : ℂ) * Complex.I) := by
  rw [seedCircle, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem seedCircle_pow_re (θ : ℝ) (j : ℕ) :
    (seedCircle θ ^ j).re = Real.cos (2 * (j : ℝ) * θ) := by
  rw [seedCircle_pow, Complex.exp_ofReal_mul_I_re]

theorem seedCircle_pow_im (θ : ℝ) (j : ℕ) :
    (seedCircle θ ^ j).im = Real.sin (2 * (j : ℝ) * θ) := by
  rw [seedCircle_pow, Complex.exp_ofReal_mul_I_im]

theorem evenPart_eq_rudinShapiro {d : ℕ} (hd : d = 4 * seedN d + 4)
    (hfit : 2 * blockShift (seedN d) + 2 ^ stage (seedN d) ≤ seedN d + 1)
    (θ : ℝ) :
    evenPart d θ = rudinShapiroEvenSinePart (stage (seedN d))
      (blockShift (seedN d)) (seedN d) (seedCircle θ) := by
  have hs : (∑ j ∈ Finset.range (seedN d + 1),
      (if cosineSelected (seedN d) j then (0 : ℂ)
        else (rudinShapiroCoefficient j : ℂ)) * seedCircle θ ^ j) =
      rudinShapiroPrefix (seedN d + 1) (seedCircle θ) -
        (seedCircle θ ^ blockShift (seedN d) *
            rsEval (rudinShapiroP (stage (seedN d))) (seedCircle θ) +
        seedCircle θ ^ (2 * blockShift (seedN d)) *
            rsEval (rudinShapiroP (stage (seedN d))) (seedCircle θ)) := by
    rw [← removed_block_evaluation hfit, rudinShapiroPrefix, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hh := congrArg Complex.im hs
  rw [evenPart_eq_sum hd]
  unfold rudinShapiroEvenSinePart
  rw [sub_sub]
  rw [← hh, Finset.sum_range_succ']
  have hzero : ¬ cosineSelected (seedN d) 0 = true := by
    rw [cosineSelected_iff]
    have := (block_parameters (seedN d)).1
    omega
  simp only [hzero, Bool.false_eq_true, ↓reduceIte, pow_zero, mul_one, Complex.add_im,
    Complex.intCast_im, add_zero, Complex.im_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · simp
  · simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero,
      seedCircle_pow_im, Nat.cast_add, Nat.cast_one]
    congr 2; ring

theorem evenPart_bound_of_parameters {d : ℕ} (hd : d = 4 * seedN d + 4)
    (hN : stageWidth 1 * 2 ^ 66 ≤ seedN d) (θ : ℝ) :
    |evenPart d θ| ≤ 6 * Real.sqrt (seedN d) := by
  have hp := even_bound_parameters hN
  have hfit : 2 * blockShift (seedN d) + 2 ^ stage (seedN d) ≤ seedN d + 1 := by
    have := block_fits hN
    have := (block_parameters (seedN d)).1
    omega
  rw [evenPart_eq_rudinShapiro hd hfit]
  exact (rudinShapiroEvenSinePart_bound (seedCircle_norm θ) hp.1 hp.2).le

set_option exponentiation.threshold 1024 in
theorem evenPart_bound {d : ℕ} (hd : Dyadic d) (hlarge : 2 ^ 512 ≤ d) (θ : ℝ) :
    |evenPart d θ| ≤ 6 * Real.sqrt (seedN d) := by
  apply evenPart_bound_of_parameters (dyadic_shape hd (by norm_num at hlarge ⊢; omega))
  have h := stage_admissible_at_cutoff hlarge
  have hs : stageWidth 1 ≤ stageWidth (stage (seedN d)) := by
    have hp : 2 ^ 1 ≤ 2 ^ stage (seedN d) :=
      Nat.pow_le_pow_right (by omega) (stage_positive _)
    have hq : 2 ^ (1 + 11) ≤ 2 ^ (stage (seedN d) + 11) :=
      Nat.pow_le_pow_right (by omega) (by have := stage_positive (seedN d); omega)
    unfold stageWidth
    omega
  exact (Nat.mul_le_mul_right (2 ^ 66) hs).trans h

end
end FlatFrontend
end Power2ModuleSVP
