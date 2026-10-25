import Power2ModuleSVP.FlatFrontend.Geometry.Even

/-!
# Cosine

Exact analytic and polynomial interpretations of the cosine scan.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators
noncomputable section

theorem cosine_eq_rudinShapiro {d : ℕ} (hd : d = 4 * seedN d + 4)
    (hfit : 2 * blockShift (seedN d) + 2 ^ stage (seedN d) ≤ seedN d + 1)
    (θ : ℝ) :
    cosine d θ = rudinShapiroCosinePart (stage (seedN d))
      (blockShift (seedN d)) (seedCircle θ) := by
  unfold rudinShapiroCosinePart
  rw [← cosine_block_evaluation (N := seedN d) hfit, Finset.sum_range_succ', Complex.add_re, Complex.re_sum]
  have hzero : cosineCoefficient (seedN d) 0 = 0 := by
    apply cosineCoefficient_unselected (N := seedN d)
    have := (block_parameters (seedN d)).1
    simp only [cosineSelected, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
  simp only [hzero, Int.cast_zero, zero_mul, Complex.zero_re, add_zero]
  rw [cosine_eq_sum hd]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
    sub_zero, seedCircle_pow_re, Nat.cast_add, Nat.cast_one]
  rw [show 2 * ((j : ℝ) + 1) * θ = (2 * (j : ℝ) + 2) * θ by ring]

theorem cosine_eq_polynomial {d : ℕ} (hd : d = 4 * seedN d + 4) (θ : ℝ) :
    cosine d θ = ((cosinePolynomial (seedN d)).map (Int.castRingHom ℝ)).eval (Real.cos θ) := by
  rw [cosine_eq_sum hd]
  simp only [cosinePolynomial, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.Chebyshev.map_T, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.Chebyshev.T_real_cos,
    Int.coe_castRingHom]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  congr 2; ring

/-- Reduction to `cos(2θ)` removes the spurious factor two in the degree
used for the sharp interval count. -/
def reducedCosinePolynomial (N : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range N, Polynomial.C (cosineCoefficient N (j + 1)) *
    Polynomial.Chebyshev.T ℤ (j + 1)

theorem cosine_eq_reducedPolynomial {d : ℕ} (hd : d = 4 * seedN d + 4) (θ : ℝ) :
    cosine d θ = ((reducedCosinePolynomial (seedN d)).map (Int.castRingHom ℝ)).eval
      (Real.cos (2 * θ)) := by
  rw [cosine_eq_sum hd]
  simp only [reducedCosinePolynomial, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.Chebyshev.map_T, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.Chebyshev.T_real_cos,
    Int.coe_castRingHom]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  congr 2; ring

theorem cosine_eq_wave {d : ℕ} (hd : d = 4 * seedN d + 4)
    (hfit : 2 * blockShift (seedN d) + 2 ^ stage (seedN d) ≤ seedN d + 1)
    (θ : ℝ) :
    cosine d θ = Real.sqrt ((2 : ℝ) ^ (stage (seedN d) + 1)) *
      rudinShapiroWave (stage (seedN d)) 0 (2 * blockShift (seedN d) * θ) := by
  rw [cosine_eq_rudinShapiro hd hfit, rudinShapiroWave_zero]
  have hphase (r : ℕ) : seedWavePhase r (2 * blockShift (seedN d) * θ) =
      seedCircle θ ^ (r * blockShift (seedN d)) := by
    rw [seedCircle_pow]
    unfold seedWavePhase
    congr 1
    push_cast
    ring
  have harg : (1 / (2 : ℝ) ^ (stage (seedN d) + 10)) *
      (2 * blockShift (seedN d) * θ) = 2 * θ := by
    simp only [blockShift, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have hp1 := hphase 1
  have hp2 := hphase 2
  norm_num only [Nat.cast_one, Nat.one_mul] at hp1
  norm_num only [Nat.cast_ofNat] at hp2
  rw [hp1, hp2, harg]
  change _ = Real.sqrt ((2 : ℝ) ^ (stage (seedN d) + 1)) *
    (rudinShapiroCosinePart (stage (seedN d)) (blockShift (seedN d)) (seedCircle θ) /
      Real.sqrt ((2 : ℝ) ^ (stage (seedN d) + 1)))
  rw [mul_div_cancel₀ _ (by positivity)]

end
end FlatFrontend
end Power2ModuleSVP
