module

public import Power2ModuleSVP.Seed.SineKernel.Variation
import Mathlib.Tactic

/-!
# Reflected

The reflected kernel estimate. Splitting cosecant at its minimum gives two
monotone continuous weights and a constant. The constant integrates to zero
on every grid interval, including an interval crossing the minimum.

Paper: `paper/power2svp.pdf`, Appendix A.2 (Lemma 10, filling the small intervals).
-/

@[expose] public section

namespace Power2ModuleSVP

open scoped BigOperators

noncomputable section

private def seedClippedCsc (a x : ℝ) : ℝ :=
  (Real.sin (min (max x a) (Real.pi / 2)))⁻¹

private theorem seedClippedCsc_arg_mem {a : ℝ} (ha : a ≤ Real.pi / 2) (x : ℝ) :
    min (max x a) (Real.pi / 2) ∈ Set.Icc a (Real.pi / 2) :=
  ⟨le_min (le_max_right _ _) ha, min_le_right _ _⟩

private theorem seedClippedCsc_sin_pos {a : ℝ} (ha0 : 0 < a) (ha : a ≤ Real.pi / 2)
    (x : ℝ) : 0 < Real.sin (min (max x a) (Real.pi / 2)) := by
  have hx := seedClippedCsc_arg_mem ha x
  exact Real.sin_pos_of_pos_of_lt_pi (ha0.trans_le hx.1) (by linarith [hx.2, Real.pi_pos])

private theorem seedClippedCsc_continuous {a : ℝ} (ha0 : 0 < a) (ha : a ≤ Real.pi / 2) :
    Continuous (seedClippedCsc a) := by
  exact (by fun_prop : Continuous (fun x : ℝ =>
    Real.sin (min (max x a) (Real.pi / 2)))).inv₀
      (fun x => (seedClippedCsc_sin_pos ha0 ha x).ne')

private theorem seedClippedCsc_antitone {a : ℝ} (ha0 : 0 < a) (ha : a ≤ Real.pi / 2) :
    Antitone (seedClippedCsc a) := by
  intro x y hxy
  have hx := seedClippedCsc_arg_mem ha x
  have hy := seedClippedCsc_arg_mem ha y
  have hs := Real.monotoneOn_sin
    (show min (max x a) (Real.pi / 2) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
    (show min (max y a) (Real.pi / 2) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [hy.1, Real.pi_pos], hy.2⟩)
    (min_le_min (max_le_max hxy le_rfl) le_rfl)
  simpa only [seedClippedCsc, one_div] using
    one_div_le_one_div_of_le (seedClippedCsc_sin_pos ha0 ha x) hs

private theorem seedClippedCsc_bounds {a : ℝ} (ha0 : 0 < a) (ha : a ≤ Real.pi / 2)
    (x : ℝ) : 1 ≤ seedClippedCsc a x ∧ seedClippedCsc a x ≤ (Real.sin a)⁻¹ := by
  have hx := seedClippedCsc_arg_mem ha x
  have hsp := seedClippedCsc_sin_pos ha0 ha x
  have hsa := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [ha, Real.pi_pos])
  constructor
  · simpa only [seedClippedCsc, one_div, inv_one] using
      one_div_le_one_div_of_le hsp (Real.sin_le_one _)
  · have hs := Real.monotoneOn_sin
      (show a ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], ha⟩)
      (show min (max x a) (Real.pi / 2) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩) hx.1
    simpa only [seedClippedCsc, one_div] using one_div_le_one_div_of_le hsa hs

private theorem seedClippedCsc_split {a t : ℝ} (_ha : a ≤ Real.pi / 2)
    (ht : t ∈ Set.Icc a (Real.pi - a)) :
    (Real.sin t)⁻¹ = seedClippedCsc a t + seedClippedCsc a (Real.pi - t) - 1 := by
  by_cases hhalf : t ≤ Real.pi / 2
  · have hx : min (max t a) (Real.pi / 2) = t := by
      rw [max_eq_left ht.1, min_eq_left hhalf]
    have hy : min (max (Real.pi - t) a) (Real.pi / 2) = Real.pi / 2 := by
      apply min_eq_right
      exact le_max_of_le_left (by linarith)
    simp [seedClippedCsc, hx, hy]
  · have hx : min (max t a) (Real.pi / 2) = Real.pi / 2 := by
      apply min_eq_right
      exact le_max_of_le_left (by linarith)
    have hy : min (max (Real.pi - t) a) (Real.pi / 2) = Real.pi - t := by
      rw [max_eq_left (by linarith [ht.2]), min_eq_left (by linarith)]
    simp [seedClippedCsc, hx, hy, Real.sin_pi_sub]

/-- The reflected kernel costs at most `2/(N sin(100 pi/N))`. The exact
minimum split avoids an additional exception for a crossing interval. -/
theorem sine_kernel_reflected_sum_bound {N J : ℕ} (hN : 2 ^ 20 ≤ N)
    (I : SeedKernelIntervals N J) (α : Fin J → ℝ) (hα : ∀ i, |α i| ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |∑ i, α i * ∫ u in I.leftAngle i..I.rightAngle i,
      oddCosineKernel N (u + θ)| ≤
        2 / ((N : ℝ) * Real.sin (100 * Real.pi / N)) := by
  have hNp : 0 < N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast hNp
  have hlarge : (1048576 : ℝ) ≤ N := by exact_mod_cast hN
  let a : ℝ := 100 * Real.pi / N
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha : a ≤ Real.pi / 2 := by
    dsimp [a]
    apply (div_le_iff₀ hn).2
    nlinarith [Real.pi_pos]
  let gL : ℝ → ℝ := fun u => -seedClippedCsc a (u + θ)
  let gR : ℝ → ℝ := fun u => seedClippedCsc a (Real.pi - (u + θ))
  let φ : ℝ := 2 * (N : ℝ) * θ
  have hc := seedClippedCsc_continuous ha0 ha
  have hm := seedClippedCsc_antitone ha0 ha
  have hgcL : Continuous gL := hc.comp (by fun_prop) |>.neg
  have hgcR : Continuous gR := hc.comp (by fun_prop)
  have hgmL : Monotone gL := by
    intro u v huv
    exact neg_le_neg (hm (by linarith : u + θ ≤ v + θ))
  have hgmR : Monotone gR := by
    intro u v huv
    exact hm (by linarith : Real.pi - (v + θ) ≤ Real.pi - (u + θ))
  let M : ℕ := N / 2
  have hright (i : Fin J) : I.right i ≤ M := by
    have := I.right_clearance i
    dsimp [M]
    omega
  have hsep (i j : Fin J) (hij : i ≠ j) : I.right i ≤ I.left j ∨ I.right j ≤ I.left i :=
    (I.separated i j hij).imp (fun h => by omega) (fun h => by omega)
  have hbL := grid_sine_sum_le_monotone_variation hNp I.left I.right
    (fun i => (I.width_pos i).le) hright hsep gL φ α hα
    hgcL.continuousOn (hgmL.monotoneOn _)
  have hbR := grid_sine_sum_le_monotone_variation hNp I.left I.right
    (fun i => (I.width_pos i).le) hright hsep gR φ α hα
    hgcR.continuousOn (hgmR.monotoneOn _)
  have harg (i : Fin J) {u : ℝ} (hu : u ∈ Set.Icc (I.leftAngle i) (I.rightAngle i)) :
      u + θ ∈ Set.Icc a (Real.pi - a) := by
    have hl : a ≤ I.leftAngle i := by
      dsimp [a, SeedKernelIntervals.leftAngle]
      apply div_le_div_of_nonneg_right _ hn.le
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast I.left_clearance i) Real.pi_pos.le
    have hr : I.rightAngle i ≤ Real.pi / 2 - a := by
      have hi : (2 : ℝ) * (I.right i + 100) ≤ N := by exact_mod_cast I.right_clearance i
      dsimp [a, SeedKernelIntervals.rightAngle]
      apply (le_sub_iff_add_le).2
      rw [← add_div, ← add_mul]
      apply (div_le_iff₀ hn).2
      nlinarith [mul_le_mul_of_nonneg_right hi Real.pi_pos.le]
    constructor <;> linarith [hu.1, hu.2, hθ.1, hθ.2]
  have hsin : Continuous (fun u : ℝ => Real.sin (2 * (N : ℝ) * u + φ)) := by fun_prop
  have heq (i : Fin J) :
      (∫ u in I.leftAngle i..I.rightAngle i, oddCosineKernel N (u + θ)) =
      -(∫ u in I.leftAngle i..I.rightAngle i, gL u * Real.sin (2 * (N : ℝ) * u + φ)) +
        ∫ u in I.leftAngle i..I.rightAngle i, gR u * Real.sin (2 * (N : ℝ) * u + φ) := by
    have horder : I.leftAngle i ≤ I.rightAngle i := by
      dsimp [SeedKernelIntervals.leftAngle, SeedKernelIntervals.rightAngle]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by exact_mod_cast (I.width_pos i).le) Real.pi_pos.le) hn.le
    have hzero : (∫ u in I.leftAngle i..I.rightAngle i,
        Real.sin (2 * (N : ℝ) * u + φ)) = 0 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => gridSinePrimitive_hasDerivAt hNp φ u) (hsin.intervalIntegrable _ _)]
      simp [SeedKernelIntervals.leftAngle, SeedKernelIntervals.rightAngle,
        gridSinePrimitive_grid hNp]
    calc
      _ = ∫ u in I.leftAngle i..I.rightAngle i,
          (-gL u + gR u - 1) * Real.sin (2 * (N : ℝ) * u + φ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le horder] at hu
        have ht := harg i hu
        have hsp := Real.sin_pos_of_pos_of_lt_pi (ha0.trans_le ht.1) (by linarith [ht.2])
        change oddCosineKernel N (u + θ) =
          (-gL u + gR u - 1) * Real.sin (2 * (N : ℝ) * u + φ)
        rw [oddCosineKernel_eq_div N hsp.ne', div_eq_mul_inv, seedClippedCsc_split ha ht]
        dsimp [gL, gR, φ]
        rw [show 2 * (N : ℝ) * (u + θ) = 2 * (N : ℝ) * u + 2 * N * θ by ring]
        ring
      _ = _ := by
        simp_rw [sub_mul, add_mul, neg_mul, one_mul]
        have hd := intervalIntegral.integral_sub (μ := MeasureTheory.volume)
          (((hgcL.mul hsin).neg.add (hgcR.mul hsin)).intervalIntegrable
            (I.leftAngle i) (I.rightAngle i))
          (hsin.intervalIntegrable (I.leftAngle i) (I.rightAngle i))
        have ha' := intervalIntegral.integral_add (μ := MeasureTheory.volume)
          ((hgcL.mul hsin).neg.intervalIntegrable (I.leftAngle i) (I.rightAngle i))
          ((hgcR.mul hsin).intervalIntegrable (I.leftAngle i) (I.rightAngle i))
        simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply] at hd ha'
        rw [hd, ha', intervalIntegral.integral_neg, hzero, sub_zero]
  have hsum : (∑ i, α i * ∫ u in I.leftAngle i..I.rightAngle i,
      oddCosineKernel N (u + θ)) =
      -(∑ i, α i * ∫ u in I.leftAngle i..I.rightAngle i,
        gL u * Real.sin (2 * (N : ℝ) * u + φ)) +
      ∑ i, α i * ∫ u in I.leftAngle i..I.rightAngle i,
        gR u * Real.sin (2 * (N : ℝ) * u + φ) := by
    simp_rw [heq, mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [hsum]
  have hV : (gL (M * Real.pi / N) - gL 0) +
      (gR (M * Real.pi / N) - gR 0) ≤ 2 * (Real.sin a)⁻¹ := by
    have hL0 := seedClippedCsc_bounds ha0 ha (0 + θ)
    have hL1 := seedClippedCsc_bounds ha0 ha (M * Real.pi / N + θ)
    have hR0 := seedClippedCsc_bounds ha0 ha (Real.pi - (0 + θ))
    have hR1 := seedClippedCsc_bounds ha0 ha (Real.pi - (M * Real.pi / N + θ))
    dsimp [gL, gR]
    linarith [hL0.2, hL1.1, hR0.1, hR1.2]
  calc
    _ ≤ |-(∑ i, α i * ∫ u in I.leftAngle i..I.rightAngle i,
        gL u * Real.sin (2 * (N : ℝ) * u + φ))| +
        |∑ i, α i * ∫ u in I.leftAngle i..I.rightAngle i,
          gR u * Real.sin (2 * (N : ℝ) * u + φ)| := abs_add_le _ _
    _ ≤ (gL (M * Real.pi / N) - gL 0) / N +
        (gR (M * Real.pi / N) - gR 0) / N := by
      rw [abs_neg]
      exact add_le_add hbL hbR
    _ ≤ (2 * (Real.sin a)⁻¹) / N := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hV hn.le
    _ = _ := by dsimp [a]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

end

end Power2ModuleSVP
