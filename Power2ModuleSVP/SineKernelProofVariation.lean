module

public import Power2ModuleSVP.SineKernelProofAux
public import Power2ModuleSVP.SineKernelProofCorrection
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.Tactic

/-!
Monotone-weight estimates without differentiability at the origin. The
second mean value theorem supplies the same grid bound as integration by
parts. Disjoint integer grid ranges then sum their variations exactly.
-/

@[expose] public section
namespace Power2ModuleSVP
open scoped BigOperators
noncomputable section

/-- A monotone continuous weight needs no differentiability assumption for
the endpoint-phase estimate. -/
theorem grid_sine_integral_le_monotone_variation {N : ℕ} (hN : 0 < N)
    {g : ℝ → ℝ} (φ : ℝ) (a b : ℕ) (hab : a ≤ b)
    (hgc : ContinuousOn g (Set.uIcc (a * Real.pi / N) (b * Real.pi / N)))
    (hgm : MonotoneOn g (Set.Icc (a * Real.pi / N) (b * Real.pi / N))) :
    |∫ u in (a * Real.pi / N)..(b * Real.pi / N),
      g u * Real.sin (2 * (N : ℝ) * u + φ)| ≤
      (g (b * Real.pi / N) - g (a * Real.pi / N)) / N := by
  let A : ℝ := a * Real.pi / N
  let B : ℝ := b * Real.pi / N
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hAB : A ≤ B := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) Real.pi_pos.le) hn.le
  have hsin : Continuous (fun u : ℝ => Real.sin (2 * (N : ℝ) * u + φ)) := by fun_prop
  have hfull : (∫ u in A..B, Real.sin (2 * (N : ℝ) * u + φ)) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => gridSinePrimitive_hasDerivAt hN φ u) (hsin.intervalIntegrable A B)]
    simp [A, B, gridSinePrimitive_grid hN]
  obtain ⟨ξ, hξ, heq⟩ :=
    exists_eq_const_mul_intervalIntegral_of_nonneg_of_monotoneOn
      (f := fun u => g u - g A) hAB (by simp)
      (fun x hx y hy hxy => sub_le_sub_right (hgm hx hy hxy) _)
      (hsin.intervalIntegrable A B)
  have htail : |∫ u in ξ..B, Real.sin (2 * (N : ℝ) * u + φ)| ≤ 1 / (N : ℝ) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => gridSinePrimitive_hasDerivAt hN φ u) (hsin.intervalIntegrable ξ B)]
    simp only [B, gridSinePrimitive_grid hN, zero_sub, abs_neg]
    exact gridSinePrimitive_abs_le hN φ ξ
  have hgi : IntervalIntegrable g MeasureTheory.volume A B :=
    hgc.intervalIntegrable
  have hexpand : (∫ u in A..B,
      (g u - g A) * Real.sin (2 * (N : ℝ) * u + φ)) =
      ∫ u in A..B, g u * Real.sin (2 * (N : ℝ) * u + φ) := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub
      (hgi.mul_continuousOn hsin.continuousOn)
      ((hsin.intervalIntegrable A B).const_mul (g A)),
      intervalIntegral.integral_const_mul, hfull, mul_zero, sub_zero]
  rw [hexpand] at heq
  rw [heq, abs_mul, abs_of_nonneg (sub_nonneg.mpr (hgm ⟨le_rfl, hAB⟩ ⟨hAB, le_rfl⟩ hAB))]
  simpa only [A, B, div_eq_mul_inv, one_div, one_mul] using
    mul_le_mul_of_nonneg_left htail
      (sub_nonneg.mpr (hgm ⟨le_rfl, hAB⟩ ⟨hAB, le_rfl⟩ hAB))

/-- Disjoint integer grid intervals consume at most the full variation of
a monotone grid function. No ordering of the interval indices is assumed. -/
theorem disjoint_grid_variation_sum {J M : ℕ} (left right : Fin J → ℕ)
    (hw : ∀ i, left i ≤ right i) (hr : ∀ i, right i ≤ M)
    (hsep : ∀ i j, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (f : ℕ → ℝ) (hf : MonotoneOn f (Set.Icc 0 M)) :
    (∑ i, (f (right i) - f (left i))) ≤ f M - f 0 := by
  classical
  have htel (a b : ℕ) (hab : a ≤ b) :
      (∑ j ∈ Finset.Ico a b, (f (j + 1) - f j)) = f b - f a := by
    rw [Finset.sum_Ico_eq_sub _ hab, Finset.sum_range_sub, Finset.sum_range_sub]
    ring
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin J)))
      (fun i => Finset.Ico (left i) (right i)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro n hni hnj
    have hi' := Finset.mem_Ico.mp hni
    have hj' := Finset.mem_Ico.mp hnj
    rcases hsep i j hij with h | h <;> omega
  have hsub : (Finset.univ.biUnion (fun i => Finset.Ico (left i) (right i))) ⊆
      Finset.range M := by
    intro n hn
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hn
    have := Finset.mem_Ico.mp hi
    exact Finset.mem_range.mpr (by have := hr i; omega)
  calc
    _ = ∑ i : Fin J, ∑ j ∈ Finset.Ico (left i) (right i), (f (j + 1) - f j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (htel _ _ (hw i)).symm
    _ = ∑ j ∈ Finset.univ.biUnion (fun i => Finset.Ico (left i) (right i)),
        (f (j + 1) - f j) := (Finset.sum_biUnion hd).symm
    _ ≤ ∑ j ∈ Finset.range M, (f (j + 1) - f j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro j hj hnot
      have hj' := Finset.mem_range.mp hj
      exact sub_nonneg.mpr (hf ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩
        (Nat.le_succ j))
    _ = f M - f 0 := Finset.sum_range_sub f M

/-- Simultaneous monotone-weight control on any disjoint grid family. -/
theorem grid_sine_sum_le_monotone_variation {N J M : ℕ} (hN : 0 < N)
    (left right : Fin J → ℕ) (hw : ∀ i, left i ≤ right i) (hr : ∀ i, right i ≤ M)
    (hsep : ∀ i j, i ≠ j → right i ≤ left j ∨ right j ≤ left i)
    (g : ℝ → ℝ) (φ : ℝ) (α : Fin J → ℝ) (hα : ∀ i, |α i| ≤ 1)
    (hgc : ContinuousOn g (Set.uIcc 0 (M * Real.pi / N)))
    (hgm : MonotoneOn g (Set.Icc 0 (M * Real.pi / N))) :
    |∑ i, α i * ∫ u in (left i * Real.pi / N)..(right i * Real.pi / N),
      g u * Real.sin (2 * (N : ℝ) * u + φ)| ≤
      (g (M * Real.pi / N) - g 0) / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hangle : Monotone (fun n : ℕ => (n : ℝ) * Real.pi / N) := by
    intro a b hab
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) Real.pi_pos.le) hn.le
  have hb (i : Fin J) :
      Set.uIcc (left i * Real.pi / N) (right i * Real.pi / N) ⊆
        Set.uIcc 0 (M * Real.pi / N) := by
    rw [Set.uIcc_of_le (hangle (hw i)), Set.uIcc_of_le (by positivity)]
    exact Set.Icc_subset_Icc (by positivity) (hangle (hr i))
  have hweight (i : Fin J) := grid_sine_integral_le_monotone_variation hN φ
    (left i) (right i) (hw i) (hgc.mono (hb i))
    (hgm.mono (by
      simpa only [Set.uIcc_of_le (hangle (hw i)),
        Set.uIcc_of_le (show (0 : ℝ) ≤ M * Real.pi / N by positivity)] using hb i))
  have hgrid : MonotoneOn (fun n : ℕ => g (n * Real.pi / N)) (Set.Icc 0 M) := by
    intro a ha b hb hab
    apply hgm ⟨by positivity, hangle ha.2⟩ ⟨by positivity, hangle hb.2⟩ (hangle hab)
  have hv := disjoint_grid_variation_sum left right hw hr hsep _ hgrid
  calc
    _ ≤ ∑ i, |α i * ∫ u in (left i * Real.pi / N)..(right i * Real.pi / N),
        g u * Real.sin (2 * (N : ℝ) * u + φ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (g (right i * Real.pi / N) - g (left i * Real.pi / N)) / N := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hα i) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hweight i)
    _ = (∑ i, (g (right i * Real.pi / N) - g (left i * Real.pi / N))) / N := by
      rw [Finset.sum_div]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hn.le
      simpa using hv

/-- The complete cosecant correction, summed over every interval, costs at
most `(2 - 4/pi)/N`, including intervals containing the observation point. -/
theorem sine_kernel_correction_sum_bound {N J : ℕ} (hN : 0 < N)
    (I : SeedKernelIntervals N J) (α : Fin J → ℝ) (hα : ∀ i, |α i| ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |∑ i, α i * ∫ u in I.leftAngle i..I.rightAngle i,
      seedCscCorrection (u - θ) * Real.sin (2 * (N : ℝ) * (u - θ))| ≤
      (2 - 4 / Real.pi) / N := by
  let M : ℕ := N / 2
  let g : ℝ → ℝ := fun u => seedCscCorrection (u - θ)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hM : 2 * (M : ℝ) ≤ N := by exact_mod_cast (show 2 * M ≤ N by dsimp [M]; omega)
  have hangle : (M : ℝ) * Real.pi / N ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hn).2
    nlinarith [mul_le_mul_of_nonneg_right hM Real.pi_pos.le]
  have hdom {u : ℝ} (hu : u ∈ Set.Icc 0 (M * Real.pi / N)) :
      u - θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hu.1, hu.2, hθ.1, hθ.2]
  have hgc : ContinuousOn g (Set.uIcc 0 (M * Real.pi / N)) := by
    rw [Set.uIcc_of_le (by positivity)]
    exact seedCscCorrection_continuousOn.comp
      (by fun_prop) (fun u hu => hdom hu)
  have hgm : MonotoneOn g (Set.Icc 0 (M * Real.pi / N)) := by
    intro u hu v hv huv
    exact seedCscCorrection_monotoneOn (hdom hu) (hdom hv) (by linarith)
  have hright (i : Fin J) : I.right i ≤ M := by
    have := I.right_clearance i
    dsimp [M]
    omega
  have hb := grid_sine_sum_le_monotone_variation hN I.left I.right
    (fun i => (I.width_pos i).le) hright
    (fun i j hij => (I.separated i j hij).imp (fun h => by omega) (fun h => by omega))
    g (-2 * N * θ) α hα hgc hgm
  have heq : (∑ i, α i * ∫ u in I.leftAngle i..I.rightAngle i,
      seedCscCorrection (u - θ) * Real.sin (2 * (N : ℝ) * (u - θ))) =
      ∑ i, α i * ∫ u in (I.left i * Real.pi / N)..(I.right i * Real.pi / N),
        g u * Real.sin (2 * (N : ℝ) * u + -2 * N * θ) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp [g]
    congr 2
    ring
  rw [heq]
  apply hb.trans
  apply div_le_div_of_nonneg_right _ hn.le
  have hu := seedCscCorrection_monotoneOn
    (hdom (show M * Real.pi / N ∈ Set.Icc (0 : ℝ) (M * Real.pi / N) from
      ⟨by positivity, le_rfl⟩))
    (show Real.pi / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], le_rfl⟩) (by linarith [hθ.1])
  have hl := seedCscCorrection_monotoneOn
    (show -(Real.pi / 2) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨le_rfl, by linarith [Real.pi_pos]⟩)
    (hdom (show (0 : ℝ) ∈ Set.Icc 0 (M * Real.pi / N) from ⟨le_rfl, by positivity⟩))
    (by linarith [hθ.2])
  simp only [g, zero_sub, seedCscCorrection_neg, seedCscCorrection_pi_div_two] at *
  nlinarith [show 4 / Real.pi = 2 * (2 / Real.pi) by ring]

end
end Power2ModuleSVP
