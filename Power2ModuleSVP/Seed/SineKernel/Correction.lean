module

public import Power2ModuleSVP.Seed.SineKernel.EndpointPhase
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic

/-!
# Correction

The cosecant correction in `lem:sine-kernel`, with its continuous value at
zero. The derivative comparison and the exact variation are unconditional.

Paper: `paper/power2svp.pdf`, Appendix A.2 (Lemma 10, filling the small intervals).
-/

@[expose] public section

namespace Power2ModuleSVP

open scoped Topology

noncomputable section

/-- Cosecant minus its singular leading term, continued at zero. -/
def seedCscCorrection (x : ℝ) : ℝ :=
  if x = 0 then 0 else (Real.sin x)⁻¹ - x⁻¹

@[simp] theorem seedCscCorrection_zero : seedCscCorrection 0 = 0 := by
  simp [seedCscCorrection]

theorem seedCscCorrection_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    seedCscCorrection x = (Real.sin x)⁻¹ - x⁻¹ := by
  simp [seedCscCorrection, hx]

@[simp] theorem seedCscCorrection_neg (x : ℝ) :
    seedCscCorrection (-x) = -seedCscCorrection x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [seedCscCorrection, hx, Real.sin_neg]
    ring

private theorem seed_sin_half_le {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    x / 2 ≤ Real.sin x := by
  have hfrac : (1 : ℝ) / 2 ≤ 2 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    linarith [Real.pi_lt_four]
  have hj := Real.mul_le_sin hx.1 hx.2
  have hm := mul_le_mul_of_nonneg_right hfrac hx.1
  nlinarith

/-- The elementary derivative comparison for the correction. -/
theorem seed_sin_sq_ge_sq_mul_cos {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    x ^ 2 * Real.cos x ≤ Real.sin x ^ 2 := by
  let F : ℝ → ℝ := fun v => Real.sin v ^ 2 - v ^ 2 * Real.cos v
  let F' : ℝ → ℝ := fun v =>
    v ^ 2 * Real.sin v - 2 * (v - Real.sin v) * Real.cos v
  have hd (v : ℝ) : HasDerivAt F (F' v) v := by
    change HasDerivAt (fun v : ℝ => Real.sin v ^ 2 - v ^ 2 * Real.cos v) _ v
    have h := ((Real.hasDerivAt_sin v).pow 2).sub
      (((hasDerivAt_id v).pow 2).mul (Real.hasDerivAt_cos v))
    convert h using 1
    · ext u
      simp
    · norm_num [F', id_eq]
      ring
  have hnonneg (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : 0 ≤ F' v := by
    have hhalf := seed_sin_half_le hv
    have hs_le := Real.sin_le hv.1
    have hs_low := Real.sin_ge_sub_cube hv.1
    have hdiff : 0 ≤ v - Real.sin v := by linarith
    have hprod : (v - Real.sin v) * Real.cos v ≤ v ^ 3 / 6 := by
      calc
        _ ≤ (v - Real.sin v) * 1 :=
          mul_le_mul_of_nonneg_left (Real.cos_le_one v) hdiff
        _ ≤ _ := by linarith
    have hmain := mul_le_mul_of_nonneg_left hhalf (sq_nonneg v)
    dsimp [F']
    nlinarith [pow_nonneg hv.1 3]
  have hm : MonotoneOn F (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (by dsimp [F]; fun_prop)
      (fun v _ => (hd v).hasDerivWithinAt)
    intro v hv
    exact hnonneg v (interior_subset hv)
  have h := hm (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from
    ⟨le_rfl, Real.pi_div_two_pos.le⟩) hx hx.1
  dsimp [F] at h
  simp only [Real.sin_zero, Real.cos_zero, zero_pow (by decide : 2 ≠ 0),
    zero_mul, sub_zero] at h
  linarith

private theorem seedCscCorrection_nonneg_le {x : ℝ}
    (hx : x ∈ Set.Ioc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ seedCscCorrection x ∧ seedCscCorrection x ≤ x / 3 := by
  have hspos := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])
  have hs := seed_sin_half_le ⟨hx.1.le, hx.2⟩
  have hs_le := Real.sin_le hx.1.le
  have hs_low := Real.sin_ge_sub_cube hx.1.le
  have hden : 0 < x * Real.sin x := mul_pos hx.1 hspos
  have hcorr : seedCscCorrection x = (x - Real.sin x) / (x * Real.sin x) := by
    rw [seedCscCorrection_of_ne_zero hx.1.ne']
    field_simp [hx.1.ne', hspos.ne']
  rw [hcorr]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hs_le) hden.le
  · apply (div_le_iff₀ hden).2
    have hprod := mul_le_mul_of_nonneg_left hs (sq_nonneg x)
    nlinarith

/-- A local linear bound proves removability without a Laurent expansion. -/
theorem seedCscCorrection_abs_le {x : ℝ} (hx : |x| ≤ Real.pi / 2) :
    |seedCscCorrection x| ≤ |x| / 3 := by
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · have habs : |-x| ≤ Real.pi / 2 := by simpa using hx
    have h := seedCscCorrection_nonneg_le
      (x := -x) ⟨neg_pos.mpr hneg, by rwa [abs_of_pos (neg_pos.mpr hneg)] at habs⟩
    have hnonpos : seedCscCorrection x ≤ 0 := by
      simpa only [seedCscCorrection_neg, neg_nonneg] using h.1
    rw [abs_of_nonpos hnonpos, abs_of_neg hneg]
    simpa only [seedCscCorrection_neg] using h.2
  · simp
  · have h := seedCscCorrection_nonneg_le
      (x := x) ⟨hpos, by rwa [abs_of_pos hpos] at hx⟩
    rw [abs_of_nonneg h.1, abs_of_pos hpos]
    exact h.2

theorem seedCscCorrection_continuousAt_zero : ContinuousAt seedCscCorrection 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min (Real.pi / 2) ε, lt_min Real.pi_div_two_pos hε, ?_⟩
  intro x hx
  have hx' : |x| < min (Real.pi / 2) ε := by simpa [Real.dist_eq] using hx
  have hb := seedCscCorrection_abs_le ((lt_min_iff.mp hx').1.le)
  simp only [seedCscCorrection_zero, Real.dist_eq, sub_zero]
  have hxε := (lt_min_iff.mp hx').2
  linarith [abs_nonneg x]

private theorem seedCscCorrection_eventuallyEq {x : ℝ} (hx : x ≠ 0) :
    seedCscCorrection =ᶠ[𝓝 x] (fun v => (Real.sin v)⁻¹ - v⁻¹) := by
  filter_upwards [eventually_ne_nhds hx] with v hv
  exact seedCscCorrection_of_ne_zero hv

theorem seedCscCorrection_continuousAt {x : ℝ}
    (hx : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ContinuousAt seedCscCorrection x := by
  by_cases hx0 : x = 0
  · simpa [hx0] using seedCscCorrection_continuousAt_zero
  · have hs : Real.sin x ≠ 0 := by
      exact fun h => hx0 ((Real.sin_eq_zero_iff_of_lt_of_lt
        (by linarith [hx.1, Real.pi_pos]) (by linarith [hx.2, Real.pi_pos])).1 h)
    exact ((Real.continuous_sin.continuousAt.inv₀ hs).sub
      (continuousAt_id.inv₀ hx0)).congr_of_eventuallyEq
        (seedCscCorrection_eventuallyEq hx0)

theorem seedCscCorrection_continuousOn :
    ContinuousOn seedCscCorrection (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
  fun _ hx => (seedCscCorrection_continuousAt hx).continuousWithinAt

theorem seedCscCorrection_hasDerivAt {x : ℝ} (hx : x ≠ 0)
    (hs : Real.sin x ≠ 0) :
    HasDerivAt seedCscCorrection (1 / x ^ 2 - Real.cos x / Real.sin x ^ 2) x := by
  have h := (((Real.hasDerivAt_sin x).inv hs).sub
    ((hasDerivAt_id x).inv hx)).congr_of_eventuallyEq
      (seedCscCorrection_eventuallyEq hx)
  simp only [id_eq] at h
  convert h using 1
  ring

private theorem seedCscCorrection_monotoneOn_nonneg :
    MonotoneOn seedCscCorrection (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (seedCscCorrection_continuousOn.mono (by
      intro x hx
      exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩))
  · intro x hx
    rw [interior_Icc] at hx
    have hs := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])
    exact (seedCscCorrection_hasDerivAt hx.1.ne' hs.ne').hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hs := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])
    have hsq := seed_sin_sq_ge_sq_mul_cos ⟨hx.1.le, hx.2.le⟩
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos hx.1)).2
    nlinarith

/-- Monotonicity on the whole interval, including the corrected origin. -/
theorem seedCscCorrection_monotoneOn :
    MonotoneOn seedCscCorrection (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
  intro x hx y hy hxy
  by_cases hx0 : 0 ≤ x
  · exact seedCscCorrection_monotoneOn_nonneg ⟨hx0, hx.2⟩ ⟨by linarith, hy.2⟩ hxy
  · by_cases hy0 : y ≤ 0
    · have h := seedCscCorrection_monotoneOn_nonneg
        (a := -y) (b := -x) ⟨by linarith, by linarith [hy.1]⟩
        ⟨by linarith, by linarith [hx.1]⟩ (by linarith)
      simp only [seedCscCorrection_neg] at h
      linarith
    · have hz : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨le_rfl, Real.pi_div_two_pos.le⟩
      have ha := seedCscCorrection_monotoneOn_nonneg hz
        (show -x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from ⟨by linarith, by linarith [hx.1]⟩)
        (by linarith)
      have hb := seedCscCorrection_monotoneOn_nonneg hz
        (show y ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from ⟨by linarith, hy.2⟩) (by linarith)
      simp only [seedCscCorrection_zero, seedCscCorrection_neg] at ha hb
      linarith

@[simp] theorem seedCscCorrection_pi_div_two :
    seedCscCorrection (Real.pi / 2) = 1 - 2 / Real.pi := by
  rw [seedCscCorrection_of_ne_zero Real.pi_div_two_pos.ne']
  simp only [Real.sin_pi_div_two, inv_one]
  field_simp

/-- The exact total variation, in Mathlib's extended-nonnegative-real API. -/
theorem seedCscCorrection_eVariationOn :
    eVariationOn seedCscCorrection (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) =
      ENNReal.ofReal (2 - 4 / Real.pi) := by
  have h := seedCscCorrection_monotoneOn.eVariationOn_eq
    (show -(Real.pi / 2) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨le_rfl, by linarith [Real.pi_pos]⟩)
    (show Real.pi / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], le_rfl⟩)
  simp only [Set.inter_self, seedCscCorrection_neg, seedCscCorrection_pi_div_two] at h
  have heq : (1 - 2 / Real.pi) - -(1 - 2 / Real.pi) = 2 - 4 / Real.pi := by ring
  simpa only [heq] using h

theorem seedCscCorrection_eVariationOn_lt_two :
    eVariationOn seedCscCorrection (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) < 2 := by
  rw [seedCscCorrection_eVariationOn]
  have he : 2 - 4 / Real.pi < 2 := by
    have hp : (0 : ℝ) < 4 / Real.pi := by positivity
    linarith
  simpa only [ENNReal.ofReal_ofNat] using
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 2)).2 he

end

end Power2ModuleSVP
