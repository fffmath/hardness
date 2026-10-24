module

public import Power2ModuleSVP.SineKernelProofLobes
import Mathlib.Tactic

/-!
The one or two nearby intervals in the sinc decomposition. Strict proximity
keeps a full cell of clearance in the discarded tail, including when the
observation point is a closed interval endpoint.
-/

@[expose] public section
namespace Power2ModuleSVP
open scoped BigOperators
noncomputable section

namespace SeedKernelIntervals

/-- Components closer than one cell to the observation point. -/
def nearIndices {N J : ℕ} (I : SeedKernelIntervals N J) (θ : ℝ) : Finset (Fin J) :=
  Finset.univ.filter fun i => θ - Real.pi / N < I.rightAngle i ∧
    I.leftAngle i < θ + Real.pi / N

@[simp] theorem mem_nearIndices {N J : ℕ} (I : SeedKernelIntervals N J) (θ : ℝ)
    (i : Fin J) : i ∈ I.nearIndices θ ↔
    θ - Real.pi / N < I.rightAngle i ∧ I.leftAngle i < θ + Real.pi / N := by
  simp [nearIndices]

theorem angle_width {N J : ℕ} (I : SeedKernelIntervals N J) (hN : 0 < N) (i : Fin J) :
    Real.pi / N ≤ I.rightAngle i - I.leftAngle i := by
  have hc : (I.left i : ℝ) + 1 ≤ (I.right i : ℝ) := by
    exact_mod_cast (show I.left i + 1 ≤ I.right i from I.width_pos i)
  have hδ : 0 ≤ Real.pi / N := by positivity
  have hw := mul_le_mul_of_nonneg_right hc hδ
  simp only [leftAngle, rightAngle, mul_div_assoc, add_mul, one_mul] at *
  linarith

theorem angle_gap {N J : ℕ} (I : SeedKernelIntervals N J) (hN : 0 < N)
    {i j : Fin J} (hij : i ≠ j) :
    I.rightAngle i + Real.pi / N ≤ I.leftAngle j ∨
      I.rightAngle j + Real.pi / N ≤ I.leftAngle i := by
  have hδ : 0 ≤ Real.pi / N := by positivity
  rcases I.separated i j hij with h | h
  · left
    have hc : (I.right i : ℝ) + 1 ≤ (I.left j : ℝ) := by exact_mod_cast h
    simpa only [leftAngle, rightAngle, mul_div_assoc, add_mul, one_mul] using
      mul_le_mul_of_nonneg_right hc hδ
  · right
    have hc : (I.right j : ℝ) + 1 ≤ (I.left i : ℝ) := by exact_mod_cast h
    simpa only [leftAngle, rightAngle, mul_div_assoc, add_mul, one_mul] using
      mul_le_mul_of_nonneg_right hc hδ

theorem nearIndices_card_le_two {N J : ℕ} (I : SeedKernelIntervals N J)
    (hN : 0 < N) (θ : ℝ) : (I.nearIndices θ).card ≤ 2 := by
  classical
  have hleft : ((I.nearIndices θ).filter fun i => I.leftAngle i ≤ θ).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    rcases Finset.mem_filter.mp hi with ⟨hi, hli⟩
    rcases Finset.mem_filter.mp hj with ⟨hj, hlj⟩
    rw [mem_nearIndices] at hi hj
    by_contra hij
    rcases I.angle_gap hN hij with h | h <;> linarith [hi.1, hj.1]
  have hright : ((I.nearIndices θ).filter fun i => ¬ I.leftAngle i ≤ θ).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    rcases Finset.mem_filter.mp hi with ⟨hi, hli⟩
    rcases Finset.mem_filter.mp hj with ⟨hj, hlj⟩
    rw [mem_nearIndices] at hi hj
    have hwi := I.angle_width hN i
    have hwj := I.angle_width hN j
    have hδ : 0 < Real.pi / N := by positivity
    by_contra hij
    rcases I.angle_gap hN hij with h | h <;> linarith [hi.2, hj.2]
  have hc := Finset.card_filter_add_card_filter_not
    (s := I.nearIndices θ) (fun i => I.leftAngle i ≤ θ)
  omega

theorem nearIndices_eq_singleton_of_mem {N J : ℕ} (I : SeedKernelIntervals N J)
    (hN : 0 < N) {θ : ℝ} {i : Fin J}
    (hθ : θ ∈ Set.Icc (I.leftAngle i) (I.rightAngle i)) :
    I.nearIndices θ = {i} := by
  classical
  have hδ : 0 < Real.pi / N := by positivity
  ext j
  simp only [Finset.mem_singleton]
  constructor
  · intro hj
    rw [mem_nearIndices] at hj
    by_contra hij
    rcases I.angle_gap hN hij with h | h <;> linarith [hθ.1, hθ.2, hj.1, hj.2]
  · intro hji
    subst j
    rw [mem_nearIndices]
    exact ⟨by linarith [hθ.2], by linarith [hθ.1]⟩

end SeedKernelIntervals

/-- The continuously filled local sinc integral for one component. -/
def seedKernelSincIntegral {N J : ℕ} (I : SeedKernelIntervals N J) (θ : ℝ) (i : Fin J) : ℝ :=
  ∫ u in I.leftAngle i..I.rightAngle i,
    2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ))

/-- The local part consists exactly of components strictly closer than one
coarse cell to the observation point. -/
def seedKernelLocalPart {N J : ℕ} (I : SeedKernelIntervals N J)
    (α : Fin J → ℝ) (θ : ℝ) : ℝ :=
  ∑ i, if θ - Real.pi / N < I.rightAngle i ∧ I.leftAngle i < θ + Real.pi / N
    then α i * seedKernelSincIntegral I θ i else 0

theorem seedKernelLocalPart_eq_sum_nearIndices {N J : ℕ}
    (I : SeedKernelIntervals N J) (α : Fin J → ℝ) (θ : ℝ) :
    seedKernelLocalPart I α θ = ∑ i ∈ I.nearIndices θ, α i * seedKernelSincIntegral I θ i := by
  simp only [seedKernelLocalPart, SeedKernelIntervals.nearIndices, Finset.sum_filter]

theorem seedKernelLocalPart_eq_single_of_mem {N J : ℕ}
    (I : SeedKernelIntervals N J) (hN : 0 < N) (α : Fin J → ℝ) {θ : ℝ} {i : Fin J}
    (hθ : θ ∈ Set.Icc (I.leftAngle i) (I.rightAngle i)) :
    seedKernelLocalPart I α θ = α i * seedKernelSincIntegral I θ i := by
  rw [seedKernelLocalPart_eq_sum_nearIndices, I.nearIndices_eq_singleton_of_mem hN hθ,
    Finset.sum_singleton]

/-- The local contribution is bounded by four, independently of the
number of intervals and of the observation angle. -/
theorem seedKernelLocalPart_abs_le_four {N J : ℕ}
    (I : SeedKernelIntervals N J) (hN : 0 < N) (α : Fin J → ℝ)
    (hα : ∀ i, |α i| ≤ 1) (θ : ℝ) : |seedKernelLocalPart I α θ| ≤ 4 := by
  classical
  by_cases hcontains : I.contains θ
  · obtain ⟨i, hi⟩ := hcontains
    rw [seedKernelLocalPart_eq_single_of_mem I hN α hi, abs_mul]
    have hb := local_sinc_integral_inside_bounds_unconditional hN θ
      (I.leftAngle i) (I.rightAngle i) hi (I.angle_width hN i)
    have hb0 : 0 ≤ seedKernelSincIntegral I θ i := by
      change 0 ≤ (∫ u in I.leftAngle i..I.rightAngle i,
        2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ)))
      linarith [hb.1]
    have hbabs : |seedKernelSincIntegral I θ i| ≤ 4 := by
      rw [abs_of_nonneg hb0]
      exact hb.2
    exact (mul_le_mul (hα i) hbabs (abs_nonneg _) zero_le_one).trans (by norm_num)
  · have hind : ∀ i, |α i * seedKernelSincIntegral I θ i| ≤ 2 := by
      intro i
      have hnot : θ ∉ Set.Icc (I.leftAngle i) (I.rightAngle i) :=
        fun hi => hcontains ⟨i, hi⟩
      have hside : θ ≤ I.leftAngle i ∨ I.rightAngle i ≤ θ := by
        by_contra h
        push Not at h
        exact hnot ⟨h.1.le, h.2.le⟩
      have hab : I.leftAngle i ≤ I.rightAngle i := by
        have hw := I.angle_width hN i
        have hδ : 0 < Real.pi / N := by positivity
        linarith
      have hb := local_sinc_integral_outside_abs_le_two N θ
        (I.leftAngle i) (I.rightAngle i) hab hside
      rw [abs_mul]
      exact (mul_le_mul (hα i) hb (abs_nonneg _) zero_le_one).trans (by norm_num)
    rw [seedKernelLocalPart_eq_sum_nearIndices]
    calc
      _ ≤ ∑ i ∈ I.nearIndices θ, |α i * seedKernelSincIntegral I θ i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ I.nearIndices θ, (2 : ℝ) :=
        Finset.sum_le_sum fun i _ => hind i
      _ = (I.nearIndices θ).card * 2 := by simp
      _ ≤ 4 := by
        have hc : ((I.nearIndices θ).card : ℝ) ≤ 2 := by
          exact_mod_cast I.nearIndices_card_le_two hN θ
        linarith

/-- On a closed component, the local part has magnitude at least four
thirds for every assignment of component signs. -/
theorem seedKernelLocalPart_abs_ge_four_thirds {N J : ℕ}
    (I : SeedKernelIntervals N J) (hN : 0 < N) (α : Fin J → ℝ)
    (hα : ∀ i, α i = -1 ∨ α i = 1) {θ : ℝ} (hcontains : I.contains θ) :
    4 / 3 ≤ |seedKernelLocalPart I α θ| := by
  obtain ⟨i, hi⟩ := hcontains
  rw [seedKernelLocalPart_eq_single_of_mem I hN α hi, abs_mul]
  have ha : |α i| = 1 := by rcases hα i with h | h <;> simp [h]
  rw [ha, one_mul]
  have hb := local_sinc_integral_inside_bounds_unconditional hN θ
    (I.leftAngle i) (I.rightAngle i) hi (I.angle_width hN i)
  exact hb.1.trans (le_abs_self _)

end
end Power2ModuleSVP
