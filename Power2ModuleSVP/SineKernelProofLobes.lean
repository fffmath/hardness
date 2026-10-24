module

public import Power2ModuleSVP.SineKernelProofSineIntegral
import Mathlib.Tactic

/-! Decreasing positive half-period integrals bound the sine integral. -/

@[expose] public section

namespace Power2ModuleSVP

noncomputable section

private theorem seed_sign_sq (n : ℕ) : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  simp

private theorem seed_signed_sinc_eq (n : ℕ) (u : ℝ)
    (h : u + n * Real.pi ≠ 0) :
    (-1 : ℝ) ^ n * Real.sinc (u + n * Real.pi) =
      Real.sin u / (u + n * Real.pi) := by
  rw [Real.sinc_of_ne_zero h, Real.sin_add_nat_mul_pi]
  calc
    _ = ((-1 : ℝ) ^ n * (-1) ^ n) * Real.sin u / (u + n * Real.pi) := by ring
    _ = _ := by rw [seed_sign_sq, one_mul]

private theorem seed_signed_sinc_nonneg (n : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) Real.pi) :
    0 ≤ (-1 : ℝ) ^ n * Real.sinc (u + n * Real.pi) := by
  have hn : (0 : ℝ) ≤ n * Real.pi := by positivity
  by_cases hd : u + n * Real.pi = 0
  · have hu0 : u = 0 := by linarith [hu.1]
    have hn0 : n = 0 := by
      have hc : (n : ℝ) = 0 := by nlinarith [Real.pi_pos, hu.1]
      exact_mod_cast hc
    simp [hn0, hu0]
  · rw [seed_signed_sinc_eq n u hd]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hu.1 hu.2) (by linarith [hu.1])

private theorem seed_signed_sinc_step (n : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) Real.pi) :
    (-1 : ℝ) ^ (n + 1) * Real.sinc (u + ((n + 1 : ℕ) : ℝ) * Real.pi) ≤
      (-1 : ℝ) ^ n * Real.sinc (u + n * Real.pi) := by
  have hn : (0 : ℝ) ≤ n * Real.pi := by positivity
  by_cases hd : u + n * Real.pi = 0
  · have hu0 : u = 0 := by linarith [hu.1]
    have hn0 : n = 0 := by
      have hc : (n : ℝ) = 0 := by nlinarith [Real.pi_pos, hu.1]
      exact_mod_cast hc
    simp [hn0, hu0, Real.sinc_of_ne_zero Real.pi_pos.ne']
  · have hp : 0 < u + n * Real.pi := lt_of_le_of_ne (by linarith [hu.1]) (Ne.symm hd)
    have hp' : 0 < u + ((n + 1 : ℕ) : ℝ) * Real.pi := by
      push_cast
      nlinarith [Real.pi_pos]
    rw [seed_signed_sinc_eq (n + 1) u hp'.ne', seed_signed_sinc_eq n u hd]
    apply div_le_div_of_nonneg_left
      (Real.sin_nonneg_of_nonneg_of_le_pi hu.1 hu.2) hp
    push_cast
    linarith [Real.pi_pos]

private def seedSineLobe (n : ℕ) : ℝ :=
  ∫ u in 0..Real.pi, (-1 : ℝ) ^ n * Real.sinc (u + n * Real.pi)

private theorem seedSineLobe_nonneg (n : ℕ) : 0 ≤ seedSineLobe n :=
  intervalIntegral.integral_nonneg Real.pi_pos.le (fun _ hu => seed_signed_sinc_nonneg n hu)

private theorem seedSineLobe_antitone : Antitone seedSineLobe := by
  apply antitone_nat_of_succ_le
  intro n
  apply intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) Real.pi_pos.le
  · exact (by fun_prop : Continuous (fun u : ℝ =>
      (-1 : ℝ) ^ (n + 1) * Real.sinc (u + ((n + 1 : ℕ) : ℝ) * Real.pi))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun u : ℝ =>
      (-1 : ℝ) ^ n * Real.sinc (u + n * Real.pi))).intervalIntegrable _ _
  · exact fun _ hu => seed_signed_sinc_step n hu

private def seedSineEndpoint (n : ℕ) : ℝ := seedSineIntegral (n * Real.pi)

private theorem seedSineEndpoint_zero : seedSineEndpoint 0 = 0 := by
  simp [seedSineEndpoint]

private theorem seedSineEndpoint_one : seedSineEndpoint 1 = seedSineIntegral Real.pi := by
  simp [seedSineEndpoint]

private theorem seedSineEndpoint_two : seedSineEndpoint 2 = seedSineIntegral (2 * Real.pi) := by
  norm_num [seedSineEndpoint]

private theorem seedSineEndpoint_step (n : ℕ) :
    seedSineEndpoint (n + 1) - seedSineEndpoint n = (-1 : ℝ) ^ n * seedSineLobe n := by
  unfold seedSineEndpoint seedSineLobe
  rw [seedSineIntegral_sub, intervalIntegral.integral_const_mul,
    ← mul_assoc, seed_sign_sq, one_mul]
  rw [intervalIntegral.integral_comp_add_right]
  congr 1 <;> push_cast <;> ring

private theorem seedSineEndpoint_even_monotone :
    Monotone (fun n : ℕ => seedSineEndpoint (2 * n)) := by
  apply monotone_nat_of_le_succ
  intro n
  have ha := seedSineEndpoint_step (2 * n)
  have hb := seedSineEndpoint_step (2 * n + 1)
  have hc := seedSineLobe_antitone (Nat.le_succ (2 * n))
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul, neg_one_mul] at ha hb
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
  linarith

private theorem seedSineEndpoint_odd_antitone :
    Antitone (fun n : ℕ => seedSineEndpoint (2 * n + 1)) := by
  apply antitone_nat_of_succ_le
  intro n
  have ha := seedSineEndpoint_step (2 * n + 1)
  have hb := seedSineEndpoint_step (2 * n + 1 + 1)
  have hc := seedSineLobe_antitone (Nat.le_succ (2 * n + 1))
  have hpow : (-1 : ℝ) ^ (2 * n + 1 + 1) = 1 := by
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
    simp [pow_mul]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul, neg_one_mul] at ha
  rw [hpow, one_mul] at hb
  rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by omega]
  linarith

private theorem seedSineIntegral_phase_monotone (n : ℕ) :
    MonotoneOn (fun x : ℝ => (-1 : ℝ) ^ n * seedSineIntegral x)
      (Set.Icc (n * Real.pi) (((n + 1 : ℕ) : ℝ) * Real.pi)) := by
  intro a ha b hb hab
  have hi : 0 ≤ ∫ x in a..b, (-1 : ℝ) ^ n * Real.sinc x := by
    apply intervalIntegral.integral_nonneg hab
    intro x hx
    have hu : x - n * Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor
      · linarith [ha.1, hx.1]
      · push_cast at hb
        linarith [hb.2, hx.2]
    have hp := seed_signed_sinc_nonneg n hu
    simpa only [sub_add_cancel] using hp
  rw [intervalIntegral.integral_const_mul, ← seedSineIntegral_sub] at hi
  nlinarith

private theorem seedSineIntegral_lobe_bounds (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (n * Real.pi) (((n + 1 : ℕ) : ℝ) * Real.pi)) :
    0 ≤ seedSineIntegral x ∧ seedSineIntegral x ≤ seedSineIntegral Real.pi ∧
      (n ≠ 0 → seedSineIntegral (2 * Real.pi) ≤ seedSineIntegral x) := by
  have hlow := seedSineIntegral_phase_monotone n
    (show n * Real.pi ∈ Set.Icc (n * Real.pi) (((n + 1 : ℕ) : ℝ) * Real.pi) from
      ⟨le_rfl, by push_cast; nlinarith [Real.pi_pos]⟩) hx hx.1
  have hhigh := seedSineIntegral_phase_monotone n hx
    (show ((n + 1 : ℕ) : ℝ) * Real.pi ∈
      Set.Icc (n * Real.pi) (((n + 1 : ℕ) : ℝ) * Real.pi) from
      ⟨by push_cast; nlinarith [Real.pi_pos], le_rfl⟩) hx.2
  change (-1 : ℝ) ^ n * seedSineEndpoint n ≤ (-1 : ℝ) ^ n * seedSineIntegral x at hlow
  change (-1 : ℝ) ^ n * seedSineIntegral x ≤ (-1 : ℝ) ^ n * seedSineEndpoint (n + 1) at hhigh
  obtain ⟨k, hnk | hnk⟩ : ∃ k : ℕ, n = 2 * k ∨ n = 2 * k + 1 := by
    refine ⟨n / 2, ?_⟩
    omega
  · subst n
    have ha := seedSineEndpoint_even_monotone (Nat.zero_le k)
    have hb := seedSineEndpoint_odd_antitone (Nat.zero_le k)
    simp only [Nat.mul_zero, Nat.zero_add, seedSineEndpoint_zero, seedSineEndpoint_one] at ha hb
    simp only [pow_mul, neg_one_sq, one_pow, one_mul] at hlow hhigh
    refine ⟨by linarith, by linarith, ?_⟩
    intro hn0
    have hk : 1 ≤ k := by omega
    have hc := seedSineEndpoint_even_monotone hk
    norm_num only [Nat.mul_one, seedSineEndpoint_two] at hc
    linarith
  · subst n
    have ha := seedSineEndpoint_even_monotone (Nat.zero_le (k + 1))
    have hb := seedSineEndpoint_odd_antitone (Nat.zero_le k)
    have hc := seedSineEndpoint_even_monotone (Nat.le_add_left 1 k)
    have hidx : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    simp only [Nat.mul_zero, Nat.zero_add, seedSineEndpoint_zero, seedSineEndpoint_one] at ha hb
    norm_num only [Nat.mul_one, seedSineEndpoint_two] at hc
    simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul, neg_one_mul]
      at hlow hhigh
    rw [hidx] at hhigh
    refine ⟨by linarith, by linarith, ?_⟩
    intro _
    linarith

private theorem seedSineIntegral_mem_lobe {x : ℝ} (hx : 0 ≤ x) :
    ∃ n : ℕ, x ∈ Set.Icc (n * Real.pi) (((n + 1 : ℕ) : ℝ) * Real.pi) ∧
      (Real.pi ≤ x → n ≠ 0) := by
  let n := ⌊x / Real.pi⌋₊
  have hlow := Nat.floor_le (div_nonneg hx Real.pi_pos.le)
  have hhigh := Nat.lt_floor_add_one (x / Real.pi)
  have ha : (n : ℝ) * Real.pi ≤ x := by
    exact (le_div_iff₀ Real.pi_pos).1 hlow
  have hb : x ≤ ((n + 1 : ℕ) : ℝ) * Real.pi := by
    have h := (div_lt_iff₀ Real.pi_pos).1 hhigh
    push_cast
    linarith
  refine ⟨n, ⟨ha, hb⟩, ?_⟩
  intro hπ hn
  have hc : (1 : ℕ) ≤ n := Nat.le_floor ((le_div_iff₀ Real.pi_pos).2 (by simpa using hπ))
  omega

theorem seedSineIntegral_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ seedSineIntegral x := by
  obtain ⟨n, hn, _⟩ := seedSineIntegral_mem_lobe hx
  exact (seedSineIntegral_lobe_bounds n x hn).1

theorem seedSineIntegral_le_two {x : ℝ} (hx : 0 ≤ x) : seedSineIntegral x ≤ 2 := by
  obtain ⟨n, hn, _⟩ := seedSineIntegral_mem_lobe hx
  exact (seedSineIntegral_lobe_bounds n x hn).2.1.trans seedSineIntegral_pi_lt_two.le

theorem seedSineIntegral_ge_four_thirds {x : ℝ} (hx : Real.pi ≤ x) :
    4 / 3 ≤ seedSineIntegral x := by
  obtain ⟨n, hn, hn0⟩ := seedSineIntegral_mem_lobe (x := x) (by linarith [Real.pi_pos])
  exact seedSineIntegral_two_pi_gt_four_thirds.le.trans
    ((seedSineIntegral_lobe_bounds n x hn).2.2 (hn0 hx))

theorem seedSineIntegral_abs_le_two (x : ℝ) : |seedSineIntegral x| ≤ 2 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg (seedSineIntegral_nonneg hx)]
    exact seedSineIntegral_le_two hx
  · have hn : 0 ≤ -x := by linarith
    have h := seedSineIntegral_le_two hn
    have h0 := seedSineIntegral_nonneg hn
    rw [seedSineIntegral_neg] at h h0
    rw [abs_of_nonpos (by linarith)]
    exact h

/-- The containing-interval sinc bounds have no remaining analytic premise. -/
theorem local_sinc_integral_inside_bounds_unconditional
    {N : ℕ} (hN : 0 < N) (θ a b : ℝ) (hθ : θ ∈ Set.Icc a b)
    (hwidth : Real.pi / N ≤ b - a) :
    4 / 3 ≤ (∫ u in a..b,
        2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ))) ∧
      (∫ u in a..b,
        2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ))) ≤ 4 :=
  local_sinc_integral_inside_bounds (fun _ => seedSineIntegral_nonneg)
    (fun _ => seedSineIntegral_le_two) (fun _ => seedSineIntegral_ge_four_thirds)
    hN θ a b hθ hwidth

private theorem seedSineIntegral_sub_abs_le_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |seedSineIntegral x - seedSineIntegral y| ≤ 2 := by
  have hx0 := seedSineIntegral_nonneg hx
  have hy0 := seedSineIntegral_nonneg hy
  have hx2 := seedSineIntegral_le_two hx
  have hy2 := seedSineIntegral_le_two hy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- An interval entirely to either side of the observation point contributes
at most two to the local sinc expression. -/
theorem local_sinc_integral_outside_abs_le_two (N : ℕ) (θ a b : ℝ)
    (hab : a ≤ b) (hθ : θ ≤ a ∨ b ≤ θ) :
    |∫ u in a..b, 2 * (N : ℝ) * Real.sinc (2 * (N : ℝ) * (u - θ))| ≤ 2 := by
  rw [local_sinc_integral]
  rcases hθ with hθ | hθ
  · apply seedSineIntegral_sub_abs_le_two
    · exact mul_nonneg (by positivity) (by linarith)
    · exact mul_nonneg (by positivity) (by linarith)
  · rw [show 2 * (N : ℝ) * (b - θ) = -(2 * (N : ℝ) * (θ - b)) by ring,
      show 2 * (N : ℝ) * (a - θ) = -(2 * (N : ℝ) * (θ - a)) by ring,
      seedSineIntegral_neg, seedSineIntegral_neg]
    rw [neg_sub_neg]
    apply seedSineIntegral_sub_abs_le_two
    · exact mul_nonneg (by positivity) (by linarith)
    · exact mul_nonneg (by positivity) (by linarith)

end

end Power2ModuleSVP
