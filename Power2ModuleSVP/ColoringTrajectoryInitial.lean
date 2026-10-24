module

public import Power2ModuleSVP.ColoringTrajectoryProjector

/-! Exponential enclosures for the implemented Taylor initialization. -/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

open scoped BigOperators

theorem expSum_cast (s : ℚ) (L : ℕ) :
    (expSum s L : ℝ) = ∑ k ∈ Finset.range L, (s : ℝ) ^ k / k.factorial := by
  have hrange : (List.range L).toFinset = Finset.range L := by ext k; simp
  simp [expSum, ← List.sum_toFinset _ List.nodup_range, hrange]

theorem expSum_one_le {s : ℚ} (hs : 0 ≤ s) {L : ℕ} (hL : 0 < L) :
    1 ≤ (expSum s L : ℝ) := by
  rw [expSum_cast]
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs
  have h := Finset.single_le_sum (f := fun k => (s : ℝ) ^ k / (k.factorial : ℝ))
    (fun k _ => by positivity) (Finset.mem_range.mpr hL)
  simpa using h

theorem expSum_le_exp {s : ℚ} (hs : 0 ≤ s) (L : ℕ) :
    (expSum s L : ℝ) ≤ Real.exp (s : ℝ) := by
  rw [expSum_cast]
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hs) L

/-- A factorial tail bound obtained by comparing the single Taylor term at
`4s` with its full exponential. This avoids a separate Stirling estimate. -/
theorem taylor_term_decay {s : ℝ} (hs : 0 ≤ s) (L : ℕ) (hL : 8 * s ≤ L) :
    s ^ L / (L.factorial : ℝ) ≤ (1 / 2 : ℝ) ^ L := by
  have hehalf : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
    have h := Real.exp_le_two_add_div_two_sub (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 2)
    norm_num at h
    linarith
  have he : Real.exp (4 * s) ≤ (2 : ℝ) ^ L := by
    calc
      _ ≤ Real.exp ((L : ℝ) * (1 / 2)) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp ((1 : ℝ) / 2) ^ L := Real.exp_nat_mul _ _
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hehalf L
  have ht := (Real.pow_div_factorial_le_exp (4 * s) (by positivity) L).trans he
  have hid : (4 : ℝ) ^ L * (1 / 2 : ℝ) ^ L = (2 : ℝ) ^ L := by
    rw [← mul_pow]
    norm_num
  rw [mul_pow] at ht
  have hpos : (0 : ℝ) < 4 ^ L := by positivity
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    _ = (4 : ℝ) ^ L * s ^ L / (L.factorial : ℝ) := by ring
    _ ≤ _ := ht.trans_eq hid.symm

theorem expSum_error {s : ℚ} (hs : 0 ≤ s) (L : ℕ) (hL : 8 * (s : ℝ) ≤ L) :
    Real.exp (s : ℝ) - (expSum s L : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ L := by
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs
  have hc : ‖(s : ℂ)‖ / (L + 1) ≤ (1 / 2 : ℝ) := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg hs']
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < L + 1)).mpr
    linarith
  have hb := Complex.exp_bound' (x := (s : ℂ)) (n := L) (by simpa using hc)
  have hcast : (Complex.exp (s : ℂ) -
      ∑ k ∈ Finset.range L, (s : ℂ) ^ k / (k.factorial : ℂ)) =
      ((Real.exp (s : ℝ) - (expSum s L : ℝ) : ℝ) : ℂ) := by
    rw [expSum_cast]
    push_cast
    rfl
  rw [hcast] at hb
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_ratCast,
    abs_of_nonneg hs'] at hb
  exact (le_abs_self _).trans (hb.trans (by nlinarith [taylor_term_decay hs' L hL]))

theorem initialWeight_enclosure {r m : ℕ} (hr : 0 < r) (lam : ℚ)
    (hl : lam ^ 2 ≤ 4 * (r : ℚ)) :
    Real.exp (-((lam : ℝ) ^ 2)) ≤ (initialWeight r m lam : ℝ) ∧
      (initialWeight r m lam : ℝ) < Real.exp (-((lam : ℝ) ^ 2)) + (mesh r m : ℝ) := by
  let L := max (32 * r) (precision r m + 4)
  let S : ℝ := expSum (lam ^ 2) L
  let E := Real.exp ((lam : ℝ) ^ 2)
  have hL₁ : 32 * r ≤ L := le_max_left _ _
  have hL₂ : precision r m + 4 ≤ L := le_max_right _ _
  have hS : 1 ≤ S := expSum_one_le (sq_nonneg _) (by omega)
  have hE : 1 ≤ E := Real.one_le_exp (sq_nonneg _)
  have hSE : S ≤ E := by simpa [S, E] using expSum_le_exp (sq_nonneg lam) L
  have ht : E - S ≤ 2 * (1 / 2 : ℝ) ^ L := by
    have h := expSum_error (sq_nonneg lam) L (by
      have hl' : (lam : ℝ) ^ 2 ≤ 4 * (r : ℝ) := by exact_mod_cast hl
      have hL' : 32 * (r : ℝ) ≤ L := by exact_mod_cast hL₁
      push_cast
      linarith)
    simpa [E, S] using h
  have htail : 2 * (1 / 2 : ℝ) ^ L ≤ (mesh r m : ℝ) / 2 := by
    have hpow : (1 / 2 : ℝ) ^ L ≤ (1 / 2 : ℝ) ^ (precision r m + 4) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hL₂
    have hm : (mesh r m : ℝ) = (1 / 2 : ℝ) ^ precision r m := by
      simp [mesh]
    rw [hm]
    rw [pow_add] at hpow
    norm_num at hpow
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (precision r m)]
  have hSi : 0 < S := by linarith
  have hEi : 0 < E := by linarith
  have hlo : E⁻¹ ≤ S⁻¹ := inv_anti₀ hSi hSE
  have hhi : S⁻¹ ≤ E⁻¹ + (mesh r m : ℝ) / 2 := by
    have hmul : 1 ≤ E * S := by nlinarith
    have hm := (show (0 : ℝ) < mesh r m by exact_mod_cast mesh_pos r m).le
    calc
      S⁻¹ = E / (E * S) := by field_simp
      _ ≤ (S + (mesh r m : ℝ) / 2 * (E * S)) / (E * S) :=
        div_le_div_of_nonneg_right (by nlinarith) (by positivity)
      _ = E⁻¹ + (mesh r m : ℝ) / 2 := by field_simp
  have heq : Real.exp (-((lam : ℝ) ^ 2)) = E⁻¹ := Real.exp_neg _
  have hsCast : (((expSum (lam ^ 2) L)⁻¹ : ℚ) : ℝ) = S⁻¹ := by simp [S]
  have h := roundUp_half_enclosure (η := mesh r m)
    (w := (expSum (lam ^ 2) L)⁻¹) (target := Real.exp (-((lam : ℝ) ^ 2))) (mesh_pos r m)
    (by simpa only [heq, hsCast] using hlo) (by simpa only [heq, hsCast] using hhi)
  exact h

theorem mesh_budget (r m : ℕ) :
    (m : ℝ) * ((stepBudget r : ℝ) + 1) * (mesh r m : ℝ) < 1 / 1024 := by
  have h := Nat.lt_size_self (1024 * m * (stepBudget r + 1))
  have h' : (1024 : ℝ) * m * ((stepBudget r : ℝ) + 1) < 2 ^ precision r m := by
    exact_mod_cast h
  have hp : (0 : ℝ) < 2 ^ precision r m := by positivity
  simp only [mesh, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
  apply (mul_lt_mul_iff_left₀ hp).mp
  have hid : (m : ℝ) * ((stepBudget r : ℝ) + 1) * (1 / 2 ^ precision r m) *
      2 ^ precision r m = m * ((stepBudget r : ℝ) + 1) := by field_simp
  rw [hid]
  linarith

end Power2ModuleSVP.PartialColoringAlg
