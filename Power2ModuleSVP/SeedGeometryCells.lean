module

public import Power2ModuleSVP.SeedGeometryRolle
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
Seven-cell exclusion and axis clearance for a smooth normalized wave. These
lemmas retain the interpolation and endpoint margins in `lem:seed-intervals`.
The Rudin--Shapiro derivative estimates are separate inputs.
-/

@[expose] public section

namespace Power2ModuleSVP

open Set

noncomputable section

private theorem seed_wave_sub_bound (F : ℕ → ℝ → ℝ)
    (hF : ∀ r x, HasDerivAt (F r) (F (r + 1) x) x)
    {n : ℕ} {B : ℝ} (hB : ∀ x, |F (n + 1) x| ≤ B) (x y : ℝ) :
    |F n x - F n y| ≤ B * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := F n) (f' := F (n + 1))
    (fun t _ => (hF n t).hasDerivWithinAt)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hB t)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

/-- Seven consecutive cells cannot all contain a small witness for a wave
whose first four derivatives have the stated bounds and nondegeneracy. -/
theorem seed_seven_cell_exclusion (F : ℕ → ℝ → ℝ)
    (hF : ∀ r x, HasDerivAt (F r) (F (r + 1) x) x)
    (hnondegenerate : ∀ x, ∃ r : Fin 4, 1 / 4 ≤ |F r.val x|)
    (hbound : ∀ r ≤ 4, ∀ x, |F r x| ≤ (2 : ℝ) ^ r + 2)
    {a b : ℝ} (ha : 0 < a) (haMax : a ≤ 1 / 2048)
    (point : Fin 7 → ℝ)
    (hpoint : ∀ i, point i ∈ Icc (b + (i.val : ℝ) * a)
      (b + ((i.val : ℝ) + 1) * a))
    (hsmall : ∀ i, |F 0 (point i)| ≤ a ^ 3 / 128) : False := by
  have haOne : a ≤ 1 := by linarith
  have hlocal (n : ℕ) (hnpos : 0 < n) (hn : n ≤ 3) :
      |F n (point 0)| < 1 / 4 := by
    let node : Fin (n + 1) → ℝ := fun i => point ⟨2 * i.val, by omega⟩
    have hlo (i : Fin (n + 1)) : b + 2 * (i.val : ℝ) * a ≤ node i := by
      simpa only [node, Nat.cast_mul, Nat.cast_ofNat] using (hpoint ⟨2 * i.val, by omega⟩).1
    have hhi (i : Fin (n + 1)) : node i ≤ b + (2 * (i.val : ℝ) + 1) * a := by
      simpa only [node, Nat.cast_mul, Nat.cast_ofNat] using (hpoint ⟨2 * i.val, by omega⟩).2
    have hgap (i j : Fin (n + 1)) (hij : i < j) : a ≤ node j - node i := by
      have hij' : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
        exact_mod_cast (show i.val + 1 ≤ j.val from hij)
      have hp := mul_nonneg (show 0 ≤ (j.val : ℝ) - i.val - 1 by linarith) ha.le
      nlinarith [hlo j, hhi i]
    have hmono : StrictMono node := by
      intro i j hij
      have := hgap i j hij
      linarith
    have hsep : ∀ i j, i ≠ j → a ≤ |node i - node j| := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hij | hji
      · rw [abs_of_nonpos (sub_nonpos.mpr (hmono hij).le)]
        linarith [hgap i j hij]
      · rw [abs_of_nonneg (sub_nonneg.mpr (hmono hji).le)]
        exact hgap j i hji
    have hpow : a ^ 3 ≤ a ^ n := pow_le_pow_of_le_one ha.le haOne hn
    obtain ⟨ξ, hξ, hξsmall⟩ := seed_interpolation_derivative_bound F hF n node hmono ha
      (show 0 ≤ a ^ n / 128 by positivity) hsep
      (fun i => (hsmall _).trans (div_le_div_of_nonneg_right hpow (by norm_num)))
    have hcoef : ((n + 1 : ℕ) : ℝ) * n.factorial ≤ 24 := by
      interval_cases n <;> norm_num [Nat.factorial]
    have hcancel : ((n + 1 : ℕ) : ℝ) * n.factorial * (a ^ n / 128) / a ^ n =
        ((n + 1 : ℕ) : ℝ) * n.factorial / 128 := by
      field_simp [ne_of_gt (pow_pos ha n)]
    rw [hcancel] at hξsmall
    have hξsmall' : |F n ξ| ≤ 24 / 128 :=
      hξsmall.trans (div_le_div_of_nonneg_right hcoef (by norm_num))
    have hnode0 : node 0 = point 0 := by simp [node]
    have hξlo : point 0 ≤ ξ := by simpa only [hnode0] using hξ.1
    have hξhi : ξ ≤ b + 7 * a := by
      have hnr : (n : ℝ) ≤ 3 := by exact_mod_cast hn
      have hh := hhi (Fin.last n)
      simp only [Fin.val_last] at hh
      nlinarith [mul_nonneg (show 0 ≤ 3 - (n : ℝ) by linarith) ha.le, hξ.2]
    have hdist : |point 0 - ξ| ≤ 7 * a := by
      rw [abs_of_nonpos (sub_nonpos.mpr hξlo)]
      have h0 := (hpoint 0).1
      norm_num at h0
      linarith
    have hB : ∀ x, |F (n + 1) x| ≤ 18 := by
      intro x
      have hb := hbound (n + 1) (by omega) x
      have hc : (2 : ℝ) ^ (n + 1) + 2 ≤ 18 := by
        interval_cases n <;> norm_num
      exact hb.trans hc
    have hdiff := (seed_wave_sub_bound F hF hB (point 0) ξ).trans
      (mul_le_mul_of_nonneg_left hdist (by norm_num : (0 : ℝ) ≤ 18))
    have htri := abs_add_le (F n (point 0) - F n ξ) (F n ξ)
    rw [sub_add_cancel] at htri
    linarith
  obtain ⟨r, hr⟩ := hnondegenerate (point 0)
  by_cases hzero : r.val = 0
  · have hp : a ^ 3 ≤ 1 := pow_le_one₀ ha.le haOne
    have hs := (hsmall 0).trans (div_le_div_of_nonneg_right hp (by norm_num))
    rw [hzero] at hr
    linarith
  · exact (not_lt_of_ge hr) (hlocal r.val (Nat.pos_of_ne_zero hzero) (by omega))

/-- Any choice of one point in each of seven consecutive cells includes
a value above the small-witness threshold. -/
theorem seed_seven_cell_large_witness (F : ℕ → ℝ → ℝ)
    (hF : ∀ r x, HasDerivAt (F r) (F (r + 1) x) x)
    (hnondegenerate : ∀ x, ∃ r : Fin 4, 1 / 4 ≤ |F r.val x|)
    (hbound : ∀ r ≤ 4, ∀ x, |F r x| ≤ (2 : ℝ) ^ r + 2)
    {a b : ℝ} (ha : 0 < a) (haMax : a ≤ 1 / 2048)
    (point : Fin 7 → ℝ)
    (hpoint : ∀ i, point i ∈ Icc (b + (i.val : ℝ) * a)
      (b + ((i.val : ℝ) + 1) * a)) :
    ∃ i, a ^ 3 / 128 < |F 0 (point i)| := by
  by_contra h
  push Not at h
  exact seed_seven_cell_exclusion F hF hnondegenerate hbound ha haMax point hpoint h

/-- Among seven consecutive short cells, one entire closed cell lies
strictly above the small-value threshold. -/
theorem seed_seven_cells_unmarked (F : ℕ → ℝ → ℝ)
    (hF : ∀ r x, HasDerivAt (F r) (F (r + 1) x) x)
    (hnondegenerate : ∀ x, ∃ r : Fin 4, 1 / 4 ≤ |F r.val x|)
    (hbound : ∀ r ≤ 4, ∀ x, |F r x| ≤ (2 : ℝ) ^ r + 2)
    {a b : ℝ} (ha : 0 < a) (haMax : a ≤ 1 / 2048) :
    ∃ i : Fin 7, ∀ x ∈ Icc (b + (i.val : ℝ) * a)
      (b + ((i.val : ℝ) + 1) * a), a ^ 3 / 128 < |F 0 x| := by
  by_contra h
  push Not at h
  choose point hpoint hsmall using h
  exact seed_seven_cell_exclusion F hF hnondegenerate hbound ha haMax point hpoint hsmall

/-- A wave equal to one at an axis and with derivative at most four stays
above one half for 101 sufficiently short cell widths. -/
theorem seed_axis_clearance {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hbound : ∀ x, |f' x| ≤ 4)
    {axis x a : ℝ} (haxis : f axis = 1) (haMax : a ≤ 1 / 2048)
    (hnear : |x - axis| ≤ 101 * a) : 1 / 2 < |f x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := f) (f' := f')
    (fun t _ => (hf t).hasDerivWithinAt)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hbound t)
    convex_univ (Set.mem_univ axis) (Set.mem_univ x)
  simp only [Real.norm_eq_abs, haxis] at h
  have hh := abs_sub_abs_le_abs_sub (1 : ℝ) (f x)
  rw [abs_one, abs_sub_comm] at hh
  nlinarith

end

end Power2ModuleSVP
