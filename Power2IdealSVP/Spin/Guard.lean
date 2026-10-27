import Power2IdealSVP.Spin.Defs
import Power2IdealSVP.Spin.Parameters

/-!
# The forbidden-distance guard

The skew guard vanishes at every active coordinate of a passing ternary spin. Balanced
base-five digits then vanish separately, and the dyadic antiperiodic orbit argument excludes
all forbidden pairs. Alternation is unnecessary for this lemma. The antipodal term is retained.

Paper: `paper/power2-ideal-svp.txt`, Lemma 2; expanded audit, Sections 2, 3 and 6.
-/

namespace Power2IdealSVP.Spin

open Power2ModuleSVP (Coeff)
open IdealCVP.Cyclotomic

/-- Unsigned cyclic distance between two coefficient positions. -/
def cyclicDistance {m : ℕ} (i j : Fin m) : ℕ :=
  min ((i.val : ℤ) - j.val).natAbs (m - ((i.val : ℤ) - j.val).natAbs)

/-- Multiplication by the guard is exactly its balanced-digit expansion. -/
theorem mul_A_apply (D : Finset ℕ) (A0 : ℕ) (σ : Coeff (n A0)) (i : Fin (n A0)) :
    mul (A D A0) σ i = ∑ j : Fin (forbiddenList D A0).length,
      (5 : ℤ) ^ j.val *
        (lift σ ((i.val : ℤ) - forbiddenAt D A0 j) -
          lift σ ((i.val : ℤ) + forbiddenAt D A0 j)) := by
  simp only [A, mul_sum_left, mul_smul_left, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Power2ModuleSVP.coeff_mul_sub_left,
    Pi.sub_apply, mul_xpow_apply (n_pos A0), sub_neg_eq_add]

/-- The coefficient inner product with the guard is zero. -/
theorem sum_fieldAt_A (D : Finset ℕ) (A0 : ℕ) (σ : Coeff (n A0)) :
    (∑ i, fieldAt (A D A0) σ i) = 0 := by
  simp only [fieldAt, A, mul_sum_left, mul_smul_left, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  have hj := (mem_forbidden_iff.mp (forbiddenAt_mem D A0 j)).2.1
  have hd : forbiddenAt D A0 j < n A0 := by have := n_pos A0; omega
  have hs := sum_skew_xpow hd σ
  calc
    _ = (5 : ℤ) ^ j.val *
        ∑ i, σ i * mul
          (xpow (n A0) (forbiddenAt D A0 j) -
            xpow (n A0) (-(forbiddenAt D A0 j : ℤ))) σ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hs]; simp

/-- The full field separates into guard, nearest neighbours and the small interaction. -/
theorem fieldAt_G_decomposition (D : Finset ℕ) (A0 h : ℕ) (σ : Coeff (n A0))
    (i : Fin (n A0)) :
    fieldAt (G D A0 h) σ i = L D A0 h * fieldAt (A D A0) σ i -
      C D A0 h * (σ i * (lift σ ((i.val : ℤ) - 1) +
        lift σ ((i.val : ℤ) + 1))) + σ i * mul (T D A0) σ i := by
  simp only [fieldAt, G, mul_add_left, Power2ModuleSVP.coeff_mul_sub_left,
    mul_smul_left, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, mul_xpow_apply (n_pos A0)]
  simp only [sub_neg_eq_add]
  ring

/-- Every non-guard contribution has the required uniform absolute bound. -/
theorem small_field_abs_le (D : Finset ℕ) (A0 h : ℕ) {σ : Coeff (n A0)}
    (hσ : Ternary σ) (i : Fin (n A0)) :
    |-(C D A0 h) * (σ i * (lift σ ((i.val : ℤ) - 1) +
        lift σ ((i.val : ℤ) + 1))) + σ i * mul (T D A0) σ i| ≤
      2 * C D A0 h + RT D A0 := by
  have hi := hσ.cube i
  have hm := abs_lift_le (by omega : (0 : ℤ) ≤ 1) hσ.cube ((i.val : ℤ) - 1)
  have hp := abs_lift_le (by omega : (0 : ℤ) ≤ 1) hσ.cube ((i.val : ℤ) + 1)
  have ht := abs_mul_le_coeffL1 (T D A0) hσ.cube i
  have hnn : |σ i * (lift σ ((i.val : ℤ) - 1) +
      lift σ ((i.val : ℤ) + 1))| ≤ 2 := by
    rw [abs_mul]
    have := abs_add_le (lift σ ((i.val : ℤ) - 1)) (lift σ ((i.val : ℤ) + 1))
    nlinarith [abs_nonneg (σ i)]
  have hts : |σ i * mul (T D A0) σ i| ≤ RT D A0 := by
    rw [abs_mul]
    change |σ i| * |mul (T D A0) σ i| ≤ coeffL1 (T D A0)
    nlinarith [abs_nonneg (mul (T D A0) σ i)]
  have hc := C_pos D A0 h
  calc
    _ ≤ |-(C D A0 h) * (σ i * (lift σ ((i.val : ℤ) - 1) +
        lift σ ((i.val : ℤ) + 1)))| + |σ i * mul (T D A0) σ i| := abs_add_le _ _
    _ ≤ 2 * C D A0 h + RT D A0 := by
      rw [abs_mul, abs_neg, abs_of_pos hc]
      nlinarith

/-- Passing spins have zero guard multiplication at every active coefficient. -/
theorem guard_zero {D : Finset ℕ} {A0 h : ℕ} (hh : 0 < h)
    {σ : Coeff (n A0)} (hσ : Ternary σ)
    (hf : ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i) :
    ∀ i ∈ support σ, mul (A D A0) σ i = 0 := by
  have hnonneg (i : Fin (n A0)) : 0 ≤ fieldAt (A D A0) σ i := by
    by_cases hi : σ i = 0
    · simp [fieldAt, hi]
    · have hfi := hf i ((mem_support σ i).mpr hi)
      have hdec := fieldAt_G_decomposition D A0 h σ i
      have hb := (abs_le.mp (small_field_abs_le D A0 h hσ i)).2
      have hL := L_pos D A0 h
      have hτ := tau_pos D A0 hh
      have hm := guard_margin D A0 h
      by_contra hn
      have ha : fieldAt (A D A0) σ i ≤ -1 := by omega
      have : fieldAt (G D A0 h) σ i ≤ -L D A0 h + 2 * C D A0 h + RT D A0 := by
        nlinarith
      omega
  have hz : ∀ i, fieldAt (A D A0) σ i = 0 := by
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp
      (sum_fieldAt_A D A0 σ)
    exact fun i => hs i (Finset.mem_univ i)
  intro i hi
  exact (mul_eq_zero.mp (hz i)).resolve_left ((mem_support σ i).mp hi)

/-- The zero guard splits into zero individual distance fields at active coordinates. -/
theorem guard_digit_zero {D : Finset ℕ} {A0 : ℕ} {σ : Coeff (n A0)}
    (hσ : Ternary σ) (hz : ∀ i ∈ support σ, mul (A D A0) σ i = 0)
    (i : Fin (n A0)) (hi : i ∈ support σ)
    (j : Fin (forbiddenList D A0).length) :
    lift σ ((i.val : ℤ) - forbiddenAt D A0 j) =
      lift σ ((i.val : ℤ) + forbiddenAt D A0 j) := by
  have hsum := hz i hi
  rw [mul_A_apply] at hsum
  have hu : ∀ j : Fin (forbiddenList D A0).length,
      -2 ≤ lift σ ((i.val : ℤ) - forbiddenAt D A0 j) -
        lift σ ((i.val : ℤ) + forbiddenAt D A0 j) ∧
      lift σ ((i.val : ℤ) - forbiddenAt D A0 j) -
        lift σ ((i.val : ℤ) + forbiddenAt D A0 j) ≤ 2 := by
    intro j
    have h1 := abs_le.mp (abs_lift_le (by omega : (0 : ℤ) ≤ 1) hσ.cube
      ((i.val : ℤ) - forbiddenAt D A0 j))
    have h2 := abs_le.mp (abs_lift_le (by omega : (0 : ℤ) ≤ 1) hσ.cube
      ((i.val : ℤ) + forbiddenAt D A0 j))
    omega
  have hdigits := balanced_five_fin_zero
    (fun j : Fin (forbiddenList D A0).length =>
      lift σ ((i.val : ℤ) - forbiddenAt D A0 j) -
        lift σ ((i.val : ℤ) + forbiddenAt D A0 j)) hu hsum
  exact sub_eq_zero.mp (hdigits j)

/-- Active distance equations extend to every integer lift with their common wrap sign. -/
theorem active_equation_lift {m : ℕ} (hm : 0 < m) (σ : Coeff m) (d : ℤ)
    (hz : ∀ i : Fin m, σ i ≠ 0 →
      lift σ ((i.val : ℤ) - d) = lift σ ((i.val : ℤ) + d)) :
    ∀ x, lift σ x ≠ 0 → lift σ (x - d) = lift σ (x + d) := by
  intro x hx
  let i : Fin m := ⟨(x % m).toNat, by
    exact (Int.toNat_lt (Int.emod_nonneg x (by omega))).mpr
      (Int.emod_lt_of_pos x (by omega))⟩
  have hi : σ i ≠ 0 := (lift_ne_zero_iff hm σ x).mp hx
  have hval : (i.val : ℤ) = x % m := Int.toNat_of_nonneg
    (Int.emod_nonneg x (by omega))
  have heq : x = i.val + (x / m) * m := by
    rw [hval]
    exact (Int.emod_add_ediv_mul x m).symm
  have hminus : x - d = (i.val - d) + (x / m) * m := by linarith
  have hplus : x + d = (i.val + d) + (x / m) * m := by linarith
  rw [hminus, hplus, lift_add_mul, lift_add_mul, hz i hi]

/-- Every forbidden step has an empty endpoint, including at the antipode. -/
theorem guard_forbidden_pair {D : Finset ℕ} {A0 h : ℕ} (hh : 0 < h)
    {σ : Coeff (n A0)} (hσ : Ternary σ)
    (hf : ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i)
    {d : ℕ} (hd : d ∈ forbidden D A0) (x : ℤ) :
    lift σ x = 0 ∨ lift σ (x + d) = 0 := by
  obtain ⟨j, hj⟩ := exists_forbiddenAt hd
  have hz := guard_zero hh hσ hf
  have heq : ∀ y, lift σ y ≠ 0 → lift σ (y - d) = lift σ (y + d) := by
    apply active_equation_lift (n_pos A0)
    intro i hi
    simpa only [hj] using guard_digit_zero hσ hz i ((mem_support σ i).mpr hi) j
  obtain ⟨k, hk⟩ := n_dyadic A0
  have hb := mem_forbidden_iff.mp hd
  have hdn : d < 2 ^ k := by have := n_pos A0; rw [← hk]; omega
  apply power_two_orbit_exclusion (lift σ) k d (by omega) hdn
  · simpa only [← hk] using lift_antiperiodic σ
  · exact heq

/-- A pair of nonzero lifted coefficients at a short positive distance is allowed. -/
theorem guard_lift_pair_allowed {D : Finset ℕ} {A0 h : ℕ} (hh : 0 < h)
    {σ : Coeff (n A0)} (hσ : Ternary σ)
    (hf : ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i)
    {d : ℕ} (hd : 0 < d) (hdn : d ≤ n A0 / 2) {x : ℤ}
    (hx : lift σ x ≠ 0) (hxd : lift σ (x + d) ≠ 0) : d ∈ Eplus D := by
  by_contra he
  have hforb : d ∈ forbidden D A0 := mem_forbidden_iff.mpr ⟨hd, hdn, he⟩
  exact (guard_forbidden_pair hh hσ hf hforb x).elim hx hxd

/-- Lemma 2: every distinct pair in a passing spin has an allowed unsigned cyclic distance. -/
theorem guard_cyclic_pair_allowed {D : Finset ℕ} {A0 h : ℕ} (hh : 0 < h)
    {σ : Coeff (n A0)} (hσ : Ternary σ)
    (hf : ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i)
    {i j : Fin (n A0)} (hi : i ∈ support σ) (hj : j ∈ support σ) (hij : i ≠ j) :
    cyclicDistance i j ∈ Eplus D := by
  wlog hlt : i.val < j.val generalizing i j
  · have hji : j.val < i.val := by
      have hne : i.val ≠ j.val := fun hv => hij (Fin.ext hv)
      omega
    have hswap := this hj hi hij.symm hji
    have habs : ((j.val : ℤ) - i.val).natAbs = ((i.val : ℤ) - j.val).natAbs := by
      rw [show (j.val : ℤ) - i.val = -((i.val : ℤ) - j.val) by ring, Int.natAbs_neg]
    simpa only [cyclicDistance, habs] using hswap
  have habs : ((i.val : ℤ) - j.val).natAbs = j.val - i.val := by omega
  unfold cyclicDistance
  rw [habs]
  have hi' : lift σ (i.val : ℤ) ≠ 0 := by simpa using (mem_support σ i).mp hi
  have hj' : lift σ (j.val : ℤ) ≠ 0 := by simpa using (mem_support σ j).mp hj
  by_cases hs : j.val - i.val ≤ n A0 / 2
  · rw [min_eq_left (by omega)]
    apply guard_lift_pair_allowed hh hσ hf (by omega) hs hi'
    simpa only [show (i.val : ℤ) + (j.val - i.val : ℕ) = j.val by omega] using hj'
  · rw [min_eq_right (by omega)]
    apply guard_lift_pair_allowed hh hσ hf (by have := j.isLt; omega) (by omega) hj'
    have heq : (j.val : ℤ) + (n A0 - (j.val - i.val) : ℕ) = i.val + n A0 := by
      have := j.isLt
      omega
    rw [heq, lift_antiperiodic σ, lift_coe]
    exact neg_ne_zero.mpr ((mem_support σ i).mp hi)

/-- Pair exclusion also implies active guard vanishing, needed in the converse construction. -/
theorem guard_zero_of_forbidden_pairs {D : Finset ℕ} {A0 : ℕ}
    {σ : Coeff (n A0)}
    (hp : ∀ d ∈ forbidden D A0, ∀ x : ℤ, lift σ x = 0 ∨ lift σ (x + d) = 0) :
    ∀ i ∈ support σ, mul (A D A0) σ i = 0 := by
  intro i hi
  have hi' : lift σ (i.val : ℤ) ≠ 0 := by simpa using (mem_support σ i).mp hi
  rw [mul_A_apply]
  apply Finset.sum_eq_zero
  intro j _
  have hd := forbiddenAt_mem D A0 j
  have hp' : lift σ ((i.val : ℤ) + forbiddenAt D A0 j) = 0 :=
    (hp _ hd i.val).resolve_left hi'
  have hm : lift σ ((i.val : ℤ) - forbiddenAt D A0 j) = 0 := by
    have hm' := hp _ hd ((i.val : ℤ) - forbiddenAt D A0 j)
    have heq : (i.val : ℤ) - forbiddenAt D A0 j + forbiddenAt D A0 j = i.val := by ring
    rw [heq] at hm'
    exact hm'.resolve_right hi'
  rw [hp', hm, sub_self]
  simp

/-- A passing active coordinate has an active nearest neighbour in the integer lift. -/
theorem guard_active_has_neighbor {D : Finset ℕ} {A0 h : ℕ} (hh : 0 < h)
    {σ : Coeff (n A0)} (hσ : Ternary σ)
    (hf : ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i)
    (i : Fin (n A0)) (hi : i ∈ support σ) :
    lift σ ((i.val : ℤ) - 1) ≠ 0 ∨ lift σ ((i.val : ℤ) + 1) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hzero := guard_zero hh hσ hf i hi
  have hdec := fieldAt_G_decomposition D A0 h σ i
  have hfield : fieldAt (G D A0 h) σ i = σ i * mul (T D A0) σ i := by
    simpa [fieldAt, hzero, hn.1, hn.2] using hdec
  have hb := abs_mul_le_coeffL1 (T D A0) hσ.cube i
  have hiabs := hσ.cube i
  have hbound : |σ i * mul (T D A0) σ i| ≤ RT D A0 := by
    rw [abs_mul]
    change |σ i| * |mul (T D A0) σ i| ≤ coeffL1 (T D A0)
    nlinarith [abs_nonneg (mul (T D A0) σ i)]
  have hfi := hf i hi
  rw [hfield] at hfi
  have hτ := tau_sub_RT D A0 h
  have := (abs_le.mp hbound).2
  omega

/-- No passing lifted support contains a pair separated by three. -/
theorem guard_lift_no_three {D : Finset ℕ} {A0 h : ℕ} (hD : DValid D A0)
    (hh : 0 < h) {σ : Coeff (n A0)} (hσ : Ternary σ)
    (hf : ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i)
    {x : ℤ} (hx : lift σ x ≠ 0) : lift σ (x + 3) = 0 := by
  have hn := separation_lt_n A0
  have hd : 3 ∈ forbidden D A0 :=
    mem_forbidden_iff.mpr ⟨by omega, by omega, three_not_mem_Eplus hD⟩
  exact (guard_forbidden_pair hh hσ hf hd x).resolve_left hx

/-- A lift immediately beside a short support has no alias from another period. -/
theorem lift_mem_support_image_of_short {m R : ℕ} {σ : Coeff m}
    (hm : R + 2 < m) (hshort : ∀ i ∈ support σ, i.val ≤ R)
    {x : ℤ} (hxl : -1 ≤ x) (hxu : x ≤ R + 1) (hx : lift σ x ≠ 0) :
    x ∈ (support σ).image (fun i => (i.val : ℤ)) := by
  have hmpos : 0 < m := by omega
  let i : Fin m := ⟨(x % m).toNat, by
    exact (Int.toNat_lt (Int.emod_nonneg x (by omega))).mpr
      (Int.emod_lt_of_pos x (by omega))⟩
  have hi : i ∈ support σ := (mem_support σ i).mpr ((lift_ne_zero_iff hmpos σ x).mp hx)
  have hirange := hshort i hi
  have hrem : (i.val : ℤ) = x % m := Int.toNat_of_nonneg
    (Int.emod_nonneg x (by omega))
  have hdvd : (m : ℤ) ∣ x - i.val := by
    rw [hrem]
    exact Int.dvd_self_sub_emod
  have hsmall : (x - i.val).natAbs < (m : ℤ).natAbs := by
    have habs : |x - i.val| < (m : ℤ) := abs_lt.mpr (by constructor <;> omega)
    rw [← Int.natCast_natAbs] at habs
    exact_mod_cast habs
  have heq : (i.val : ℤ) = x := by
    have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hsmall
    omega
  exact Finset.mem_image.mpr ⟨i, hi, heq⟩

/-- Short-arc cyclic distances are ordinary integer distances. -/
theorem cyclicDistance_eq_of_short {m R : ℕ} (hm : 2 * R < m)
    (i j : Fin m) (hi : i.val ≤ R) (hj : j.val ≤ R) :
    cyclicDistance i j = ((i.val : ℤ) - j.val).natAbs := by
  unfold cyclicDistance
  have habs : ((i.val : ℤ) - j.val).natAbs ≤ R := by omega
  exact min_eq_left (by omega)

end Power2IdealSVP.Spin
