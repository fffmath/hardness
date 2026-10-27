import Power2ModuleSVP.Coset.ParityBlock

/-!
# Sparse-spin coefficient arithmetic

Integer lifts use Euclidean division and the sign of the quotient, so negative indices carry
exactly the negacyclic sign. The orbit lemma is independent of support alternation.

Paper: `paper/power2-ideal-svp.txt`, Sections 1.2–1.3; audit Sections 2 and 6.
-/

namespace Power2IdealSVP.Spin

open Power2ModuleSVP (Coeff)
open IdealCVP.Cyclotomic

/-- The sign `(-1)^q`, including for negative integer exponents. -/
def signZ (q : ℤ) : ℤ := (q.negOnePow : ℤ)

/-- The sign at exponent zero is positive. -/
@[simp] theorem signZ_zero : signZ 0 = 1 := by simp [signZ]

/-- Addition of integer exponents multiplies their signs. -/
@[simp] theorem signZ_add (p q : ℤ) : signZ (p + q) = signZ p * signZ q := by
  simp [signZ, Int.negOnePow_add]

/-- Increasing an integer exponent by one reverses its sign. -/
@[simp] theorem signZ_add_one (q : ℤ) : signZ (q + 1) = -signZ q := by
  simp [signZ, Int.negOnePow_add]

/-- Negating an integer exponent preserves its sign. -/
@[simp] theorem signZ_neg (q : ℤ) : signZ (-q) = signZ q := by
  simp [signZ, Int.negOnePow_neg]

/-- Each integer sign is one or minus one. -/
theorem signZ_cases (q : ℤ) : signZ q = 1 ∨ signZ q = -1 := by
  rcases Int.units_eq_one_or q.negOnePow with h | h <;> simp [signZ, h]

/-- Every integer power of minus one has absolute value one. -/
@[simp] theorem abs_signZ (q : ℤ) : |signZ q| = 1 := by
  rcases signZ_cases q with h | h <;> simp [h]

/-- Every integer power of minus one squares to one. -/
@[simp] theorem signZ_sq (q : ℤ) : signZ q * signZ q = 1 := by
  rcases signZ_cases q with h | h <;> simp [h]

/-- Antiperiodic extension of a coefficient array to every integer index. -/
def lift {n : ℕ} (σ : Coeff n) (x : ℤ) : ℤ :=
  if hn : 0 < n then
    signZ (x / n) * σ ⟨(x % n).toNat, by
      exact (Int.toNat_lt (Int.emod_nonneg x (by omega))).mpr
        (Int.emod_lt_of_pos x (by omega))⟩
  else 0

/-- The reduced coefficient array of the signed monomial `X^k`. -/
def xpow (n : ℕ) (k : ℤ) : Coeff n := fun i =>
  if (k % n).toNat = i.val then signZ (k / n) else 0

/-- Integer coefficient one-norm. -/
def coeffL1 {n : ℕ} (a : Coeff n) : ℤ := ∑ i, |a i|

/-- Lifting an ordinary coefficient preserves its value. -/
@[simp] theorem lift_coe {n : ℕ} (σ : Coeff n) (i : Fin n) :
    lift σ (i.val : ℤ) = σ i := by
  have hn : 0 < n := by have := i.isLt; omega
  simp [lift, hn, Int.ediv_eq_zero_of_lt (a := (i.val : ℤ)) (b := (n : ℤ)) (by omega)
      (by exact_mod_cast i.isLt),
    Int.emod_eq_of_lt (a := (i.val : ℤ)) (b := (n : ℤ)) (by omega)
      (by exact_mod_cast i.isLt)]

/-- The lift changes sign on adding one full period. -/
theorem lift_antiperiodic {n : ℕ} (σ : Coeff n) :
    Function.Antiperiodic (lift σ) (n : ℤ) := by
  intro x
  by_cases hn : 0 < n
  · simp only [lift, dite_eq_left hn, Int.add_emod_right]
    have hdiv : (x + (n : ℤ)) / n = x / n + 1 := by
      simpa using Int.add_mul_ediv_right x 1 (show (n : ℤ) ≠ 0 by omega)
    rw [hdiv, signZ_add_one]
    ring
  · simp [lift, hn]

/-- Every integer translate has the expected sign. -/
theorem lift_add_mul {n : ℕ} (σ : Coeff n) (x k : ℤ) :
    lift σ (x + k * n) = signZ k * lift σ x := by
  exact (lift_antiperiodic σ).add_int_mul_eq k

/-- The lift preserves absolute coefficient bounds. -/
theorem abs_lift_le {n : ℕ} {σ : Coeff n} {B : ℤ} (hB : 0 ≤ B)
    (hσ : ∀ i, |σ i| ≤ B) (x : ℤ) : |lift σ x| ≤ B := by
  by_cases hn : 0 < n
  · simp only [lift, dite_eq_left hn, abs_mul, abs_signZ, one_mul]
    exact hσ _
  · simp [lift, hn, hB]

/-- A lift vanishes exactly when the coefficient at its remainder vanishes. -/
theorem lift_ne_zero_iff {n : ℕ} (hn : 0 < n) (σ : Coeff n) (x : ℤ) :
    lift σ x ≠ 0 ↔ σ ⟨(x % n).toNat, by
      exact (Int.toNat_lt (Int.emod_nonneg x (by omega))).mpr
        (Int.emod_lt_of_pos x (by omega))⟩ ≠ 0 := by
  simp only [lift, dite_eq_left hn, mul_ne_zero_iff]
  have hs : signZ (x / n) ≠ 0 := by
    rcases signZ_cases (x / n) with h | h <;> omega
  simp [hs]

/-- Natural exponents below the degree reduce without a sign. -/
theorem xpow_of_lt {n k : ℕ} (hk : k < n) :
    xpow n (k : ℤ) = monomial ⟨k, hk⟩ 1 := by
  funext i
  simp only [xpow, monomial]
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast hk),
    Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast hk), signZ_zero]
  simp [Fin.ext_iff, eq_comm]

/-- Integer exponent monomials change sign after adding the degree. -/
theorem xpow_add_degree {n : ℕ} (hn : 0 < n) (k : ℤ) :
    xpow n (k + n) = -xpow n k := by
  funext i
  simp only [xpow, Int.add_emod_right, Pi.neg_apply]
  have hdiv : (k + (n : ℤ)) / n = k / n + 1 := by
    simpa using Int.add_mul_ediv_right k 1 (show (n : ℤ) ≠ 0 by omega)
  rw [hdiv, signZ_add_one]
  split_ifs <;> rfl

/-- A zero balanced base-five expansion has every digit zero. -/
theorem balanced_five_zero (s : ℕ) (u : ℕ → ℤ)
    (hu : ∀ j < s, -2 ≤ u j ∧ u j ≤ 2)
    (hs : ∑ j ∈ Finset.range s, (5 : ℤ) ^ j * u j = 0) :
    ∀ j < s, u j = 0 := by
  induction s generalizing u with
  | zero => simp
  | succ s ih =>
    have heq : (5 : ℤ) * (∑ j ∈ Finset.range s, 5 ^ j * u (j + 1)) + u 0 = 0 := by
      simpa [Finset.sum_range_succ', pow_succ, mul_assoc, mul_left_comm,
        ← Finset.mul_sum] using hs
    have hdvd : (5 : ℤ) ∣ u 0 := ⟨-(∑ j ∈ Finset.range s, 5 ^ j * u (j + 1)), by
      linarith⟩
    have hz : u 0 = 0 := by
      have hmod := Int.emod_eq_zero_of_dvd hdvd
      have hbound := hu 0 (by omega)
      omega
    have htail : ∑ j ∈ Finset.range s, (5 : ℤ) ^ j * u (j + 1) = 0 := by
      linarith
    have hzero := ih (fun j => u (j + 1)) (fun j hj => hu (j + 1) (by omega)) htail
    intro j hj
    cases j with
    | zero => exact hz
    | succ j => exact hzero j (by omega)

/-- Active zero difference fields propagate a distance pair with period two along its orbit. -/
theorem active_pair_propagation (f : ℤ → ℤ) (d x : ℤ)
    (hz : ∀ y, f y ≠ 0 → f (y - d) = f (y + d))
    (hx : f x ≠ 0) (hxd : f (x + d) ≠ 0) :
    ∀ m : ℕ,
      f (x + (2 * (m : ℤ)) * d) = f x ∧
      f (x + (2 * (m : ℤ) + 1) * d) = f (x + d) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hodd : f (x + (2 * (m : ℤ) + 1) * d) ≠ 0 := by rwa [ih.2]
    have heven := hz (x + (2 * (m : ℤ) + 1) * d) hodd
    have hnext : f (x + (2 * ((m + 1 : ℕ) : ℤ)) * d) = f x := by
      calc
        _ = f (x + (2 * (m : ℤ) + 1) * d + d) := by congr 1; push_cast; ring
        _ = f (x + (2 * (m : ℤ) + 1) * d - d) := heven.symm
        _ = f (x + (2 * (m : ℤ)) * d) := by congr 1; ring
        _ = f x := ih.1
    refine ⟨hnext, ?_⟩
    have hnextne : f (x + (2 * ((m + 1 : ℕ) : ℤ)) * d) ≠ 0 := by rwa [hnext]
    have hnextodd := hz (x + (2 * ((m + 1 : ℕ) : ℤ)) * d) hnextne
    calc
      _ = f (x + (2 * ((m + 1 : ℕ) : ℤ)) * d + d) := by congr 1; ring
      _ = f (x + (2 * ((m + 1 : ℕ) : ℤ)) * d - d) := hnextodd.symm
      _ = f (x + (2 * (m : ℤ) + 1) * d) := by congr 1; push_cast; ring
      _ = f (x + d) := ih.2

/-- An antiperiodic power-of-two orbit cannot contain an active forbidden-distance pair. -/
theorem power_two_orbit_exclusion (f : ℤ → ℤ) (k d : ℕ)
    (hd : 0 < d) (hdn : d < 2 ^ k)
    (ha : Function.Antiperiodic f ((2 ^ k : ℕ) : ℤ))
    (hz : ∀ y, f y ≠ 0 → f (y - d) = f (y + d)) (x : ℤ) :
    f x = 0 ∨ f (x + d) = 0 := by
  by_contra h
  push Not at h
  obtain ⟨e, m, hm, hdm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : d ≠ 0)
    2 (by omega)
  have hmpos : 0 < m := by
    by_contra hmzero
    have : m = 0 := by omega
    simp [this] at hdm
    omega
  have hpowle : 2 ^ e ≤ d := by
    rw [hdm]
    nlinarith [Nat.two_pow_pos e]
  have hek : e < k := by
    by_contra hek
    have := Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega : k ≤ e)
    omega
  have hpowe : 2 ^ k = 2 * 2 ^ (k - e - 1) * 2 ^ e := by
    have hexp : k = (k - e - 1) + e + 1 := by omega
    conv_lhs => rw [hexp]
    rw [pow_succ, pow_add]
    ring
  have hdist : ((2 ^ k : ℕ) : ℤ) * m =
      (2 * ((2 ^ (k - e - 1) : ℕ) : ℤ)) * d := by
    exact_mod_cast (show 2 ^ k * m = (2 * 2 ^ (k - e - 1)) * d by rw [hpowe, hdm]; ring)
  have hp := (active_pair_propagation f d x hz h.1 h.2 (2 ^ (k - e - 1))).1
  have hodd : Odd m := Nat.not_even_iff_odd.mp (fun he => hm he.two_dvd)
  have hant : f (x + (m : ℤ) * ((2 ^ k : ℕ) : ℤ)) = -f x := by
    simpa [hodd.neg_one_pow] using ha.add_nat_mul_eq (x := x) m
  have : f x = -f x := by
    calc
      f x = f (x + (2 * ((2 ^ (k - e - 1) : ℕ) : ℤ)) * d) := hp.symm
      _ = f (x + (m : ℤ) * ((2 ^ k : ℕ) : ℤ)) := by rw [← hdist, _root_.mul_comm]
      _ = -f x := hant
  have : f x = 0 := by omega
  exact h.1 this

/-- A unit monomial acts by the lift at the difference of the two indices. -/
theorem monomial_mul_apply_lift {n : ℕ} (e i : Fin n) (σ : Coeff n) :
    mul (monomial e 1) σ i = lift σ ((i.val : ℤ) - e.val) := by
  have hn : 0 < n := by have := i.isLt; omega
  let : NeZero n := ⟨by omega⟩
  obtain ⟨j, rfl⟩ := (Equiv.addLeft e).surjective i
  have hj : mul (monomial e 1) σ (e + j) =
      (if e.val + j.val < n then 1 else -1) * σ j := by
    rw [mul_monomial_left]
    rw [Finset.sum_eq_single j]
    · simp [Fin.val_add]
    · intro b _ hbj
      have hne : (e.val + b.val) % n ≠ (e + j).val := by
        intro he
        have : e + b = e + j := Fin.ext (by simpa [Fin.val_add] using he)
        exact hbj (add_left_cancel this)
      simp [hne]
    · simp
  change mul (monomial e 1) σ (e + j) = lift σ ((e + j).val - (e.val : ℤ))
  rw [hj]
  by_cases h : e.val + j.val < n
  · have hv : (e + j).val = e.val + j.val := by simp [Fin.val_add, Nat.mod_eq_of_lt h]
    rw [hv]
    have hdiff : ((e.val + j.val : ℕ) : ℤ) - e.val = j.val := by omega
    simp [h]
  · have hv : (e + j).val = e.val + j.val - n := by
      rw [Fin.val_add, Nat.mod_eq_sub_mod (by omega : n ≤ e.val + j.val)]
      rw [Nat.mod_eq_of_lt (by omega)]
    have hdiff : (((e + j).val : ℤ) - e.val) = j.val + (-1 : ℤ) * n := by
      rw [hv]; omega
    rw [hdiff, lift_add_mul]
    simp [h, signZ]

/-- Arbitrary integer powers act by signed shifts, including negative powers. -/
theorem mul_xpow_apply {n : ℕ} (hn : 0 < n) (k : ℤ) (σ : Coeff n) (i : Fin n) :
    mul (xpow n k) σ i = lift σ ((i.val : ℤ) - k) := by
  let e : Fin n := ⟨(k % n).toNat, by
    exact (Int.toNat_lt (Int.emod_nonneg k (by omega))).mpr
      (Int.emod_lt_of_pos k (by omega))⟩
  have he : (e.val : ℤ) = k % n := Int.toNat_of_nonneg (Int.emod_nonneg k (by omega))
  have hx : xpow n k = signZ (k / n) • monomial e 1 := by
    ext r
    simp only [xpow, Pi.smul_apply, smul_eq_mul, monomial]
    have heq : (k % n).toNat = r.val ↔ r = e := by simp [Fin.ext_iff, e, eq_comm]
    simp only [heq]
    split_ifs <;> simp
  rw [hx, mul_smul_left]
  change signZ (k / n) * mul (monomial e 1) σ i = _
  rw [monomial_mul_apply_lift]
  have hk : (i.val : ℤ) - k = ((i.val : ℤ) - e.val) + (-(k / n)) * n := by
    rw [he]
    have hdiv := Int.emod_add_ediv_mul k n
    linarith
  rw [hk, lift_add_mul, signZ_neg]

/-- Convolution is a sum of lifted signed shifts. -/
theorem mul_apply_lift {n : ℕ} (a σ : Coeff n) (i : Fin n) :
    mul a σ i = ∑ j, a j * lift σ ((i.val : ℤ) - j.val) := by
  have ha : a = ∑ j : Fin n, a j • monomial j 1 := by
    ext r
    simp [Finset.sum_apply, monomial]
  conv_lhs => rw [ha, mul_sum_left]
  simp only [Finset.sum_apply, mul_smul_left, Pi.smul_apply, smul_eq_mul,
    monomial_mul_apply_lift]

/-- The convolution operator is bounded by its coefficient one-norm on the unit cube. -/
theorem abs_mul_le_coeffL1 {n : ℕ} (a : Coeff n) {σ : Coeff n}
    (hσ : Power2ModuleSVP.Cube σ) (i : Fin n) : |mul a σ i| ≤ coeffL1 a := by
  rw [mul_apply_lift]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left (abs_lift_le (by omega) hσ _) (abs_nonneg (a j))

/-- The coefficient pairing transposes a shift by reversing its exponent. -/
theorem sum_pair_monomial {n : ℕ} (e : Fin n) (a b : Coeff n) :
    (∑ i, a i * mul (monomial e 1) b i) =
      ∑ j, mul (xpow n (-(e.val : ℤ))) a j * b j := by
  have hn : 0 < n := by have := e.isLt; omega
  let : NeZero n := ⟨by omega⟩
  symm
  apply Fintype.sum_equiv (Equiv.addLeft e)
  intro j
  change mul (xpow n (-(e.val : ℤ))) a j * b j =
    a (e + j) * mul (monomial e 1) b (e + j)
  rw [monomial_mul_apply_lift, mul_xpow_apply hn]
  let q : ℤ := ((e.val + j.val : ℕ) : ℤ) / n
  have hrem : ((e + j).val : ℤ) = ((e.val : ℤ) + j.val) % n := by
    simp [Fin.val_add, Int.natCast_emod, Nat.cast_add]
  have heq : (e.val : ℤ) + j.val = (e + j).val + q * n := by
    rw [hrem]
    exact (Int.emod_add_ediv_mul _ _).symm
  have h1 : ((e + j).val : ℤ) - e.val = j.val + (-q) * n := by linarith
  have h2 : (j.val : ℤ) - -(e.val : ℤ) = (e + j).val + q * n := by linarith
  rw [h1, h2, lift_add_mul, lift_add_mul, lift_coe, lift_coe, signZ_neg]
  ring

/-- The field sum of a skew monomial difference vanishes integrally. -/
theorem sum_skew_xpow {n d : ℕ} (hd : d < n) (σ : Coeff n) :
    (∑ i, σ i * mul (xpow n d - xpow n (-(d : ℤ))) σ i) = 0 := by
  have hs := sum_pair_monomial (⟨d, hd⟩ : Fin n) σ σ
  rw [← xpow_of_lt hd] at hs
  simp only [Power2ModuleSVP.coeff_mul_sub_left, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]
  have hs' : (∑ i, σ i * mul (xpow n d) σ i) =
      ∑ i, σ i * mul (xpow n (-(d : ℤ))) σ i := by
    simpa only [_root_.mul_comm] using hs
  exact sub_eq_zero.mpr hs'

/-- At the antipode, the skew difference has coefficient two rather than zero. -/
theorem xpow_antipodal {n d : ℕ} (hn : 0 < n) (hnd : n = 2 * d) :
    xpow n d - xpow n (-(d : ℤ)) = (2 : ℤ) • xpow n d := by
  have hexp : -(d : ℤ) + n = d := by exact_mod_cast (show -((d : ℤ)) + n = d by omega)
  have hx := xpow_add_degree hn (-(d : ℤ))
  rw [hexp] at hx
  rw [hx]
  ext i
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The balanced base-five uniqueness lemma indexed by a finite type. -/
theorem balanced_five_fin_zero {s : ℕ} (u : Fin s → ℤ)
    (hu : ∀ j, -2 ≤ u j ∧ u j ≤ 2)
    (hs : ∑ j, (5 : ℤ) ^ j.val * u j = 0) : ∀ j, u j = 0 := by
  let v : ℕ → ℤ := fun j => if hj : j < s then u ⟨j, hj⟩ else 0
  have hv : ∀ j < s, -2 ≤ v j ∧ v j ≤ 2 := by
    intro j hj
    simpa [v, hj] using hu ⟨j, hj⟩
  have hsum : ∑ j ∈ Finset.range s, (5 : ℤ) ^ j * v j = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa [v] using hs
  intro j
  simpa [v, j.isLt] using balanced_five_zero s v hv hsum j.val j.isLt

/-- Within an interval shorter than the degree, a signed monomial has no aliases. -/
theorem lift_xpow_near {n : ℕ} (hn : 0 < n) (e k : ℤ) (hek : |e - k| < (n : ℤ)) :
    lift (xpow n k) e = if e = k then 1 else 0 := by
  by_cases heq : e = k
  · subst e
    simp only [lift, dite_eq_left hn, xpow]
    exact signZ_sq _
  · have hmod : (k % n).toNat ≠ (e % n).toNat := by
      intro hc
      have hr : k % n = e % n := by
        have hk0 := Int.emod_nonneg k (by omega : (n : ℤ) ≠ 0)
        have he0 := Int.emod_nonneg e (by omega : (n : ℤ) ≠ 0)
        omega
      have hdvd : (n : ℤ) ∣ e - k := by
        apply Int.dvd_of_emod_eq_zero
        rw [Int.sub_emod, ← hr, sub_self, Int.zero_emod]
      have hsmall : (e - k).natAbs < (n : ℤ).natAbs := by
        have hnabs : |(n : ℤ)| = n := abs_of_pos (by omega)
        have := hek
        rw [← Int.natCast_natAbs, ← hnabs, ← Int.natCast_natAbs] at this
        exact_mod_cast this
      have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hsmall
      exact heq (by omega)
    simp [lift, hn, xpow, hmod, heq]

/-- The weighted antipodal guard coefficient is twice its weight. -/
theorem antipodal_guard_coefficient {n d : ℕ} (hn : 0 < n) (hnd : n = 2 * d)
    (w : ℤ) :
    (w • (xpow n d - xpow n (-(d : ℤ))))
      ⟨d, by omega⟩ = 2 * w := by
  rw [xpow_antipodal hn hnd, xpow_of_lt (show d < n by omega)]
  simp only [Pi.smul_apply, smul_eq_mul, monomial_self]
  ring

end Power2IdealSVP.Spin
