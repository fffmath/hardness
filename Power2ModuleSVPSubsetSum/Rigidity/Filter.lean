import Power2ModuleSVP.Coset.ParityBlock

/-! # The opposite-pair filter

Explicit filter polynomials and the opposite-pair identities in the negacyclic coefficient
model. These identities hold for every positive half-degree, without a dyadic assumption.

Paper: `paper/power2svp-subsetsum.pdf`, Section 3, Lemma 3.1.
-/
namespace Power2ModuleSVPSubsetSum.Rigidity
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- A coefficient monomial specified by a natural exponent; out-of-range exponents vanish. -/
def atom (n k : ℕ) : Coeff n := fun i => if i.val = k then 1 else 0

/-- The opposite-pair filter `1 + X^m` in degree `2m`. -/
def D (m : ℕ) : Coeff (2 * m) := atom (2 * m) 0 + atom (2 * m) m

/-- The skew shift `X^d - X^(-d)`, represented by two positive coefficients. -/
def S (m d : ℕ) : Coeff (2 * m) := atom (2 * m) d + atom (2 * m) (2 * m - d)

/-- The balanced base-five sum of all skew shifts of distance less than `m`. -/
def K (m : ℕ) : Coeff (2 * m) :=
  ∑ d : Fin (m - 1), (5 ^ d.val : ℤ) • S m (d.val + 1)

/-- A natural-exponent monomial agrees with the existing finite-exponent monomial. -/
theorem atom_eq_monomial {n k : ℕ} (hk : k < n) :
    atom n k = monomial ⟨k, hk⟩ 1 := by
  ext i
  simp [atom, monomial, Fin.ext_iff]

private theorem half_mod {m : ℕ} (_hm : 0 < m) (i : Fin (2 * m)) :
    (m + i.val) % (2 * m) = if i.val < m then m + i.val else i.val - m := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [show m + i.val = 2 * m + (i.val - m) by omega]
    simp [Nat.mod_eq_of_lt (show i.val - m < 2 * m by omega)]

/-- Low-half coefficient of multiplication by the half-degree monomial. -/
theorem half_mul_low {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m)) (j : Fin m) :
    mul (atom (2 * m) m) b ⟨j.val, by omega⟩ =
      -b ⟨j.val + m, by omega⟩ := by
  rw [atom_eq_monomial (by omega), mul_monomial_left]
  rw [Finset.sum_eq_single (⟨j.val + m, by omega⟩ : Fin (2 * m))]
  · have he : (m + (j.val + m)) % (2 * m) = j.val := by
      rw [show m + (j.val + m) = 2 * m + j.val by omega]
      simp [Nat.mod_eq_of_lt (show j.val < 2 * m by omega)]
    simp [he, show ¬m + (j.val + m) < 2 * m by omega]
  · intro i _ hi
    have hne : i.val ≠ j.val + m := by
      intro h
      exact hi (Fin.ext h)
    have hmod := half_mod hm i
    have he : (m + i.val) % (2 * m) ≠ j.val := by
      split_ifs at hmod <;> omega
    simp [he]
  · simp

/-- High-half coefficient of multiplication by the half-degree monomial. -/
theorem half_mul_high {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m)) (j : Fin m) :
    mul (atom (2 * m) m) b ⟨j.val + m, by omega⟩ = b ⟨j.val, by omega⟩ := by
  rw [atom_eq_monomial (by omega), mul_monomial_left]
  rw [Finset.sum_eq_single (⟨j.val, by omega⟩ : Fin (2 * m))]
  · simp [Nat.mod_eq_of_lt (show m + j.val < 2 * m by omega),
      show m + j.val < 2 * m by omega, Nat.add_comm]
  · intro i _ hi
    have hne : i.val ≠ j.val := by
      intro h
      exact hi (Fin.ext h)
    have hmod := half_mod hm i
    have he : (m + i.val) % (2 * m) ≠ j.val + m := by
      split_ifs at hmod <;> omega
    simp [he]
  · simp

/-- Multiplication by `D` sends an opposite pair `(c,e)` to `(c-e,c+e)`. -/
theorem D_mul_low {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m)) (j : Fin m) :
    mul (D m) b ⟨j.val, by omega⟩ =
      b ⟨j.val, by omega⟩ - b ⟨j.val + m, by omega⟩ := by
  rw [D, mul_add_left]
  rw [atom_eq_monomial (by omega : 0 < 2 * m)]
  change (mul (coeffOne (by omega)) b + mul (atom (2 * m) m) b) _ = _
  simp [half_mul_low hm, sub_eq_add_neg]

/-- High coefficient of the opposite-pair map. -/
theorem D_mul_high {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m)) (j : Fin m) :
    mul (D m) b ⟨j.val + m, by omega⟩ =
      b ⟨j.val, by omega⟩ + b ⟨j.val + m, by omega⟩ := by
  rw [D, mul_add_left]
  rw [atom_eq_monomial (by omega : 0 < 2 * m)]
  change (mul (coeffOne (by omega)) b + mul (atom (2 * m) m) b) _ = _
  simp only [mul_coeffOne, Pi.add_apply]
  rw [half_mul_high hm]
  exact add_comm _ _

/-- The maximum of the two transformed absolute values equals the opposite-pair mass. -/
theorem max_abs_pair (c e : ℤ) : max |c - e| |c + e| = |c| + |e| := by
  rcases le_total 0 c with hc | hc <;> rcases le_total 0 e with he | he
  · rw [abs_of_nonneg hc, abs_of_nonneg he, abs_of_nonneg (by omega : 0 ≤ c + e)]
    exact max_eq_right (abs_le.mpr ⟨by omega, by omega⟩)
  · rw [abs_of_nonneg hc, abs_of_nonpos he, abs_of_nonneg (by omega : 0 ≤ c - e)]
    exact max_eq_left (abs_le.mpr ⟨by omega, by omega⟩)
  · have ha : |c - e| = -c + e := by rw [abs_of_nonpos (by omega)]; omega
    rw [abs_of_nonpos hc, abs_of_nonneg he, ha]
    exact max_eq_left (abs_le.mpr ⟨by omega, by omega⟩)
  · have ha : |c + e| = -c + -e := by rw [abs_of_nonpos (by omega)]; omega
    rw [abs_of_nonpos hc, abs_of_nonpos he, ha]
    exact max_eq_right (abs_le.mpr ⟨by omega, by omega⟩)

/-- The absolute mass of each opposite pair is bounded by the filter's maximum norm. -/
theorem pair_mass_le {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m)) (j : Fin m) :
    |b ⟨j.val, by omega⟩| + |b ⟨j.val + m, by omega⟩| ≤
      (coeffSup (mul (D m) b) : ℤ) := by
  rw [← max_abs_pair, ← D_mul_low hm, ← D_mul_high hm]
  apply max_le
  · rw [← Int.natCast_natAbs]
    exact_mod_cast (show _ ≤ coeffSup (mul (D m) b) from
      Finset.le_sup (f := fun i => ((mul (D m) b) i).natAbs)
        (Finset.mem_univ (⟨j.val, by omega⟩ : Fin (2 * m))))
  · rw [← Int.natCast_natAbs]
    exact_mod_cast (show _ ≤ coeffSup (mul (D m) b) from
      Finset.le_sup (f := fun i => ((mul (D m) b) i).natAbs)
        (Finset.mem_univ (⟨j.val + m, by omega⟩ : Fin (2 * m))))

/-- The filter never decreases the maximum coefficient norm. -/
theorem coeffSup_le_D_mul {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m)) :
    coeffSup b ≤ coeffSup (mul (D m) b) := by
  apply Finset.sup_le
  intro i _
  by_cases hi : i.val < m
  · have h := pair_mass_le hm b ⟨i.val, hi⟩
    dsimp only at h
    have he : (⟨i.val, by omega⟩ : Fin (2 * m)) = i := Fin.ext rfl
    rw [he] at h
    have ha : |b i| ≤ (coeffSup (mul (D m) b) : ℤ) := by
      have := abs_nonneg (b ⟨i.val + m, by omega⟩)
      omega
    rw [← Int.natCast_natAbs] at ha
    exact_mod_cast ha
  · have h := pair_mass_le hm b ⟨i.val - m, by omega⟩
    dsimp only at h
    have he : (⟨i.val - m + m, by omega⟩ : Fin (2 * m)) = i := by
      apply Fin.ext
      simp only
      omega
    rw [he] at h
    have ha : |b i| ≤ (coeffSup (mul (D m) b) : ℤ) := by
      have := abs_nonneg (b ⟨i.val - m, by omega⟩)
      omega
    rw [← Int.natCast_natAbs] at ha
    exact_mod_cast ha

/-- The skew filter has zero constant coefficient. -/
theorem K_zero {m : ℕ} (hm : 0 < m) : K m ⟨0, by omega⟩ = 0 := by
  simp only [K, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro d _
  have hd := d.isLt
  simp [S, atom, show (0 : ℕ) ≠ 2 * m - (d.val + 1) by omega]

/-- The skew filter has zero half-degree coefficient. -/
theorem K_half {m : ℕ} (hm : 0 < m) : K m ⟨m, by omega⟩ = 0 := by
  simp only [K, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro d _
  have hd := d.isLt
  simp [S, atom, show m ≠ d.val + 1 by omega,
    show m ≠ 2 * m - (d.val + 1) by omega]

/-- The product `DK` also vanishes at the constant coefficient. -/
theorem DK_zero {m : ℕ} (hm : 0 < m) : mul (D m) (K m) ⟨0, by omega⟩ = 0 := by
  simpa [K_zero hm, K_half hm] using D_mul_low hm (K m) ⟨0, hm⟩

/-- The product `DK` also vanishes at the half-degree coefficient. -/
theorem DK_half {m : ℕ} (hm : 0 < m) : mul (D m) (K m) ⟨m, by omega⟩ = 0 := by
  simpa [K_zero hm, K_half hm] using D_mul_high hm (K m) ⟨0, hm⟩

/-- Explicit coefficients of the base-five skew filter, suitable for list implementations. -/
theorem K_apply {m : ℕ} (i : Fin (2 * m)) :
    K m i = if 0 < i.val ∧ i.val < m then (5 : ℤ) ^ (i.val - 1)
      else if m < i.val then (5 : ℤ) ^ (2 * m - i.val - 1) else 0 := by
  by_cases hlo : 0 < i.val ∧ i.val < m
  · rw [ite_eq_left hlo]
    simp only [K, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (⟨i.val - 1, by omega⟩ : Fin (m - 1))]
    · simp only [S, atom, Pi.add_apply]
      rw [show i.val - 1 + 1 = i.val by omega]
      simp [show i.val ≠ 2 * m - i.val by omega]
    · intro d _ hd
      have hne : d.val ≠ i.val - 1 := by intro h; exact hd (Fin.ext h)
      have hdlt := d.isLt
      simp [S, atom, show i.val ≠ d.val + 1 by omega,
        show i.val ≠ 2 * m - (d.val + 1) by omega]
    · simp
  · rw [ite_eq_right hlo]
    by_cases hhi : m < i.val
    · rw [ite_eq_left hhi]
      simp only [K, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single (⟨2 * m - i.val - 1, by omega⟩ : Fin (m - 1))]
      · simp only [S, atom, Pi.add_apply]
        rw [show 2 * m - i.val - 1 + 1 = 2 * m - i.val by omega,
          show 2 * m - (2 * m - i.val) = i.val by omega]
        simp [show i.val ≠ 2 * m - i.val by omega]
      · intro d _ hd
        have hne : d.val ≠ 2 * m - i.val - 1 := by intro h; exact hd (Fin.ext h)
        have hdlt := d.isLt
        simp [S, atom, show i.val ≠ d.val + 1 by omega,
          show i.val ≠ 2 * m - (d.val + 1) by omega]
      · simp
    · rw [ite_eq_right hhi]
      simp only [K, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_eq_zero
      intro d _
      have hdlt := d.isLt
      simp [S, atom, show i.val ≠ d.val + 1 by omega,
        show i.val ≠ 2 * m - (d.val + 1) by omega]

end Power2ModuleSVPSubsetSum.Rigidity
