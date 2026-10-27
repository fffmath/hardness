import Power2ModuleSVPSubsetSum.Rigidity.Filter
import Power2ModuleSVPSubsetSum.Algebra.Norms

/-! # Balanced digits and support rigidity

The balanced base-five separation argument used to distinguish all the skew shifts.

Paper: `paper/power2svp-subsetsum.pdf`, Section 3, Lemma 3.2.
-/
namespace Power2ModuleSVPSubsetSum.Rigidity
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- Evaluate a list of balanced base-five digits, with the lowest digit first. -/
def balancedFive (digits : List ℤ) : ℤ := digits.foldr (fun a b => a + 5 * b) 0

/-- Balanced digits in `[-2,2]` cannot sum to zero unless every digit is zero. -/
theorem balancedFive_eq_zero_iff (digits : List ℤ)
    (hbound : ∀ a ∈ digits, |a| ≤ 2) :
    balancedFive digits = 0 ↔ ∀ a ∈ digits, a = 0 := by
  induction digits with
  | nil => simp [balancedFive]
  | cons a digits ih =>
    have ha := abs_le.mp (hbound a (by simp))
    have ht : ∀ b ∈ digits, |b| ≤ 2 := fun b hb => hbound b (by simp [hb])
    change a + 5 * balancedFive digits = 0 ↔ _
    rw [List.forall_mem_cons]
    constructor
    · intro h
      have hz : a = 0 := by omega
      refine ⟨hz, (ih ht).mp ?_⟩
      omega
    · rintro ⟨rfl, h⟩
      rw [(ih ht).mpr h]
      omega

/-- Finite-sum version of balanced base-five uniqueness. -/
theorem sum_five_pow_eq_zero {k : ℕ} (c : Fin k → ℤ)
    (hbound : ∀ i, |c i| ≤ 2) (hsum : ∑ i, (5 ^ i.val : ℤ) * c i = 0) :
    ∀ i, c i = 0 := by
  induction k with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
    have he : c 0 + 5 * (∑ i : Fin k, (5 ^ i.val : ℤ) * c i.succ) = 0 := by
      simpa [Fin.sum_univ_succ, pow_succ, Finset.mul_sum, _root_.mul_assoc,
        _root_.mul_left_comm, _root_.mul_comm] using hsum
    have hb := abs_le.mp (hbound 0)
    have hz : c 0 = 0 := by omega
    have ht : ∑ i : Fin k, (5 ^ i.val : ℤ) * c i.succ = 0 := by omega
    have hc := ih (fun i => c i.succ) (fun i => hbound i.succ) ht
    intro i
    refine Fin.cases hz (fun j => hc j) i

/-- One vanishing base-five filter coefficient forces every skew-shift test to vanish. -/
theorem K_mul_zero_tests {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m))
    (hb : coeffSup b ≤ 1) (i : Fin (2 * m)) (hi : mul (K m) b i = 0) :
    ∀ d : Fin (m - 1), mul (S m (d.val + 1)) b i = 0 := by
  apply sum_five_pow_eq_zero
  · intro d
    have hd := d.isLt
    have hsup : coeffSup (mul (S m (d.val + 1)) b) ≤ 2 := by
      rw [S, mul_add_left, atom_eq_monomial (by omega),
        atom_eq_monomial (by omega)]
      exact (coeffSup_add_le _ _).trans (by
        rw [coeffSup_monomial_mul, coeffSup_monomial_mul]
        omega)
    have h := (natAbs_le_coeffSup (mul (S m (d.val + 1)) b) i).trans hsup
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  · rw [K, mul_sum_left] at hi
    simpa only [mul_smul_left, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hi

/-- The lower-half skew test is a difference of the two samples at distance `d`. -/
theorem S_mul_low {m d : ℕ} (hd : 0 < d) (hdm : d < m)
    (b : Coeff (2 * m)) (j : Fin m) :
    mul (S m d) b ⟨j.val, by omega⟩ =
      (if h : d ≤ j.val then b ⟨j.val - d, by omega⟩
        else -b ⟨2 * m + j.val - d, by omega⟩) - b ⟨j.val + d, by omega⟩ := by
  rw [S, mul_add_left, atom_eq_monomial (by omega), atom_eq_monomial (by omega)]
  simp only [Pi.add_apply, monomial_mul_apply]
  rw [dite_eq_right (by omega : ¬2 * m - d ≤ j.val)]
  have he : (⟨2 * m + j.val - (2 * m - d), by omega⟩ : Fin (2 * m)) =
      ⟨j.val + d, by omega⟩ := by apply Fin.ext; dsimp; omega
  rw [he]
  rfl

/-- The complementary skew test at the upper partner is the sum of the same samples. -/
theorem S_mul_high_complement {m d : ℕ} (hd : 0 < d) (hdm : d < m)
    (b : Coeff (2 * m)) (j : Fin m) :
    mul (S m (m - d)) b ⟨j.val + m, by omega⟩ =
      b ⟨j.val + d, by omega⟩ +
      (if h : d ≤ j.val then b ⟨j.val - d, by omega⟩
        else -b ⟨2 * m + j.val - d, by omega⟩) := by
  rw [S, mul_add_left, atom_eq_monomial (by omega), atom_eq_monomial (by omega)]
  simp only [Pi.add_apply, monomial_mul_apply]
  rw [dite_eq_left (by omega : m - d ≤ j.val + m)]
  have he : (⟨j.val + m - (m - d), by omega⟩ : Fin (2 * m)) =
      ⟨j.val + d, by omega⟩ := by apply Fin.ext; dsimp; omega
  rw [he]
  split_ifs with h h' h'
  all_goals try omega
  · congr 2
    apply Fin.ext
    dsimp
    omega
  · congr 2
    congr 1
    apply Fin.ext
    dsimp
    omega

private theorem tests_force_samples {m d : ℕ} (hd : 0 < d) (hdm : d < m)
    (b : Coeff (2 * m)) (j : Fin m)
    (hl : mul (S m d) b ⟨j.val, by omega⟩ = 0)
    (hh : mul (S m (m - d)) b ⟨j.val + m, by omega⟩ = 0) :
    (if h : d ≤ j.val then b ⟨j.val - d, by omega⟩
      else -b ⟨2 * m + j.val - d, by omega⟩) = 0 ∧
      b ⟨j.val + d, by omega⟩ = 0 := by
  rw [S_mul_low hd hdm] at hl
  rw [S_mul_high_complement hd hdm] at hh
  constructor <;> omega

private theorem pair_support {m : ℕ} (b : Coeff (2 * m)) (j : Fin m)
    (ht : ∀ d, 0 < d → d < m →
      mul (S m d) b ⟨j.val, by omega⟩ = 0 ∧
      mul (S m (m - d)) b ⟨j.val + m, by omega⟩ = 0) :
    ∀ i : Fin (2 * m), i.val ≠ j.val → i.val ≠ j.val + m → b i = 0 := by
  intro i hlow hhigh
  by_cases hij : i.val < j.val
  · obtain ⟨hl, hh⟩ := ht (j.val - i.val) (by omega) (by omega)
    have h := (tests_force_samples (by omega) (by omega) b j hl hh).1
    rw [dite_eq_left (by omega)] at h
    convert h using 1
    congr 1
    apply Fin.ext
    dsimp
    omega
  · by_cases hijm : i.val < j.val + m
    · obtain ⟨hl, hh⟩ := ht (i.val - j.val) (by omega) (by omega)
      have h := (tests_force_samples (by omega) (by omega) b j hl hh).2
      convert h using 1
      congr 1
      apply Fin.ext
      dsimp
      omega
    · obtain ⟨hl, hh⟩ := ht (2 * m + j.val - i.val) (by omega) (by omega)
      have h := (tests_force_samples (by omega) (by omega) b j hl hh).1
      rw [dite_eq_right (by omega)] at h
      have he : (⟨2 * m + j.val - (2 * m + j.val - i.val), by omega⟩ :
          Fin (2 * m)) = i := by apply Fin.ext; dsimp; omega
      rw [he] at h
      exact neg_eq_zero.mp h

/-- Lemma 3.2: the only multipliers surviving the occupied-pair tests are signed monomials. -/
theorem support_rigidity {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m))
    (hD : coeffSup (mul (D m) b) ≤ 1)
    (hK : ∀ j : Fin m,
      (b ⟨j.val, by omega⟩ ≠ 0 ∨ b ⟨j.val + m, by omega⟩ ≠ 0) →
      mul (K m) b ⟨j.val, by omega⟩ = 0 ∧
      mul (K m) b ⟨j.val + m, by omega⟩ = 0) :
    b = 0 ∨ SignedMonomial b := by
  by_cases hb : b = 0
  · exact Or.inl hb
  right
  have hsup : coeffSup b ≤ 1 := (coeffSup_le_D_mul hm b).trans hD
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra! h
    exact hb (funext h)
  let j : Fin m := ⟨if i.val < m then i.val else i.val - m, by split_ifs <;> omega⟩
  have hi_pair : i.val = j.val ∨ i.val = j.val + m := by
    dsimp [j]
    split_ifs <;> omega
  have hocc : b ⟨j.val, by omega⟩ ≠ 0 ∨ b ⟨j.val + m, by omega⟩ ≠ 0 := by
    rcases hi_pair with he | he
    · left
      simpa [show (⟨j.val, by omega⟩ : Fin (2 * m)) = i from Fin.ext he.symm]
        using hi
    · right
      simpa [show (⟨j.val + m, by omega⟩ : Fin (2 * m)) = i from Fin.ext he.symm]
        using hi
  obtain ⟨hkl, hkh⟩ := hK j hocc
  have htests := K_mul_zero_tests hm b hsup _ hkl
  have htesth := K_mul_zero_tests hm b hsup _ hkh
  have ht : ∀ d, 0 < d → d < m →
      mul (S m d) b ⟨j.val, by omega⟩ = 0 ∧
      mul (S m (m - d)) b ⟨j.val + m, by omega⟩ = 0 := by
    intro d hd hdm
    constructor
    · simpa [show d - 1 + 1 = d by omega] using
        htests ⟨d - 1, by omega⟩
    · simpa [show m - d - 1 + 1 = m - d by omega] using
        htesth ⟨m - d - 1, by omega⟩
  have hout := pair_support b j ht
  have hmass : |b ⟨j.val, by omega⟩| + |b ⟨j.val + m, by omega⟩| ≤ 1 :=
    (pair_mass_le hm b j).trans (by exact_mod_cast hD)
  have hclass :
      (b ⟨j.val, by omega⟩ = 1 ∨ b ⟨j.val, by omega⟩ = -1) ∧
        b ⟨j.val + m, by omega⟩ = 0 ∨
      (b ⟨j.val + m, by omega⟩ = 1 ∨ b ⟨j.val + m, by omega⟩ = -1) ∧
        b ⟨j.val, by omega⟩ = 0 := by
    have h1 := abs_le.mp (show |b ⟨j.val, by omega⟩| ≤ 1 from
      (le_add_of_nonneg_right (abs_nonneg _)).trans hmass)
    have h2 := abs_le.mp (show |b ⟨j.val + m, by omega⟩| ≤ 1 from
      (le_add_of_nonneg_left (abs_nonneg _)).trans hmass)
    rcases hocc with h | h
    · left
      have he : b ⟨j.val, by omega⟩ = 1 ∨ b ⟨j.val, by omega⟩ = -1 := by omega
      refine ⟨he, ?_⟩
      rcases he with he | he <;> simp [he] at hmass <;> omega
    · right
      have he : b ⟨j.val + m, by omega⟩ = 1 ∨ b ⟨j.val + m, by omega⟩ = -1 := by omega
      refine ⟨he, ?_⟩
      rcases he with he | he <;> simp [he] at hmass <;> omega
  have hex : ∃ t : Fin (2 * m), (b t = 1 ∨ b t = -1) ∧
      ∀ r : Fin (2 * m), r ≠ t → b r = 0 := by
    rcases hclass with ⟨hs, hz⟩ | ⟨hs, hz⟩
    · refine ⟨⟨j.val, by omega⟩, hs, ?_⟩
      intro r hr
      have hrl : r.val ≠ j.val := by
        intro h
        exact hr (Fin.ext h)
      by_cases hrh : r.val = j.val + m
      · exact (congrArg b (Fin.ext hrh)).trans hz
      · exact hout r hrl hrh
    · refine ⟨⟨j.val + m, by omega⟩, hs, ?_⟩
      intro r hr
      have hrh : r.val ≠ j.val + m := by
        intro h
        exact hr (Fin.ext h)
      by_cases hrl : r.val = j.val
      · exact (congrArg b (Fin.ext hrl)).trans hz
      · exact hout r hrl hrh
  obtain ⟨t, hs, hout'⟩ := hex
  refine ⟨t, ?_⟩
  rcases hs with hs | hs
  · left
    ext r
    by_cases hr : r = t
    · subst r
      simpa using hs
    · simp [monomial, hr, hout' r hr]
  · right
    ext r
    by_cases hr : r = t
    · subst r
      simpa using hs
    · simp [monomial, hr, hout' r hr]

end Power2ModuleSVPSubsetSum.Rigidity
