import Power2ModuleSVPSubsetSum.Rigidity.Filter
import Power2ModuleSVPSubsetSum.Algebra.Norms

/-! # Exact pair norm and filter size

The pair-norm formula and the base-five l1 bound for the rigidity filter.

Paper: `paper/power2svp-subsetsum.pdf`, Section 3, Lemma 3.1.
-/
namespace Power2ModuleSVPSubsetSum.Rigidity
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- Exact maximum-norm formula for the opposite-pair filter. -/
theorem coeffSup_D_mul {m : ℕ} (hm : 0 < m) (b : Coeff (2 * m)) :
    coeffSup (mul (D m) b) = Finset.univ.sup (fun j : Fin m =>
      (b ⟨j.val, by omega⟩).natAbs + (b ⟨j.val + m, by omega⟩).natAbs) := by
  apply Nat.le_antisymm
  · apply (coeffSup_le_iff _ _).mpr
    intro i
    by_cases hi : i.val < m
    · have he : (⟨i.val, by omega⟩ : Fin (2 * m)) = i := Fin.ext rfl
      have h := D_mul_low hm b ⟨i.val, hi⟩
      dsimp only at h
      rw [he] at h
      rw [h]
      exact (Int.natAbs_sub_le _ _).trans
        (Finset.le_sup (f := fun j : Fin m =>
          (b ⟨j.val, by omega⟩).natAbs + (b ⟨j.val + m, by omega⟩).natAbs)
          (Finset.mem_univ ⟨i.val, hi⟩))
    · have he : (⟨i.val - m + m, by omega⟩ : Fin (2 * m)) = i := by
        apply Fin.ext
        dsimp
        omega
      have h := D_mul_high hm b ⟨i.val - m, by omega⟩
      dsimp only at h
      rw [he] at h
      rw [h]
      have hs := Finset.le_sup (f := fun j : Fin m =>
        (b ⟨j.val, by omega⟩).natAbs + (b ⟨j.val + m, by omega⟩).natAbs)
        (Finset.mem_univ (⟨i.val - m, by omega⟩ : Fin m))
      dsimp only at hs
      rw [he] at hs
      exact (Int.natAbs_add_le _ _).trans hs
  · apply Finset.sup_le
    intro j _
    have h := pair_mass_le hm b j
    simpa only [← Int.natCast_natAbs, ← Nat.cast_add, Nat.cast_le] using h

private theorem coeffL1_atom {n k : ℕ} (hk : k < n) : coeffL1 (atom n k) = 1 := by
  rw [atom_eq_monomial hk]
  simp only [coeffL1, monomial, apply_ite Int.natAbs, Int.natAbs_one, Int.natAbs_zero]
  simp

private theorem four_sum_five (k : ℕ) :
    4 * (∑ i : Fin k, 5 ^ i.val) + 1 = 5 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ]
    rw [← Finset.sum_mul]
    omega

/-- The l1 norm of the parity filter is at most two. -/
theorem coeffL1_D_le (m : ℕ) : coeffL1 (D m) ≤ 2 := by
  by_cases hm : 0 < m
  · exact (coeffL1_add_le _ _).trans (by
      rw [coeffL1_atom (by omega), coeffL1_atom (by omega)])
  · have hz : m = 0 := by omega
    subst m
    simp [D, coeffL1]

/-- The l1 norm of a skew shift is at most two. -/
theorem coeffL1_S_le {m d : ℕ} (hd : 0 < d) (hdm : d < m) :
    coeffL1 (S m d) ≤ 2 := by
  exact (coeffL1_add_le _ _).trans (by
    rw [coeffL1_atom (by omega), coeffL1_atom (by omega)])

/-- Lemma 3.1's explicit base-five upper bound on `rho = ||DK||₁`. -/
theorem coeffL1_DK_le (m : ℕ) : coeffL1 (mul (D m) (K m)) ≤ 5 ^ (m - 1) - 1 := by
  have hk : coeffL1 (K m) ≤ 2 * (∑ d : Fin (m - 1), 5 ^ d.val) := by
    calc
      _ ≤ ∑ d : Fin (m - 1), coeffL1 ((5 ^ d.val : ℤ) • S m (d.val + 1)) :=
        coeffL1_sum_le _
      _ ≤ ∑ d : Fin (m - 1), 5 ^ d.val * 2 := by
        apply Finset.sum_le_sum
        intro d _
        rw [coeffL1_smul]
        simp only [Int.natAbs_pow]
        exact Nat.mul_le_mul_left _ (coeffL1_S_le (by omega) (by have := d.isLt; omega))
      _ = _ := by rw [← Finset.sum_mul]; omega
  have h := (coeffL1_mul_le (D m) (K m)).trans
    (Nat.mul_le_mul (coeffL1_D_le m) hk)
  have hg := four_sum_five (m - 1)
  omega

end Power2ModuleSVPSubsetSum.Rigidity
