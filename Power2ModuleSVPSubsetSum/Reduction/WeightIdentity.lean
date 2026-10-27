import Power2ModuleSVPSubsetSum.Reduction.Boolean
import Power2ModuleSVPSubsetSum.Rigidity.Filter

/-! # The two equality-test coefficients

The Laurent weight word pairs diagonally with a Boolean word at coefficient zero,
and has no half-degree coefficient. These are the coefficient identities behind Lemma 4.1.

Paper: `paper/power2svp-subsetsum.pdf`, Lemma 4.1.
-/

namespace Power2ModuleSVPSubsetSum.Reduction
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- Coefficient formula for the executable Laurent weight word. -/
theorem ofList_weights (n : ℕ) (w : List ℕ) :
    IdealCVP.ofList (d := n) (weights n w) =
      fun i => if i.val = 0 then (w.getD 0 0 : ℤ) else -(w.getD (n - i.val) 0 : ℤ) := by
  ext i
  simp [IdealCVP.ofList, weights, List.getD_eq_getElem?_getD, i.isLt]

/-- The centered Boolean word is a sum of monomials at the weight positions. -/
theorem centeredWord_eq_sparse {n s : ℕ} (hs : s ≤ n) (ξ : Fin s → Bool) :
    (2 : ℤ) • booleanWord hs ξ - IdealCVP.ofList (mask n s) =
      sparse (fun j : Fin s => (⟨j.val, lt_of_lt_of_le j.isLt hs⟩ : Fin n))
        (fun j => 2 * (if ξ j then 1 else 0) - 1) := by
  let e : Fin s → Fin n := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hs⟩
  have he : Function.Injective e := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin n => x.val) h)
  rw [ofList_mask]
  ext i
  by_cases hi : i.val < s
  · have hat := sparse_at he (fun j => 2 * (if ξ j then 1 else 0) - 1) ⟨i.val, hi⟩
    simpa [booleanWord, hi, e] using hat.symm
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, booleanWord, dite_eq_right hi,
      ite_eq_right hi, MulZeroClass.mul_zero, sub_zero, sparse_apply]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hne : i ≠ (⟨j.val, lt_of_lt_of_le j.isLt hs⟩ : Fin n) := by
      intro h
      have hval := congrArg Fin.val h
      have hj := j.isLt
      change i.val = j.val at hval
      omega
    simp [hne]

/-- A weight monomial has exactly its own diagonal contribution at coefficient zero. -/
theorem weights_mul_monomial_zero {m : ℕ} (hm : 0 < m) (w : List ℕ)
    (hw : w.length ≤ m) (j : Fin w.length) (c : ℤ) :
    mul (IdealCVP.ofList (d := 2 * m) (weights (2 * m) w))
      (monomial ⟨j.val, by omega⟩ c) ⟨0, by omega⟩ = (w.get j : ℤ) * c := by
  rw [mul_comm, mul_monomial_left, ofList_weights]
  by_cases hj : j.val = 0
  · rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (2 * m))]
    · simp [hj, hm, show 0 < w.length by omega, _root_.mul_comm]
    · intro k _ hk
      have hkv : k.val ≠ 0 := by
        intro h
        exact hk (Fin.ext h)
      simp [hj, Nat.mod_eq_of_lt k.isLt, hkv]
    · simp
  · let k : Fin (2 * m) := ⟨2 * m - j.val, by omega⟩
    rw [Finset.sum_eq_single k]
    · have he : j.val + k.val = 2 * m := by dsimp [k]; omega
      have hk : k.val ≠ 0 := by dsimp [k]; omega
      have hk' : 2 * m - k.val = j.val := by dsimp [k]; omega
      simp only [he, Nat.mod_self, ite_true, lt_self_iff_false, ite_false, hk,
        hk', List.getD_eq_getElem w 0 j.isLt]
      simp [List.get_eq_getElem, _root_.mul_comm]
    · intro l _ hl
      have hne : l.val ≠ 2 * m - j.val := by
        intro h
        exact hl (Fin.ext h)
      have hmod : (j.val + l.val) % (2 * m) ≠ 0 := by
        have hlt : j.val + l.val < 2 * (2 * m) := by omega
        have hcases := Nat.mod_add_div (j.val + l.val) (2 * m)
        by_cases h : j.val + l.val < 2 * m
        · rw [Nat.mod_eq_of_lt h]
          omega
        · rw [show j.val + l.val = 2 * m + (j.val + l.val - 2 * m) by omega]
          simp only [Nat.add_mod_left]
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
      simp [hmod]
    · simp

/-- No weight monomial can contribute at half-degree. -/
theorem weights_mul_monomial_half {m : ℕ} (hm : 0 < m) (w : List ℕ)
    (hw : w.length ≤ m) (j : Fin w.length) (c : ℤ) :
    mul (IdealCVP.ofList (d := 2 * m) (weights (2 * m) w))
      (monomial ⟨j.val, by omega⟩ c) ⟨m, by omega⟩ = 0 := by
  rw [mul_comm, mul_monomial_left, ofList_weights]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hmod : (j.val + k.val) % (2 * m) = m
  · have he : k.val = m - j.val := by
      by_cases h : j.val + k.val < 2 * m
      · rw [Nat.mod_eq_of_lt h] at hmod
        omega
      · rw [show j.val + k.val = 2 * m + (j.val + k.val - 2 * m) by omega]
          at hmod
        simp only [Nat.add_mod_left] at hmod
        rw [Nat.mod_eq_of_lt (by omega)] at hmod
        omega
    have hk : k.val ≠ 0 := by omega
    have hfar : w.length ≤ 2 * m - k.val := by omega
    dsimp only
    rw [List.getD_eq_default w 0 hfar]
    simp [hmod, hk]
  · simp [hmod]

/-- The constant coefficient computes the centered weighted Boolean sum. -/
theorem weights_centered_zero {m : ℕ} (hm : 0 < m) (w : List ℕ)
    (hw : w.length ≤ m) (ξ : Fin w.length → Bool) :
    mul (IdealCVP.ofList (d := 2 * m) (weights (2 * m) w))
      ((2 : ℤ) • booleanWord (by omega : w.length ≤ 2 * m) ξ -
        IdealCVP.ofList (mask (2 * m) w.length)) ⟨0, by omega⟩ =
      2 * (∑ j : Fin w.length, (w.get j : ℤ) * (if ξ j then 1 else 0)) -
        (w.sum : ℤ) := by
  rw [centeredWord_eq_sparse, sparse, mul_sum_right]
  simp only [Finset.sum_apply, weights_mul_monomial_zero hm w hw]
  have hsum : (∑ j : Fin w.length, (w.get j : ℤ)) = (w.sum : ℤ) := by
    exact_mod_cast (Fin.sum_univ_getElem w)
  rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The half-degree coefficient of the Laurent product vanishes. -/
theorem weights_centered_half {m : ℕ} (hm : 0 < m) (w : List ℕ)
    (hw : w.length ≤ m) (ξ : Fin w.length → Bool) :
    mul (IdealCVP.ofList (d := 2 * m) (weights (2 * m) w))
      ((2 : ℤ) • booleanWord (by omega : w.length ≤ 2 * m) ξ -
        IdealCVP.ofList (mask (2 * m) w.length)) ⟨m, by omega⟩ = 0 := by
  rw [centeredWord_eq_sparse, sparse, mul_sum_right]
  simp only [Finset.sum_apply, weights_mul_monomial_half hm w hw, Finset.sum_const_zero]

/-- The stored adjoint filter is the difference of the two opposite monomials. -/
theorem ofList_filterDStar {m : ℕ} (hm : 0 < m) :
    IdealCVP.ofList (d := 2 * m) (filterDStar m) =
      coeffOne (by omega) - Rigidity.atom (2 * m) m := by
  ext i
  simp only [IdealCVP.ofList, filterDStar, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range i.isLt, Option.map_some, Option.getD_some,
    coeffOne, monomial, Rigidity.atom, Pi.sub_apply, Fin.ext_iff]
  split_ifs <;> simp_all

/-- Applying `D*` gives the first equality-test coefficient. -/
theorem H_centered_zero {m : ℕ} (hm : 0 < m) (w : List ℕ)
    (hw : w.length ≤ m) (ξ : Fin w.length → Bool) :
    mul (mul (IdealCVP.ofList (d := 2 * m) (filterDStar m))
      (IdealCVP.ofList (weights (2 * m) w)))
      ((2 : ℤ) • booleanWord (by omega : w.length ≤ 2 * m) ξ -
        IdealCVP.ofList (mask (2 * m) w.length)) ⟨0, by omega⟩ =
      2 * (∑ j : Fin w.length, (w.get j : ℤ) * (if ξ j then 1 else 0)) -
        (w.sum : ℤ) := by
  rw [coeff_mul_assoc (by omega), ofList_filterDStar hm, coeff_mul_sub_left,
    mul_coeffOne]
  simp only [Pi.sub_apply]
  rw [Rigidity.half_mul_low hm _ ⟨0, hm⟩]
  simp only [zero_add]
  rw [weights_centered_zero hm w hw, weights_centered_half hm w hw]
  simp

/-- The second equality-test coefficient is the negative of the first. -/
theorem H_centered_half {m : ℕ} (hm : 0 < m) (w : List ℕ)
    (hw : w.length ≤ m) (ξ : Fin w.length → Bool) :
    mul (mul (IdealCVP.ofList (d := 2 * m) (filterDStar m))
      (IdealCVP.ofList (weights (2 * m) w)))
      ((2 : ℤ) • booleanWord (by omega : w.length ≤ 2 * m) ξ -
        IdealCVP.ofList (mask (2 * m) w.length)) ⟨m, by omega⟩ =
      -(2 * (∑ j : Fin w.length, (w.get j : ℤ) * (if ξ j then 1 else 0)) -
        (w.sum : ℤ)) := by
  rw [coeff_mul_assoc (by omega), ofList_filterDStar hm, coeff_mul_sub_left,
    mul_coeffOne]
  simp only [Pi.sub_apply]
  have hshift (f : Coeff (2 * m)) :
      mul (Rigidity.atom (2 * m) m) f ⟨m, by omega⟩ = f ⟨0, by omega⟩ := by
    simpa only [zero_add] using Rigidity.half_mul_high hm f ⟨0, hm⟩
  rw [hshift]
  rw [weights_centered_zero hm w hw, weights_centered_half hm w hw]
  simp

end Power2ModuleSVPSubsetSum.Reduction
