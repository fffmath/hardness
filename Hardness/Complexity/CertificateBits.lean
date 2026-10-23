import Hardness.Complexity.Witness

/-! # An explicit polynomial bit bound for Cramer's certificate bound -/
namespace Hardness
open Turing.MultiTapeTM

/-- Every integer lookup is bounded by a power of two in the list's encoded size. -/
theorem getD_abs_le_two_pow (l : List ℤ) (N : ℕ)
    (hl : (encList encIntBin l).length ≤ N) (i : ℕ) :
    |l.getD i 0| ≤ (2 : ℤ)^N := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    have he := (length_le_encList_of_mem encIntBin (List.getElem_mem hi)).trans hl
    rw [length_encIntBin] at he
    have hsize : l[i].natAbs.size ≤ N := by omega
    have habs := (Nat.size_le.mp hsize).le
    rw [← Int.natCast_natAbs]
    exact_mod_cast habs
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : l.length ≤ i),
      Option.getD_none, abs_zero]
    positivity

/-- A deliberately loose entry bound, avoiding any permutation bookkeeping. -/
theorem multiplicationMatrix_entry_bound {d : ℕ} (g : Coeff d) (A : ℤ)
    (hA : 0 ≤ A) (hg : ∀ i, |g i| ≤ A) (i j : Fin d) :
    |multiplicationMatrix g i j| ≤ d * A := by
  unfold multiplicationMatrix
  rw [Cyclotomic.mul_comm, Cyclotomic.mul_monomial_left]
  calc
    _ ≤ ∑ k : Fin d, |if (j.val + k.val) % d = i.val then
        (if j.val + k.val < d then 1 else -1) * 1 * g k else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, A := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs <;> first | simpa using (hg k) | exact hA
    _ = _ := by simp

/-- Unary dimensions and framed binary data are individually charged by `encCVP`. -/
theorem cvp_input_length_bounds (x : CVPInput) :
    x.1 ≤ (encCVP x).length ∧
    (encList encIntBin x.2.1).length ≤ (encCVP x).length ∧
    (encList encIntBin x.2.2.1).length ≤ (encCVP x).length ∧
    (encIntBin x.2.2.2).length ≤ (encCVP x).length := by
  simp only [encCVP, length_encPair, encUnary_apply, List.length_replicate]
  omega

/-- The full Cramer bound uses at most `7 (N+1)^2` magnitude bits. -/
theorem cvpCertificateBound_bits (x : CVPInput) :
    (cvpCertificateBound x).toNat.size ≤ certificateBitBound (encCVP x).length := by
  let N := (encCVP x).length
  let A : ℤ := 2^N
  have hA : 1 ≤ A := one_le_pow₀ (by norm_num)
  obtain ⟨hdN, hglen, htlen, hΔlen⟩ := cvp_input_length_bounds x
  have hd : (x.1 : ℤ) ≤ A := by
    have hN : N ≤ 2^N := (Nat.lt_two_pow_self (n := N)).le
    dsimp [A]
    exact_mod_cast hdN.trans hN
  have hg (i : Fin x.1) : |ofList x.2.1 i| ≤ A :=
    getD_abs_le_two_pow _ N hglen i.val
  have ht (i : Fin x.1) : |ofList x.2.2.1 i| ≤ A :=
    getD_abs_le_two_pow _ N htlen i.val
  have hΔ : |x.2.2.2| ≤ A := by
    rw [length_encIntBin] at hΔlen
    have hs : x.2.2.2.natAbs.size ≤ N := by omega
    dsimp [A]
    rw [← Int.natCast_natAbs]
    exact_mod_cast (Nat.size_le.mp hs).le
  have hentry := multiplicationMatrix_entry_bound (ofList (d := x.1) x.2.1) A
    (by omega) hg
  have hbas : basisMagnitude (multiplicationMatrix (ofList (d := x.1) x.2.1)) ≤
      (x.1 : ℤ)^3 * A := by
    unfold basisMagnitude
    calc
      _ ≤ ∑ _i : Fin x.1, ∑ _j : Fin x.1, (x.1 : ℤ) * A := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum fun j _ => hentry i j
      _ = _ := by simp; ring
  have htar : targetMagnitude (ofList (d := x.1) x.2.2.1) ≤ (x.1 : ℤ) * A := by
    unfold targetMagnitude
    calc
      _ ≤ ∑ _i : Fin x.1, A := Finset.sum_le_sum fun i _ => ht i
      _ = _ := by simp
  have hd3 : (x.1 : ℤ)^3 ≤ A^3 := pow_le_pow_left₀ (by positivity) hd 3
  have hA14 : 1 ≤ A^4 := one_le_pow₀ hA
  have hA24 : A^2 ≤ A^4 := pow_le_pow_right₀ hA (by omega)
  have hA4 : A ≤ A^4 := by simpa using (pow_le_pow_right₀ hA (show 1 ≤ 4 by omega))
  have hb4 : (x.1 : ℤ)^3 * A ≤ A^4 := by
    calc
      _ ≤ A^3 * A := mul_le_mul_of_nonneg_right hd3 (by omega)
      _ = _ := by ring
  have ht4 : (x.1 : ℤ) * A ≤ A^4 := by
    calc
      _ ≤ A * A := mul_le_mul_of_nonneg_right hd (by omega)
      _ = A^2 := by ring
      _ ≤ _ := hA24
  have hbase : 1 + basisMagnitude (multiplicationMatrix (ofList (d := x.1) x.2.1)) +
      targetMagnitude (ofList (d := x.1) x.2.2.1) + |x.2.2.2| ≤ 4 * A^4 := by
    linarith
  have hbase0 : 0 ≤ 1 + basisMagnitude (multiplicationMatrix (ofList (d := x.1) x.2.1)) +
      targetMagnitude (ofList (d := x.1) x.2.2.1) + |x.2.2.2| := by
    have := basisMagnitude_nonneg (multiplicationMatrix (ofList (d := x.1) x.2.1))
    have := targetMagnitude_nonneg (ofList (d := x.1) x.2.2.1)
    have := abs_nonneg x.2.2.2
    omega
  have hfac : (x.1.factorial : ℤ) ≤ A^x.1 := by
    calc
      _ ≤ (x.1 : ℤ)^x.1 := by exact_mod_cast Nat.factorial_le_pow x.1
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hd x.1
  have hpow : cvpCertificateBound x ≤ (2 : ℤ)^((N*5+2)*x.1) := by
    calc
      _ ≤ A^x.1 * (4 * A^4)^x.1 :=
        mul_le_mul hfac (pow_le_pow_left₀ hbase0 hbase _) (by positivity) (by positivity)
      _ = (4 * A^5)^x.1 := by rw [← mul_pow]; congr 1; ring
      _ = ((2 : ℤ)^(N*5+2))^x.1 := by
        congr 1
        dsimp [A]
        rw [pow_add, pow_mul]
        norm_num
        ring
      _ = _ := (pow_mul _ _ _).symm
  have hnat : (cvpCertificateBound x).toNat ≤ 2^((N*5+2)*x.1) := by
    have hc := Int.toNat_of_nonneg (cvpCertificateBound_nonneg x)
    rw [← hc] at hpow
    exact_mod_cast hpow
  apply Nat.size_le.mpr
  apply lt_of_le_of_lt hnat
  apply Nat.pow_lt_pow_right (by decide : 1 < 2)
  unfold certificateBitBound
  have hm := Nat.mul_le_mul_left (N*5+2) hdN
  change (N * 5 + 2) * x.1 < 7 * (N + 1)^2
  nlinarith

end Hardness
