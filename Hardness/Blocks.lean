import Hardness.Cyclotomic

/-! # Even/odd multiplication in the negacyclic coefficient model -/
namespace Hardness.Cyclotomic
open Hardness

theorem sum_parity {A : Type*} [AddCommMonoid A] {N : ℕ} (f : Fin (2 * N) → A) :
    (∑ r, f r) = ∑ i : Fin N,
      (f ⟨2 * i.val, by omega⟩ + f ⟨2 * i.val + 1, by omega⟩) := by
  let e : Fin N × Fin 2 ≃ Fin (2 * N) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm N 2))
  rw [← e.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  rw [Fin.sum_univ_two]
  congr 1 <;> congr 1 <;> apply Fin.ext <;> simp [e, finProdFinEquiv] <;> omega

theorem coeff_ext_parity {N : ℕ} {a b : R (2 * N)}
    (he : ∀ i : Fin N, a ⟨2 * i.val, by omega⟩ = b ⟨2 * i.val, by omega⟩)
    (ho : ∀ i : Fin N, a ⟨2 * i.val + 1, by omega⟩ = b ⟨2 * i.val + 1, by omega⟩) : a = b := by
  funext r
  let i : Fin N := ⟨r.val / 2, by omega⟩
  by_cases hr : r.val % 2 = 0
  · have h : r = (⟨2 * i.val, by omega⟩ : Fin (2 * N)) := by apply Fin.ext; dsimp [i]; omega
    simpa [h] using he i
  · have h : r = (⟨2 * i.val + 1, by omega⟩ : Fin (2 * N)) := by apply Fin.ext; dsimp [i]; omega
    simpa [h] using ho i

theorem double_mod (N s : ℕ) : (2 * s) % (2 * N) = 2 * (s % N) :=
  Nat.mul_mod_mul_left _ _ _

theorem double_add_one_mod {N : ℕ} (hN : 0 < N) (s : ℕ) :
    (2 * s + 1) % (2 * N) = 2 * (s % N) + 1 := by
  rw [Nat.add_mod, double_mod, Nat.mod_eq_of_lt (show 1 < 2 * N by omega),
    Nat.mod_eq_of_lt (by have := Nat.mod_lt s hN; omega)]

theorem even_mul {N : ℕ} (h a b : R N) :
    mul (interleave h 0) (interleave a b) = interleave (mul h a) (mul h b) := by
  apply coeff_ext_parity
  · intro r
    have hN : 0 < N := by have := r.isLt; omega
    rw [interleave_even]
    unfold mul
    rw [sum_parity]
    simp_rw [sum_parity, interleave_even, interleave_odd]
    simp only [Pi.zero_apply, MulZeroClass.mul_zero, MulZeroClass.zero_mul,
      ite_self, Finset.sum_const_zero, add_zero, zero_add]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    have he : 2 * i.val + 2 * j.val = 2 * (i.val + j.val) := by omega
    have ho : 2 * i.val + (2 * j.val + 1) = 2 * (i.val + j.val) + 1 := by omega
    rw [he, ho, double_mod, double_add_one_mod hN]
    have hc : (2 * ((i.val + j.val) % N) = 2 * r.val) ↔
        (i.val + j.val) % N = r.val := by omega
    have hn : 2 * ((i.val + j.val) % N) + 1 ≠ 2 * r.val := by omega
    have hs : 2 * (i.val + j.val) < 2 * N ↔ i.val + j.val < N := by omega
    simp [hc, hn, hs]
  · intro r
    have hN : 0 < N := by have := r.isLt; omega
    rw [interleave_odd]
    unfold mul
    rw [sum_parity]
    simp_rw [sum_parity, interleave_even, interleave_odd]
    simp only [Pi.zero_apply, MulZeroClass.mul_zero, MulZeroClass.zero_mul,
      ite_self, Finset.sum_const_zero, add_zero, zero_add]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    have he : 2 * i.val + 2 * j.val = 2 * (i.val + j.val) := by omega
    have ho : 2 * i.val + (2 * j.val + 1) = 2 * (i.val + j.val) + 1 := by omega
    rw [he, ho, double_mod, double_add_one_mod hN]
    have hc : (2 * ((i.val + j.val) % N) + 1 = 2 * r.val + 1) ↔
        (i.val + j.val) % N = r.val := by omega
    have hn : 2 * ((i.val + j.val) % N) ≠ 2 * r.val + 1 := by omega
    have hs : 2 * (i.val + j.val) + 1 < 2 * N ↔ i.val + j.val < N := by omega
    simp [hc, hn, hs]

theorem interleave_smul {N : ℕ} (k : ℤ) (a b : R N) :
    k • interleave a b = interleave (k • a) (k • b) := by
  funext r
  simp only [interleave, Pi.smul_apply]
  split_ifs <;> rfl

theorem interleave_add {N : ℕ} (a b c d : R N) :
    interleave a b + interleave c d = interleave (a + c) (b + d) := by
  funext r
  simp only [interleave, Pi.add_apply]
  split_ifs <;> rfl

theorem interleave_sub {N : ℕ} (a b c d : R N) :
    interleave a b - interleave c d = interleave (a - c) (b - d) := by
  funext r
  simp only [interleave, Pi.sub_apply]
  split_ifs <;> rfl

theorem interleave_monomial_one {N : ℕ} (hN : 0 < N) (a : R N) (z : ℤ) :
    interleave a (monomial ⟨0, hN⟩ z) =
      interleave a 0 + monomial ⟨1, by omega⟩ z := by
  apply coeff_ext_parity
  · intro i
    simp only [interleave_even, Pi.add_apply, monomial]
    have hn : (⟨2 * i.val, by omega⟩ : Fin (2 * N)) ≠ ⟨1, by omega⟩ := by
      intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp [hn]
  · intro i
    simp only [interleave_odd, Pi.add_apply, Pi.zero_apply, zero_add, monomial]
    have hh : ((⟨2 * i.val + 1, by omega⟩ : Fin (2 * N)) = ⟨1, by omega⟩) ↔
        i = ⟨0, hN⟩ := by simp only [Fin.ext_iff]; omega
    simp only [hh]

theorem shift_interleave {N : ℕ} (hN : 0 < N) (a b : R N) :
    shift (by omega) (interleave a b) = interleave (shift hN b) a := by
  apply coeff_ext_parity
  · intro i
    rw [interleave_even]
    by_cases hi : i.val = 0
    · have he : (⟨2 * N - 1, by omega⟩ : Fin (2 * N)) =
          ⟨2 * (N - 1) + 1, by omega⟩ := by apply Fin.ext; dsimp <;> omega
      simp only [shift, hi, MulZeroClass.mul_zero, ite_true]
      rw [he]
      exact congrArg Neg.neg (interleave_odd a b ⟨N - 1, by omega⟩)
    · have he : (⟨2 * i.val - 1, by omega⟩ : Fin (2 * N)) =
          ⟨2 * (i.val - 1) + 1, by omega⟩ := by apply Fin.ext; dsimp <;> omega
      simp only [shift, show 2 * i.val ≠ 0 by omega, hi, ite_false]
      rw [he]
      exact interleave_odd a b ⟨i.val - 1, by omega⟩
  · intro i
    rw [interleave_odd]
    have he : (⟨2 * i.val + 1 - 1, by omega⟩ : Fin (2 * N)) =
        ⟨2 * i.val, by omega⟩ := by apply Fin.ext; dsimp <;> omega
    simp only [shift, show 2 * i.val + 1 ≠ 0 by omega, ite_false]
    rw [he]
    exact interleave_even a b i

end Hardness.Cyclotomic
