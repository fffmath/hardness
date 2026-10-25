import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Rank2ModuleSVP.Descent2

/-! # The Bennett–Peikert minimum

Newton identities prove the Reed–Solomon minimum used in paper v2
Theorem 3.2, and hence the canonical minimum of the ramified ideal.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Rank2ModuleSVP
noncomputable section
open scoped BigOperators
variable {q : ℕ} [Fact q.Prime]

/-- Below the characteristic, equal power sums determine equal elementary
    symmetric polynomials, including repeated entries. -/
theorem newton_esymm_eq_of_power_sums {σ τ : Type*} [Fintype σ] [Fintype τ]
    (f : σ → ZMod q) (g : τ → ZMod q) (n : ℕ) (hn : n < q)
    (hp : ∀ j ≤ n, 0 < j → (∑ i, f i ^ j) = ∑ i, g i ^ j) :
    MvPolynomial.eval f (MvPolynomial.esymm σ (ZMod q) n) =
      MvPolynomial.eval g (MvPolynomial.esymm τ (ZMod q) n) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp
    have hncast : (n : ZMod q) ≠ 0 := by
      intro h
      have hd := (ZMod.natCast_eq_zero_iff n q).mp h
      exact (Nat.le_of_dvd (by omega) hd).not_gt hn
    have hsum :
        (∑ a ∈ (Finset.antidiagonal n).filter (fun a => a.1 < n),
          (-1 : ZMod q) ^ a.1 *
            MvPolynomial.eval f (MvPolynomial.esymm σ (ZMod q) a.1) *
            MvPolynomial.eval f (MvPolynomial.psum σ (ZMod q) a.2)) =
        ∑ a ∈ (Finset.antidiagonal n).filter (fun a => a.1 < n),
          (-1 : ZMod q) ^ a.1 *
            MvPolynomial.eval g (MvPolynomial.esymm τ (ZMod q) a.1) *
            MvPolynomial.eval g (MvPolynomial.psum τ (ZMod q) a.2) := by
      apply Finset.sum_congr rfl
      intro a ha
      obtain ⟨ha, han⟩ := Finset.mem_filter.mp ha
      have haeq := Finset.mem_antidiagonal.mp ha
      have hleft := ih a.1 han (by omega) (fun j hj hj0 => hp j (by omega) hj0)
      have hright : MvPolynomial.eval f (MvPolynomial.psum σ (ZMod q) a.2) =
          MvPolynomial.eval g (MvPolynomial.psum τ (ZMod q) a.2) := by
        simpa [MvPolynomial.psum] using hp a.2 (by omega) (by omega)
      rw [hleft, hright]
    have hf := congrArg (MvPolynomial.eval f)
      (MvPolynomial.mul_esymm_eq_sum σ (ZMod q) n)
    have hg := congrArg (MvPolynomial.eval g)
      (MvPolynomial.mul_esymm_eq_sum τ (ZMod q) n)
    simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at hf hg
    apply mul_left_cancel₀ hncast
    rw [hf, hg, hsum]

/-- The monic polynomials with two root lists are equal once the list sizes
    and their power sums agree below the characteristic. -/
theorem prod_X_sub_C_eq_of_power_sums {σ τ : Type*} [Fintype σ] [Fintype τ]
    (f : σ → ZMod q) (g : τ → ZMod q)
    (hc : Fintype.card σ = Fintype.card τ) (hn : Fintype.card σ < q)
    (hp : ∀ j ≤ Fintype.card σ, 0 < j → (∑ i, f i ^ j) = ∑ i, g i ^ j) :
    (∏ i, (Polynomial.X - Polynomial.C (f i))) =
      ∏ i, (Polynomial.X - Polynomial.C (g i)) := by
  classical
  have hpneg : ∀ j ≤ Fintype.card σ, 0 < j →
      (∑ i, (-f i) ^ j) = ∑ i, (-g i) ^ j := by
    intro j hj hj0
    have hf : (∑ i, (-f i) ^ j) = (-1 : ZMod q) ^ j * ∑ i, f i ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [neg_pow]
    have hg : (∑ i, (-g i) ^ j) = (-1 : ZMod q) ^ j * ∑ i, g i ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [neg_pow]
    rw [hf, hg, hp j hj hj0]
  have hes : ∀ j ≤ Fintype.card σ,
      MvPolynomial.eval (fun i => -f i) (MvPolynomial.esymm σ (ZMod q) j) =
      MvPolynomial.eval (fun i => -g i) (MvPolynomial.esymm τ (ZMod q) j) := by
    intro j hj
    exact newton_esymm_eq_of_power_sums _ _ j (hj.trans_lt hn)
      (fun l hl hl0 => hpneg l (hl.trans hj) hl0)
  have hf := congrArg (Polynomial.map (MvPolynomial.eval (fun i => -f i)))
    (MvPolynomial.prod_C_add_X_eq_sum_esymm (ZMod q) σ)
  have hg := congrArg (Polynomial.map (MvPolynomial.eval (fun i => -g i)))
    (MvPolynomial.prod_C_add_X_eq_sum_esymm (ZMod q) τ)
  simp only [Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_C, MvPolynomial.eval_X, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.C_neg, ← sub_eq_add_neg] at hf hg
  rw [hf, hg, ← hc]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hes j (by have := Finset.mem_range.mp hj; omega)]

private theorem int_pos_neg_decomposition (t : ℤ) :
    ((t.toNat : ℕ) : ℤ) - (((-t).toNat : ℕ) : ℤ) = t ∧
      ((t.toNat : ℕ) : ℤ) + (((-t).toNat : ℕ) : ℤ) = |t| := by
  by_cases ht : 0 ≤ t
  · simp [Int.toNat_of_nonneg ht, Int.toNat_of_nonpos (by omega : -t ≤ 0), abs_of_nonneg ht]
  · simp [Int.toNat_of_nonpos (by omega : t ≤ 0),
      Int.toNat_of_nonneg (by omega : 0 ≤ -t), abs_of_nonpos (by omega : t ≤ 0)]

/-- Bennett--Peikert Theorem 14, proved from integral positive/negative parts
    and Newton identities in characteristic `q`. -/
theorem bennettPeikertMinimum : BennettPeikertMinimum := by
  intro q hq
  let : Fact q.Prime := ⟨hq⟩
  intro k hk hkq z hz hne
  by_contra hmin
  have hshort : IdealCVP.sqNorm z < (2 * k : ℤ) := lt_of_not_ge hmin
  have hsum := short_liftedRS_sum_zero k hk hkq z hz hshort
  let σ := Σ a : ZMod q, Fin ((z a).toNat)
  let τ := Σ a : ZMod q, Fin ((-z a).toNat)
  let f : σ → ZMod q := fun i => i.1
  let g : τ → ZMod q := fun i => i.1
  have hcardσ : Fintype.card σ = ∑ a, (z a).toNat := by simp [σ, Fintype.card_sigma]
  have hcardτ : Fintype.card τ = ∑ a, (-z a).toNat := by simp [τ, Fintype.card_sigma]
  have hdiff : (Fintype.card σ : ℤ) - (Fintype.card τ : ℤ) = 0 := by
    rw [hcardσ, hcardτ, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib]
    simp_rw [(int_pos_neg_decomposition _).1]
    exact hsum
  have hc : Fintype.card σ = Fintype.card τ := by omega
  have hl1 : (Fintype.card σ : ℤ) + (Fintype.card τ : ℤ) ≤ IdealCVP.sqNorm z := by
    rw [hcardσ, hcardτ, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_add_distrib]
    simp_rw [(int_pos_neg_decomposition _).2]
    exact sum_abs_le_sqNorm z
  have hcardk : Fintype.card σ < k := by
    have hcast : (Fintype.card σ : ℤ) = Fintype.card τ := by omega
    rw [← hcast] at hl1
    have : (Fintype.card σ : ℤ) < k := by omega
    exact_mod_cast this
  have hp : ∀ j ≤ Fintype.card σ, 0 < j →
      (∑ i, f i ^ j) = ∑ i, g i ^ j := by
    intro j hj _
    have hsj := congrFun hz ⟨j, hj.trans_lt hcardk⟩
    change (∑ a : ZMod q, (z a : ZMod q) * a ^ j) = 0 at hsj
    have hcast (a : ZMod q) :
        (((z a).toNat : ℕ) : ZMod q) - (((-z a).toNat : ℕ) : ZMod q) = (z a : ZMod q) := by
      have he := congrArg (fun t : ℤ => (t : ZMod q))
        (int_pos_neg_decomposition (z a)).1
      simpa only [Int.cast_sub, Int.cast_natCast] using he
    apply sub_eq_zero.mp
    change (∑ i : (Σ a : ZMod q, Fin (z a).toNat), i.1 ^ j) -
      (∑ i : (Σ a : ZMod q, Fin (-z a).toNat), i.1 ^ j) = 0
    simp only [Fintype.sum_sigma, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul, hcast]
    exact hsj
  have hpoly := prod_X_sub_C_eq_of_power_sums f g hc (by omega) hp
  obtain ⟨a, ha⟩ : ∃ a : ZMod q, 0 < z a := by
    by_contra h
    have hnonpos : ∀ a, z a ≤ 0 := by simpa using h
    have hzero : ∀ a, z a = 0 := by
      have hh := (Finset.sum_eq_zero_iff_of_nonpos (fun a _ => hnonpos a)).mp hsum
      exact fun a => hh a (Finset.mem_univ a)
    exact hne (funext hzero)
  let i : σ := ⟨a, ⟨0, by omega⟩⟩
  have he := congrArg (Polynomial.eval (f i)) hpoly
  have hleft : (∏ j : σ, (f i - f j)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have hright : (∏ j : τ, (f i - g j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply sub_ne_zero.mpr
    intro hij
    have haj : a = j.1 := hij
    have hjneg : 0 < -z j.1 := by
      have hh := j.2.isLt
      have : 0 < (-z j.1).toNat := by omega
      omega
    rw [← haj] at hjneg
    omega
  apply hright
  simpa only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, hleft] using he.symm

/-- The canonical minimum from cyclotomic descent is unconditional after the
    elementary Bennett--Peikert argument above. -/
theorem ramifiedIdeal_minimum {q : ℕ} [NeZero q] [Fact q.Prime]
    (k : ℕ) (hk : 1 ≤ k) (hkq : 2 * k ≤ q) (v : IntegerRing q)
    (hv : v ∈ ramifiedIdeal k) (hne : v ≠ 0) :
    (2 * k * q : ℤ) ≤ normSq v :=
  ramifiedIdeal_norm_lower bennettPeikertMinimum k hk hkq v hv hne

end
end Rank2ModuleSVP
