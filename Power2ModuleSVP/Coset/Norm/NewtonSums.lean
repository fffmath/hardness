module

public import Power2ModuleSVP.Coset.Norm.Separation
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Data.Multiset.Fintype

/-!
# Newton Sums

Newton identities for the integer power sums used in `lem:elementary-mahler`.
Root multisets retain their multiplicities throughout.

Audit: the normalization covers both signs of the constant coefficient.
The Newton argument includes degree zero and requires no separability.

Paper: `paper/power2svp.pdf`, Section 3.2 (Lemmas 2–4, algebraic norm separation).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Power2ModuleSVP

open Polynomial
open scoped BigOperators

noncomputable section

private theorem newton_esymm_eq {σ τ : Type*} [Fintype σ] [Fintype τ]
    (f : σ → ℂ) (g : τ → ℂ) (n : ℕ)
    (hp : ∀ j ≤ n, 0 < j → (∑ i, f i ^ j) = ∑ i, g i ^ j) :
    MvPolynomial.eval f (MvPolynomial.esymm σ ℂ n) =
      MvPolynomial.eval g (MvPolynomial.esymm τ ℂ n) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simp
    have hsum :
        (∑ a ∈ (Finset.antidiagonal n).filter (fun a => a.1 < n),
          (-1 : ℂ) ^ a.1 * MvPolynomial.eval f (MvPolynomial.esymm σ ℂ a.1) *
            MvPolynomial.eval f (MvPolynomial.psum σ ℂ a.2)) =
        ∑ a ∈ (Finset.antidiagonal n).filter (fun a => a.1 < n),
          (-1 : ℂ) ^ a.1 * MvPolynomial.eval g (MvPolynomial.esymm τ ℂ a.1) *
            MvPolynomial.eval g (MvPolynomial.psum τ ℂ a.2) := by
      apply Finset.sum_congr rfl
      intro a ha
      obtain ⟨ha, han⟩ := Finset.mem_filter.mp ha
      have haeq := Finset.mem_antidiagonal.mp ha
      have hleft := ih a.1 han (fun j hj hj0 => hp j (by omega) hj0)
      have hright : MvPolynomial.eval f (MvPolynomial.psum σ ℂ a.2) =
          MvPolynomial.eval g (MvPolynomial.psum τ ℂ a.2) := by
        simpa [MvPolynomial.psum] using hp a.2 (by omega) (by omega)
      rw [hleft, hright]
    have hf := congrArg (MvPolynomial.eval f) (MvPolynomial.mul_esymm_eq_sum σ ℂ n)
    have hg := congrArg (MvPolynomial.eval g) (MvPolynomial.mul_esymm_eq_sum τ ℂ n)
    simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum] at hf hg
    apply mul_left_cancel₀ (show (n : ℂ) ≠ 0 by exact_mod_cast hn)
    rw [hf, hg, hsum]

private theorem newton_prod_eq {σ τ : Type*} [Fintype σ] [Fintype τ]
    (f : σ → ℂ) (g : τ → ℂ) (hc : Fintype.card σ = Fintype.card τ)
    (hp : ∀ j ≤ Fintype.card σ, 0 < j → (∑ i, f i ^ j) = ∑ i, g i ^ j) :
    (∏ i, (X - C (f i))) = ∏ i, (X - C (g i)) := by
  classical
  have hpneg : ∀ j ≤ Fintype.card σ, 0 < j →
      (∑ i, (-f i) ^ j) = ∑ i, (-g i) ^ j := by
    intro j hj hj0
    have hf : (∑ i, (-f i) ^ j) = (-1 : ℂ) ^ j * ∑ i, f i ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [neg_pow]
    have hg : (∑ i, (-g i) ^ j) = (-1 : ℂ) ^ j * ∑ i, g i ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [neg_pow]
    rw [hf, hg, hp j hj hj0]
  have hes : ∀ j ≤ Fintype.card σ,
      MvPolynomial.eval (fun i => -f i) (MvPolynomial.esymm σ ℂ j) =
      MvPolynomial.eval (fun i => -g i) (MvPolynomial.esymm τ ℂ j) :=
    fun j hj => newton_esymm_eq _ _ j (fun l hl hl0 => hpneg l (hl.trans hj) hl0)
  have hf := congrArg (Polynomial.map (MvPolynomial.eval (fun i => -f i)))
    (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ σ)
  have hg := congrArg (Polynomial.map (MvPolynomial.eval (fun i => -g i)))
    (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ τ)
  simp only [Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_C, MvPolynomial.eval_X, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.C_neg, ← sub_eq_add_neg] at hf hg
  rw [hf, hg, ← hc]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hes j (by have := Finset.mem_range.mp hj; omega)]

private theorem newton_psum_mem_integer {σ : Type*} [Fintype σ]
    (f : σ → ℂ) (d : ℕ)
    (he : ∀ j ≤ d, MvPolynomial.eval f (MvPolynomial.esymm σ ℂ j) ∈
      (Int.castRingHom ℂ).range) :
    ∀ j ≤ d, MvPolynomial.eval f (MvPolynomial.psum σ ℂ j) ∈
      (Int.castRingHom ℂ).range := by
  classical
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hj0 : j = 0
    · subst j
      simp only [MvPolynomial.psum_zero, map_natCast]
      exact ⟨(Fintype.card σ : ℤ), by simp⟩
    have hn := congrArg (MvPolynomial.eval f)
      (MvPolynomial.psum_eq_mul_esymm_sub_sum σ ℂ j (Nat.pos_of_ne_zero hj0))
    simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum] at hn
    rw [hn]
    apply Subring.sub_mem
    · exact Subring.mul_mem _
        (Subring.mul_mem _ (Subring.pow_mem _
          (Subring.neg_mem _ (Subring.one_mem _)) _) ⟨(j : ℤ), by simp⟩) (he j hj)
    · apply Subring.sum_mem
      intro a ha
      obtain ⟨ha, ha'⟩ := Finset.mem_filter.mp ha
      have haeq := Finset.mem_antidiagonal.mp ha
      have halt : 0 < a.1 ∧ a.1 < j := ha'
      exact Subring.mul_mem _
        (Subring.mul_mem _ (Subring.pow_mem _
          (Subring.neg_mem _ (Subring.one_mem _)) _) (he a.1 (by omega)))
        (ih a.2 (by omega) (by omega))

private theorem eval_esymm_roots (p : ℤ[X]) (hp : p.Monic) (j : ℕ)
    (hj : j ≤ p.natDegree) :
    MvPolynomial.eval (fun z : (complexPolynomial p).roots => (z : ℂ))
      (MvPolynomial.esymm (complexPolynomial p).roots ℂ j) =
        (-1 : ℂ) ^ j * (p.coeff (p.natDegree - j) : ℂ) := by
  classical
  have hv := Polynomial.coeff_eq_esymm_roots_of_splits
    (IsAlgClosed.splits (complexPolynomial p))
    (show p.natDegree - j ≤ (complexPolynomial p).natDegree by
      rw [complexPolynomial_natDegree hp]; omega)
  rw [(complexPolynomial_monic hp).leadingCoeff, one_mul,
    complexPolynomial_natDegree hp, Nat.sub_sub_self hj] at hv
  have hs : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨j, rfl⟩
  have hm := MvPolynomial.aeval_esymm_eq_multiset_esymm
    (complexPolynomial p).roots ℂ j (fun z : (complexPolynomial p).roots => (z : ℂ))
  simp only [MvPolynomial.aeval_eq_eval, Multiset.map_univ_coe] at hm
  rw [hm]
  calc
    _ = (-1 : ℂ) ^ j * (complexPolynomial p).coeff (p.natDegree - j) := by
      rw [hv, ← mul_assoc, hs, one_mul]
    _ = (-1 : ℂ) ^ j * (p.coeff (p.natDegree - j) : ℂ) := by
      simp only [complexPolynomial, coeff_map, Int.coe_castRingHom]

/-- Every power sum through the degree of a monic integer polynomial is an integer. -/
theorem integer_root_power_sum {p : ℤ[X]} (hp : p.Monic) (m : ℕ)
    (hm : m ≤ p.natDegree) :
    ∃ a : ℤ, ((complexPolynomial p).roots.map (fun z => z ^ m)).sum = (a : ℂ) := by
  classical
  have he : ∀ j ≤ p.natDegree,
      MvPolynomial.eval (fun z : (complexPolynomial p).roots => (z : ℂ))
        (MvPolynomial.esymm (complexPolynomial p).roots ℂ j) ∈
          (Int.castRingHom ℂ).range := by
    intro j hj
    rw [eval_esymm_roots p hp j hj]
    exact Subring.mul_mem _
      (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
      ⟨p.coeff (p.natDegree - j), rfl⟩
  obtain ⟨a, ha⟩ := newton_psum_mem_integer _ p.natDegree he m hm
  refine ⟨a, ?_⟩
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.eval_X] at ha
  have hmap := Multiset.map_univ (complexPolynomial p).roots (fun z : ℂ => z ^ m)
  have hsum := congrArg Multiset.sum hmap
  exact hsum.symm.trans ha.symm

/-- The normalized reciprocal of a monic unit-constant polynomial is monic. -/
theorem normalizedReciprocal_monic {p : ℤ[X]} (hu : HasUnitConstant p) :
    (normalizedReciprocal p).Monic := by
  have hu0 : p.coeff 0 ≠ 0 := by rcases hu with h | h <;> simp [h]
  change (C (p.coeff 0) * p.reverse).leadingCoeff = 1
  rw [leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff,
    trailingCoeff_eq_coeff_zero hu0]
  rcases hu with h | h <;> simp [h]

theorem normalizedReciprocal_natDegree {p : ℤ[X]} (hu : HasUnitConstant p) :
    (normalizedReciprocal p).natDegree = p.natDegree := by
  have hu0 : p.coeff 0 ≠ 0 := by rcases hu with h | h <;> simp [h]
  rw [normalizedReciprocal, natDegree_C_mul hu0, reverse_natDegree,
    natTrailingDegree_eq_zero.mpr (.inr hu0), Nat.sub_zero]

private theorem complexPolynomial_reverse {p : ℤ[X]} (hp : p.Monic) :
    complexPolynomial p.reverse = (complexPolynomial p).reverse := by
  simp only [complexPolynomial, reverse, hp.natDegree_map, reflect_map]

private theorem reverse_finset_prod {σ : Type*} (s : Finset σ) (f : σ → ℂ[X]) :
    (∏ i ∈ s, f i).reverse = ∏ i ∈ s, (f i).reverse := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact reverse_C (1 : ℂ)
  | @insert a s ha ih => simp [ha, ih]

private theorem reverse_X_sub_C (z : ℂ) (hz : z ≠ 0) :
    (X - C z).reverse = C (-z) * (X - C z⁻¹) := by
  have hx : (X : ℂ[X]).reverse = 1 := by
    simpa only [one_mul, show (1 : ℂ[X]).reverse = 1 from reverse_C (1 : ℂ)] using
      (reverse_mul_X (1 : ℂ[X]))
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, hx, natDegree_X, pow_one]
  rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ hz]
  simp only [C_neg, C_1]
  ring

/-- The full root multiset of the normalized reciprocal consists of inverse roots. -/
theorem roots_normalizedReciprocal {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) :
    (complexPolynomial (normalizedReciprocal p)).roots =
      (complexPolynomial p).roots.map (fun z => z⁻¹) := by
  classical
  let s := (complexPolynomial p).roots
  have hprod : (∏ z : s, (X - C (z : ℂ))) = complexPolynomial p := by
    have hmap := Multiset.map_univ s (fun z : ℂ => (X - C z : ℂ[X]))
    calc
      _ = (s.map (fun z => X - C z)).prod := congrArg Multiset.prod hmap
      _ = _ := prod_multiset_X_sub_C_of_monic_of_roots_card_eq
        (complexPolynomial_monic hp) (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
  have hc : (∏ z : s, -(z : ℂ)) = (p.coeff 0 : ℂ) := by
    have he := congrArg (Polynomial.eval 0) hprod
    simp only [eval_prod, eval_sub, eval_X, eval_C, zero_sub] at he
    simpa only [← coeff_zero_eq_eval_zero, complexPolynomial, coeff_map,
      Int.coe_castRingHom] using he
  have hr : (complexPolynomial p).reverse =
      C (p.coeff 0 : ℂ) * ∏ z : s, (X - C (z : ℂ)⁻¹) := by
    rw [← hprod, reverse_finset_prod]
    calc
      _ = ∏ z : s, C (-(z : ℂ)) * (X - C (z : ℂ)⁻¹) := by
        apply Finset.prod_congr rfl
        intro z _
        exact reverse_X_sub_C _ (root_ne_zero_of_unitConstant hu
          (show (z : ℂ) ∈ (complexPolynomial p).roots from Multiset.coe_mem))
      _ = (∏ z : s, C (-(z : ℂ))) * ∏ z : s, (X - C (z : ℂ)⁻¹) :=
        Finset.prod_mul_distrib
      _ = _ := by rw [← map_prod, hc]
  have hnorm : complexPolynomial (normalizedReciprocal p) =
      ∏ z : s, (X - C (z : ℂ)⁻¹) := by
    have he : complexPolynomial (normalizedReciprocal p) =
        C (p.coeff 0 : ℂ) * complexPolynomial p.reverse := by
      simp only [complexPolynomial, normalizedReciprocal, Polynomial.map_mul,
        Polynomial.map_C, Int.coe_castRingHom]
    rw [he, complexPolynomial_reverse hp, hr, ← mul_assoc, ← C_mul]
    have hsq : (p.coeff 0 : ℂ) * (p.coeff 0 : ℂ) = 1 := by
      rcases hu with h | h <;> simp [h]
    rw [hsq, C_1, one_mul]
  rw [hnorm]
  have hmap := Multiset.map_univ s (fun z : ℂ => (X - C z⁻¹ : ℂ[X]))
  rw [Finset.prod_eq_multiset_prod, hmap]
  simpa only [Multiset.map_map, Function.comp_apply] using
    roots_multiset_prod_X_sub_C (s.map (fun z => z⁻¹))

/-- Distinct normalized reciprocals have distinct integer power sums at an
order between one and the degree.  No squarefreeness assumption is needed. -/
theorem nonreciprocal_power_sum_witness {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) (hne : p ≠ normalizedReciprocal p) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ p.natDegree ∧ ∃ a b : ℤ, a ≠ b ∧
      ((complexPolynomial p).roots.map (fun z => z ^ m)).sum = (a : ℂ) ∧
      ((complexPolynomial p).roots.map (fun z => z⁻¹ ^ m)).sum = (b : ℂ) := by
  classical
  have hpr := normalizedReciprocal_monic hu
  have hdr := normalizedReciprocal_natDegree hu
  have hroot := roots_normalizedReciprocal hp hu
  have hcard (q : ℤ[X]) (hq : q.Monic) :
      Fintype.card (complexPolynomial q).roots = q.natDegree := by
    rw [Multiset.card_coe, ← (IsAlgClosed.splits _).natDegree_eq_card_roots,
      complexPolynomial_natDegree hq]
  have hdiff : ∃ m : ℕ, 1 ≤ m ∧ m ≤ p.natDegree ∧
      ((complexPolynomial p).roots.map (fun z => z ^ m)).sum ≠
      ((complexPolynomial p).roots.map (fun z => z⁻¹ ^ m)).sum := by
    by_contra h
    push Not at h
    have he : ∀ j ≤ Fintype.card (complexPolynomial p).roots, 0 < j →
        (∑ z : (complexPolynomial p).roots, (z : ℂ) ^ j) =
        ∑ z : (complexPolynomial (normalizedReciprocal p)).roots, (z : ℂ) ^ j := by
      intro j hj hj0
      have hjd : j ≤ p.natDegree := by rwa [hcard p hp] at hj
      have hpj := h j (by omega) hjd
      have hrecj :
          ((complexPolynomial (normalizedReciprocal p)).roots.map (fun z => z ^ j)).sum =
          ((complexPolynomial p).roots.map (fun z => z⁻¹ ^ j)).sum := by
        rw [hroot, Multiset.map_map]
        rfl
      have hmap1 := congrArg Multiset.sum
        (Multiset.map_univ (complexPolynomial p).roots (fun z : ℂ => z ^ j))
      have hmap2 := congrArg Multiset.sum
        (Multiset.map_univ (complexPolynomial (normalizedReciprocal p)).roots
          (fun z : ℂ => z ^ j))
      exact hmap1.trans (hpj.trans (hrecj.symm.trans hmap2.symm))
    have hpoly := newton_prod_eq
      (fun z : (complexPolynomial p).roots => (z : ℂ))
      (fun z : (complexPolynomial (normalizedReciprocal p)).roots => (z : ℂ))
      (by rw [hcard p hp, hcard _ hpr, hdr]) he
    have hprod (q : ℤ[X]) (hq : q.Monic) :
        (∏ z : (complexPolynomial q).roots, (X - C (z : ℂ))) = complexPolynomial q := by
      calc
        _ = ((complexPolynomial q).roots.map (fun z => X - C z)).prod :=
          congrArg Multiset.prod (Multiset.map_univ _ (fun z : ℂ => (X - C z : ℂ[X])))
        _ = _ := prod_multiset_X_sub_C_of_monic_of_roots_card_eq
          (complexPolynomial_monic hq) (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
    rw [hprod p hp, hprod _ hpr] at hpoly
    apply hne
    ext k
    have hk := congrArg (fun q : ℂ[X] => q.coeff k) hpoly
    have hk' : (p.coeff k : ℂ) = ((normalizedReciprocal p).coeff k : ℂ) := by
      simpa only [complexPolynomial, coeff_map, Int.coe_castRingHom] using hk
    exact Int.cast_injective hk'
  obtain ⟨m, hm, hmd, hdiff⟩ := hdiff
  obtain ⟨a, ha⟩ := integer_root_power_sum hp m hmd
  obtain ⟨b, hb⟩ := integer_root_power_sum hpr m (by rwa [hdr])
  have hb' : ((complexPolynomial p).roots.map (fun z => z⁻¹ ^ m)).sum = (b : ℂ) := by
    simpa only [hroot, Multiset.map_map, Function.comp_apply] using hb
  refine ⟨m, hm, hmd, a, b, ?_, ha, hb'⟩
  intro hab
  exact hdiff (ha.trans ((congrArg (fun t : ℤ => (t : ℂ)) hab).trans hb'.symm))

end

end Power2ModuleSVP
