import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-!
# Positivity padding (`lem:sidon-padding`)

This lemma works for any nonnegative integral input coefficients. The upper
output bound is enough; bit-valued inputs and outputs are a special case.
The translation assumptions are explicit, so the result can be reused without
unfolding the finite Sidon construction.

Paper: `paper/power2svp.pdf`, Section 4 (Proposition 2 and Lemmas 5–6).
-/
namespace Power2ModuleSVP
namespace BooleanSource
noncomputable section
open Polynomial
open scoped BigOperators

/-- Coefficients of a nonnegative polynomial product are nonnegative. -/
theorem product_coeff_nonneg {P x : ℤ[X]}
    (hP : ∀ i, 0 ≤ P.coeff i) (hx : ∀ i, 0 ≤ x.coeff i) (n : ℕ) :
    0 ≤ (P*x).coeff n := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hP _) (hx _)

/-- A coefficient-one term in a nonnegative factor bounds the corresponding input. -/
theorem coeff_le_product {P x : ℤ[X]}
    (hP : ∀ i, 0 ≤ P.coeff i) (hx : ∀ i, 0 ≤ x.coeff i)
    {k : ℕ} (hk : P.coeff k = 1) (i : ℕ) :
    x.coeff i ≤ (P*x).coeff (i+k) := by
  rw [coeff_mul]
  have h := Finset.single_le_sum
    (f := fun q : ℕ × ℕ => P.coeff q.1 * x.coeff q.2)
    (fun q _ => mul_nonneg (hP _) (hx _))
    (show (k,i) ∈ Finset.antidiagonal (i+k) by simp [add_comm])
  simpa [hk] using h

/-- Below the first nonconstant term, multiplication reads the input unchanged. -/
theorem product_coeff_low {P x : ℤ[X]} {B : ℕ}
    (hzero : P.coeff 0 = 1)
    (hgap : ∀ i, 0 < i → i ≤ B → P.coeff i = 0)
    {n : ℕ} (hn : n ≤ B) : (P*x).coeff n = x.coeff n := by
  rw [coeff_mul, Finset.sum_eq_single (0,n)]
  · simp [hzero]
  · intro q hq hne
    have hsum := Finset.mem_antidiagonal.mp hq
    have hq0 : 0 < q.1 := by
      by_contra h
      have he : q = (0,n) := by ext <;> dsimp at * <;> omega
      exact hne he
    rw [hgap q.1 hq0 (by omega), zero_mul]
  · simp

/-- Full padding theorem. `A` is the set of permitted input positions, all
lying in `[0,B]`; the constructed translation satisfies the two stated rules. -/
theorem sidon_padding {P x y : ℤ[X]} {T L B : ℕ} {A : Finset ℕ} {c : ℕ → ℤ}
    (hT : 0 < T) (hBL : B < T) (hL : 3*T < L)
    (hdeg : P.natDegree ≤ T) (hxdeg : x.degree < L)
    (hP : ∀ i, 0 ≤ P.coeff i) (hx : ∀ i, 0 ≤ x.coeff i)
    (hy : ∀ i < L, y.coeff i ≤ 1)
    (hzero : P.coeff 0 = 1) (htop : P.coeff T = 1)
    (hgap : ∀ i, 0 < i → i ≤ B → P.coeff i = 0)
    (chigh : ∀ i, T+B < i → i < L → c i = 1)
    (clow : ∀ i, i ≤ B → i ∉ A → c i = 1)
    (heq : ∀ i < L, y.coeff i = ((P*x) %ₘ (X^L+P)).coeff i + c i) :
    (∀ i, i ∉ A → x.coeff i = 0) ∧ (P*x) %ₘ (X^L+P) = P*x := by
  by_cases hx0 : x = 0
  · subst x
    simp
  have hxnd : x.natDegree < L := (natDegree_lt_iff_degree_lt hx0).mpr hxdeg
  have hTL : T < L := by omega
  have hmonic : (X^L + P).Monic := monic_X_pow_add
    (degree_le_natDegree.trans_lt (by exact_mod_cast hdeg.trans_lt hTL))
  have hwdeg : (X^L + P).natDegree = L := by
    rw [natDegree_add_eq_left_of_natDegree_lt (by simpa using hdeg.trans_lt hTL)]
    simp
  let q := (P*x) /ₘ (X^L+P)
  have hqdeg : q.natDegree < T := by
    dsimp [q]
    rw [natDegree_divByMonic _ hmonic, hwdeg]
    have hd := natDegree_mul_le (p := P) (q := x)
    omega
  have hcorrection : ∀ i, 2*T ≤ i → (P*q).coeff i = 0 := by
    intro i hi
    apply coeff_eq_zero_of_natDegree_lt
    have hd := natDegree_mul_le (p := P) (q := q)
    omega
  have hhigh : ∀ i, 2*T ≤ i → i < L → (P*x).coeff i = 0 := by
    intro i hi hiL
    have hc := hcorrection i hi
    have he := heq i hiL
    rw [modByMonic_eq_sub_mul_div, add_mul, coeff_sub, coeff_add,
      coeff_X_pow_mul', ite_eq_right (by omega : ¬L ≤ i), zero_add] at he
    change y.coeff i = (P*x).coeff i - (P*q).coeff i + c i at he
    rw [hc, sub_zero, chigh i (by omega) hiL] at he
    have hp := product_coeff_nonneg hP hx i
    have hh := hy i hiL
    omega
  have hxhigh : ∀ i, T ≤ i → x.coeff i = 0 := by
    intro i hi
    by_cases hiL : L ≤ i
    · exact (degree_lt_iff_coeff_zero x L).mp hxdeg i hiL
    by_cases hi2 : 2*T ≤ i
    · have hz := hhigh i hi2 (by omega)
      have hb := coeff_le_product hP hx hzero i
      simp only [add_zero] at hb
      have hn := hx i
      omega
    · have hz := hhigh (i+T) (by omega) (by omega)
      have hb := coeff_le_product hP hx htop i
      have hn := hx i
      omega
  have hsmall : x.degree < T := (degree_lt_iff_coeff_zero x T).mpr hxhigh
  have hxndT : x.natDegree < T := (natDegree_lt_iff_degree_lt hx0).mpr hsmall
  have hprod : (P*x).degree < (X^L+P).degree := by
    have hd := natDegree_mul_le (p := P) (q := x)
    apply lt_of_le_of_lt degree_le_natDegree
    rw [degree_eq_natDegree hmonic.ne_zero, hwdeg]
    exact_mod_cast (show (P*x).natDegree < L by omega)
  have hrem : (P*x) %ₘ (X^L+P) = P*x := (modByMonic_eq_self_iff hmonic).mpr hprod
  refine ⟨?_, hrem⟩
  intro i hiA
  by_cases hiT : T ≤ i
  · exact hxhigh i hiT
  by_cases hiB : B < i
  · have he := heq (i+T) (by omega)
    rw [hrem, chigh (i+T) (by omega) (by omega)] at he
    have hh := hy (i+T) (by omega)
    have hb := coeff_le_product hP hx htop i
    have hn := hx i
    omega
  · have he := heq i (by omega)
    rw [hrem, product_coeff_low hzero hgap (by omega),
      clow i (by omega) hiA] at he
    have hh := hy i (by omega)
    have hn := hx i
    omega

end
end BooleanSource
end Power2ModuleSVP
