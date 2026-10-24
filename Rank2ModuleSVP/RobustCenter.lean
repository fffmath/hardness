import Rank2ModuleSVP.Descent2
import Rank2ModuleSVP.Sparse
import Mathlib.Order.Filter.AtTopBot.Basic

/-! The robust centre, in integral coefficients and finite-field polynomials. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Rank2ModuleSVP
noncomputable section
open scoped BigOperators
open Polynomial
variable {q : ℕ} [NeZero q]

/-- Largest integer `k` with `(2k)^1000 ≤ q`. -/
def descentParameter (q : ℕ) : ℕ :=
  (Finset.range (q+1)).filter (fun k => (2*k)^1000 ≤ q) |>.max'
    ⟨0, by simp⟩

theorem descentParameter_spec (q : ℕ) : (2*descentParameter q)^1000 ≤ q := by
  have hm := Finset.max'_mem
    ((Finset.range (q+1)).filter (fun k : ℕ => (2*k)^1000 ≤ q)) ⟨0, by simp⟩
  exact (Finset.mem_filter.mp hm).2

theorem le_descentParameter (q r : ℕ) (hr : (2*r)^1000 ≤ q) :
    r ≤ descentParameter q := by
  apply Finset.le_max'
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, hr⟩
  have hh := (Nat.le_self_pow (by decide : 1000 ≠ 0) (2*r)).trans hr
  omega

theorem descentParameter_large (hq : 200^1000 ≤ q) :
    100 ≤ descentParameter q := le_descentParameter q 100 (by simpa using hq)

theorem descentParameter_le_half (q : ℕ) : 2*descentParameter q ≤ q :=
  (Nat.le_self_pow (by decide) _).trans (descentParameter_spec q)

/-- The prescribed binary weight. -/
def descentWeight (q : ℕ) : ℕ := 201 * descentParameter q / 200

/-- The centre in equation `robust-center`, with parameters made explicit. -/
def robustCenter (k h : ℕ) : IntegerRing q := (h : IntegerRing q) + (pi : IntegerRing q)^(k/2)

/-- Scalar multiplication of all integral coefficients scales the squared norm. -/
theorem coeffNormSq_mul_int (z : Coeff ℤ q) (t : ℤ) :
    coeffNormSq (fun a => t*z a) = t^2*coeffNormSq z := by
  rw [coeffNormSq_eq, coeffNormSq_eq]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- A short nonzero element cannot have every coefficient divisible by `q`. -/
theorem residuePolynomial_ne_zero_of_short (z : Coeff ℤ q)
    (hne : classOf z ≠ 0) (hq : 4 ≤ q) (hshort : normSq (classOf z) ≤ 3*q) :
    residuePolynomial z ≠ 0 := by
  intro hz
  have hd : ∀ a, (q : ℤ) ∣ z a := by
    intro a
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have he := congrArg (fun f : (ZMod q)[X] => f.coeff a.val) hz
    rw [residuePolynomial_coeff, coeff_zero] at he
    exact he
  choose y hy using hd
  have he : z = fun a => (q : ℤ)*y a := funext hy
  have hnorm : normSq (classOf z) = (q : ℤ)^2*coeffNormSq y := by
    rw [he, normSq_classOf, coeffNormSq_mul_int]
  have hpos : 0 < normSq (classOf z) :=
    lt_of_le_of_ne (normSq_nonneg _) (Ne.symm ((normSq_eq_zero_iff _).not.mpr hne))
  have hypos : 1 ≤ coeffNormSq y := by
    have := coeffNormSq_nonneg y
    by_contra hh
    have : coeffNormSq y = 0 := by omega
    rw [this, mul_zero] at hnorm
    omega
  have hq' : (4 : ℤ) ≤ q := by exact_mod_cast hq
  nlinarith [mul_nonneg (sq_nonneg (q : ℤ)) (sub_nonneg.mpr hypos)]

/-- Reduction modulo `q` cannot increase coefficient support. -/
theorem residuePolynomial_support_le (z : Coeff ℤ q) :
    (residuePolynomial z).support.card ≤ supportCard z := by
  classical
  let s := Finset.univ.filter fun a : ZMod q => z a ≠ 0
  have hs : (residuePolynomial z).support ⊆ s.image ZMod.val := by
    intro n hn
    have hnl : n < q := (le_natDegree_of_mem_supp n hn).trans_lt
      (residuePolynomial_natDegree_lt z)
    refine Finset.mem_image.mpr ⟨(n : ZMod q), ?_, ZMod.val_natCast_of_lt hnl⟩
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hz
    have hh := mem_support_iff.mp hn
    have he := residuePolynomial_coeff z (n : ZMod q)
    rw [ZMod.val_natCast_of_lt hnl, hz, Int.cast_zero] at he
    exact hh he
  exact (Finset.card_le_card hs).trans (Finset.card_image_le)

private theorem support_sub_C_mul_le {R : Type*} [CommRing R] [DecidableEq R]
    (P Q : R[X]) (h : R) :
    (P-C h*Q).support.card ≤ P.support.card+Q.support.card := by
  have hs : (P-C h*Q).support ⊆ P.support ∪ Q.support := by
    intro n hn
    simp only [Finset.mem_union, mem_support_iff] at hn ⊢
    contrapose! hn
    simp [coeff_sub, coeff_C_mul, hn]
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

private theorem exists_integral_ideal_norm (I : Ideal (IntegerRing q)) (v : IntegerRing q) :
    ∃ n : ℕ, ∃ a ∈ I, (n : ℤ) = normSq (v-a) := by
  refine ⟨(normSq v).toNat, 0, I.zero_mem, ?_⟩
  simpa using Int.toNat_of_nonneg (normSq_nonneg v)

/-- The squared distance to an integral ideal, as an attained integer minimum.
    The norm is the canonical form from the coefficient quotient model. -/
def idealDistanceSq (I : Ideal (IntegerRing q)) (v : IntegerRing q) : ℕ := by
  classical
  exact Nat.find (exists_integral_ideal_norm I v)

theorem idealDistanceSq_attained (I : Ideal (IntegerRing q)) (v : IntegerRing q) :
    ∃ a ∈ I, (idealDistanceSq I v : ℤ) = normSq (v-a) := by
  classical
  exact Nat.find_spec (exists_integral_ideal_norm I v)

theorem idealDistanceSq_le (I : Ideal (IntegerRing q)) (v a : IntegerRing q)
    (ha : a ∈ I) : (idealDistanceSq I v : ℤ) ≤ normSq (v-a) := by
  classical
  have he : (((normSq (v-a)).toNat : ℕ) : ℤ) = normSq (v-a) :=
    Int.toNat_of_nonneg (normSq_nonneg _)
  have hh : idealDistanceSq I v ≤ (normSq (v-a)).toNat :=
    Nat.find_min' (exists_integral_ideal_norm I v) ⟨a, ha, he⟩
  exact (show (idealDistanceSq I v : ℤ) ≤ ((normSq (v-a)).toNat : ℕ) by
    exact_mod_cast hh).trans_eq he

section Prime
variable [Fact q.Prime]

/-- Sparse multiplicity forces the first congruence in the robust-centre proof
    to be an equality of polynomials. -/
theorem robust_sparse_polynomial (k m : ℕ) (hm : m ≤ k)
    (E W : (ZMod q)[X]) (hE : E.natDegree < q) (hW : W.natDegree < q)
    (h : ZMod q) (hs : E.support.card+W.support.card ≤ m)
    (hc : (X-1 : (ZMod q)[X])^k ∣ E-W*(C h+(1-X)^m)) :
    E = C h*W := by
  have hdiv : (X-1 : (ZMod q)[X])^m ∣ E-C h*W := by
    have h1 := dvd_trans (pow_dvd_pow (X-1 : (ZMod q)[X]) hm) hc
    have h2 : (X-1 : (ZMod q)[X])^m ∣ W*(1-X)^m := by
      rw [show (1-X : (ZMod q)[X]) = -(X-1) by ring, neg_pow]
      exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
    convert dvd_add h1 h2 using 1 <;> ring
  by_contra hn
  have hne : E-C h*W ≠ 0 := sub_ne_zero.mpr hn
  have hd : (E-C h*W).natDegree < q := by
    exact (natDegree_sub_le _ _).trans_lt (max_lt hE ((natDegree_C_mul_le _ _).trans_lt hW))
  have hm' := (le_rootMultiplicity_iff hne).mpr (by rw [show (C (1 : ZMod q) : (ZMod q)[X]) = 1 from C_1]; exact hdiv)
  have hs' := support_sub_C_mul_le E W h
  have hsp := sparse_tools_ii (E-C h*W) hne hd
  omega

/-- Once the sparse difference vanishes, the second multiplicity contradicts
    the support bound for the nonzero short multiplier. -/
theorem robust_polynomial_contradiction (k m : ℕ) (hm : m ≤ k)
    (E W : (ZMod q)[X]) (hE : E.natDegree < q) (hW : W.natDegree < q)
    (h : ZMod q) (hW0 : W ≠ 0) (hs : E.support.card+W.support.card ≤ m)
    (hWs : W.support.card ≤ k-m)
    (hc : (X-1 : (ZMod q)[X])^k ∣ E-W*(C h+(1-X)^m)) : False := by
  have he := robust_sparse_polynomial k m hm E W hE hW h hs hc
  rw [he] at hc
  have hdiv : (X-1 : (ZMod q)[X])^(k-m) ∣ W := by
    have hh : (X-1 : (ZMod q)[X])^k ∣ W*(X-1)^m := by
      have hu : IsUnit ((-1 : (ZMod q)[X])^m) := isUnit_neg_one.pow m
      have heq : C h*W-W*(C h+(1-X)^m) = -(((-1 : (ZMod q)[X])^m)*(W*(X-1)^m)) := by
        rw [show (1-X : (ZMod q)[X]) = -(X-1) by ring, neg_pow]
        ring
      rw [heq, dvd_neg, hu.dvd_mul_left] at hc
      exact hc
    have heq : k = (k-m)+m := (Nat.sub_add_cancel hm).symm
    rw [heq, pow_add] at hh
    exact (mul_dvd_mul_iff_right (pow_ne_zero m (X_sub_C_ne_zero (1 : ZMod q)))).mp hh
  have hl := (le_rootMultiplicity_iff hW0).mpr (by rw [show (C (1 : ZMod q) : (ZMod q)[X]) = 1 from C_1]; exact hdiv)
  have hu := sparse_tools_ii W hW0 hW
  omega

/-- Robust-centre separation, with explicit finite numerical bounds.
    This pointwise form implies the squared distance bound for the ideal. -/
theorem robust_center_explicit (k h : ℕ) (hk : 100 ≤ k) (hkq : k ≤ q-1)
    (hq : 4 ≤ q) (w e : IntegerRing q) (hw : w ≠ 0) (hwn : normSq w ≤ 3*q)
    (he : e-w*robustCenter k h ∈ ramifiedIdeal k) :
    (2*k*q : ℤ) < 100*normSq e := by
  by_contra hbad
  have hen : 100*normSq e ≤ (2*k*q : ℤ) := le_of_not_gt hbad
  obtain ⟨ze, hze, hse⟩ := sparse_representative e
  obtain ⟨zw, hzw, hsw⟩ := sparse_representative w
  have hqpos : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  have hse' : 25*supportCard ze ≤ k := by
    have hq0 : (0 : ℤ) ≤ q := le_of_lt hqpos
    have hh : (q : ℤ)*(25*supportCard ze) ≤ (q : ℤ)*k := by nlinarith
    have hh' := (mul_le_mul_iff_right₀ hqpos).mp hh
    exact_mod_cast hh'
  have hsw' : supportCard zw ≤ 6 := by
    have hh : (q : ℤ)*supportCard zw ≤ (q : ℤ)*6 := by nlinarith
    exact_mod_cast (mul_le_mul_iff_right₀ hqpos).mp hh
  have hcong : (X-1 : (ZMod q)[X])^k ∣
      residuePolynomial ze - residuePolynomial zw * (C (h : ZMod q)+(1-X)^(k/2)) := by
    have heval : cyclotomicEval (q := q)
        (coefficientPolynomial ze - coefficientPolynomial zw*(C (h : ℤ)+(1-X)^(k/2))) ∈
          ramifiedIdeal k := by
      simpa [hze, hzw, robustCenter, pi] using he
    have hh := (cyclotomicEval_mem_ramifiedIdeal_iff k hkq _).mp heval
    simpa [residuePolynomial] using hh
  have hsE := residuePolynomial_support_le ze
  have hsW := residuePolynomial_support_le zw
  have hW0 := residuePolynomial_ne_zero_of_short zw (by rwa [hzw]) hq (by rwa [hzw])
  exact robust_polynomial_contradiction k (k/2) (Nat.div_le_self _ _)
    (residuePolynomial ze) (residuePolynomial zw)
    (residuePolynomial_natDegree_lt ze) (residuePolynomial_natDegree_lt zw)
    (h : ZMod q) hW0 (by omega) (by omega) hcong

/-- Paper `robust-center`: for all sufficiently large primes, every point in
    the relevant ideal coset has squared norm strictly above `L/100`.
    The universal bound is the exact squared-distance formulation needed by
    the later soundness argument. -/
theorem robust_center (hq : 200^1000 ≤ q) (w e : IntegerRing q)
    (hw : w ≠ 0) (hwn : normSq w ≤ 3*q)
    (he : e-w*robustCenter (descentParameter q) (descentWeight q) ∈
      ramifiedIdeal (descentParameter q)) :
    (2*descentParameter q*q : ℤ) < 100*normSq e := by
  have hk := descentParameter_large hq
  have hhalf := descentParameter_le_half q
  apply robust_center_explicit _ _ hk (by omega) (by omega) w e hw hwn he

/-- The same separation with an explicit ideal element subtracted from `wc`. -/
theorem robust_center_sub_ideal (hq : 200^1000 ≤ q) (w a : IntegerRing q)
    (hw : w ≠ 0) (hwn : normSq w ≤ 3*q)
    (ha : a ∈ ramifiedIdeal (descentParameter q)) :
    (2*descentParameter q*q : ℤ) <
      100*normSq (w*robustCenter (descentParameter q) (descentWeight q)-a) := by
  apply robust_center hq w _ hw hwn
  convert (ramifiedIdeal (descentParameter q)).neg_mem ha using 1 <;> abel

/-- The squared-distance statement of paper `robust-center`. -/
theorem robust_center_distance (hq : 200^1000 ≤ q) (w : IntegerRing q)
    (hw : w ≠ 0) (hwn : normSq w ≤ 3*q) :
    (2*descentParameter q*q : ℤ) <
      100*(idealDistanceSq (ramifiedIdeal (descentParameter q))
        (w*robustCenter (descentParameter q) (descentWeight q)) : ℤ) := by
  obtain ⟨a, ha, he⟩ := idealDistanceSq_attained
    (ramifiedIdeal (descentParameter q))
    (w*robustCenter (descentParameter q) (descentWeight q))
  rw [he]
  exact robust_center_sub_ideal hq w a hw hwn ha

end Prime
end
end Rank2ModuleSVP
