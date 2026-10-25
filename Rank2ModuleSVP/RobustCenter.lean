import Rank2ModuleSVP.Descent2
import Rank2ModuleSVP.Sparse
import Rank2ModuleSVP.SparsePolynomial

/-! # Robust centre separation

Paper v2 §3.3, especially Lemmas 3.5–3.6 and Theorem 3.7:
sparse integral coefficients and finite-field polynomials separate ideal cosets.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Rank2ModuleSVP
noncomputable section
open scoped BigOperators
open Polynomial
variable {q : ℕ} [NeZero q]

/-- An explicit threshold sufficient for the support inequalities in Theorem 3.7. -/
def sepK0 : ℕ := 100

/-- Separation needs only the linear lower bound `q ≥ 2k`. -/
def sepC0 : ℕ := 1

/-- The prescribed binary weight in v2, with `k` chosen first. -/
def sepWeight (k : ℕ) : ℕ := 21 * k / 20

/-- The centre in v2 equation (11), allowing an arbitrary integral weight. -/
def robustCenter (k h : ℕ) : IntegerRing q := (h : IntegerRing q) + (pi : IntegerRing q) ^ (k / 2)

/-- The centre for the prescribed v2 weight. -/
def sepCenter (k : ℕ) : IntegerRing q := robustCenter k (sepWeight k)

/-- The explicit integral polynomial representing the centre. -/
def robustCenterPolynomial (k h : ℕ) : ℤ[X] := C (h : ℤ) + (1 - X) ^ (k / 2)

/-- Its degree-`<q` coefficient vector (under the degree hypothesis below). -/
def robustCenterCoeffs (k h : ℕ) : Coeff ℤ q :=
  fun a => (robustCenterPolynomial k h).coeff a.val

/-- V2 Lemma 3.5(i), including the squared coefficient norm bound.
The averaging proof works for every element, without a smallness assumption. -/
theorem sparse_tools_i_v2 (v : IntegerRing q) :
    ∃ z : Coeff ℤ q, classOf z = v ∧
      (q : ℤ) * IdealCVP.sqNorm z ≤ 2 * normSq v ∧
      (q : ℤ) * supportCard z ≤ 2 * normSq v := by
  classical
  obtain ⟨z, rfl⟩ := classOf_surjective v
  let row (a : ZMod q) : ℤ := ∑ b, (z b - z a) ^ 2
  have hsum : ∑ a, (q : ℤ) * row a ≤ ∑ _a : ZMod q, 2 * coeffNormSq z := by
    rw [← Finset.mul_sum]
    have he : (∑ a, row a) = 2 * coeffNormSq z := by
      unfold row
      rw [Finset.sum_comm, ← two_mul_coeffNormSq]
    rw [he]
    simp [Finset.card_univ, ZMod.card]
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  let x : Coeff ℤ q := fun b => z b - z a
  refine ⟨x, ?_, ?_, ?_⟩
  · simpa only [x, sub_eq_add_neg] using classOf_add_constant z (-z a)
  · simpa only [normSq_classOf, IdealCVP.sqNorm, x, row] using ha
  · rw [normSq_classOf]
    exact (mul_le_mul_of_nonneg_left (supportCard_le_sqNorm x)
      (Nat.cast_nonneg q)).trans ha

/-- A degree bound ensures that no coefficient wraps around modulo `q`. -/
theorem robustCenterPolynomial_natDegree_le (k h : ℕ) :
    (robustCenterPolynomial k h).natDegree ≤ k / 2 := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact (natDegree_pow_le).trans (by
      have hd : (1 - X : ℤ[X]).natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (by simp)
      simpa using Nat.mul_le_mul_left (k / 2) hd)

/-- The explicit vector recovers the entire centre polynomial. -/
theorem coefficientPolynomial_robustCenterCoeffs (k h : ℕ) (hkq : k / 2 < q) :
    coefficientPolynomial (robustCenterCoeffs (q := q) k h) = robustCenterPolynomial k h := by
  exact coefficientPolynomial_of_degree_lt _
    ((robustCenterPolynomial_natDegree_le k h).trans_lt hkq)

/-- The vector represents the centre in the integral cyclotomic quotient. -/
theorem classOf_robustCenterCoeffs (k h : ℕ) (hkq : k / 2 < q) :
    classOf (robustCenterCoeffs (q := q) k h) = robustCenter k h := by
  rw [← cyclotomicEval_coefficientPolynomial,
    coefficientPolynomial_robustCenterCoeffs k h hkq]
  simp [robustCenterPolynomial, robustCenter, pi]

/-- Evaluating the explicit representative at `X = 1` gives coefficient sum `h`. -/
theorem sum_robustCenterCoeffs (k h : ℕ) (hk : 2 ≤ k) (hkq : k / 2 < q) :
    ∑ a, robustCenterCoeffs (q := q) k h a = (h : ℤ) := by
  have hm : k / 2 ≠ 0 := by omega
  have he := congrArg (Polynomial.eval (1 : ℤ))
    (coefficientPolynomial_robustCenterCoeffs (q := q) k h hkq)
  simpa [coefficientPolynomial, robustCenterPolynomial, eval_finsetSum, hm] using he

/-- Equation (11), with its prescribed v2 weight and exact coefficient sum. -/
theorem sepCenter_representative (k : ℕ) (hk : sepK0 ≤ k) (hkq : 2 * k ≤ q) :
    classOf (robustCenterCoeffs (q := q) k (sepWeight k)) = sepCenter k ∧
      ∑ a, robustCenterCoeffs (q := q) k (sepWeight k) a = (sepWeight k : ℤ) := by
  have hk100 : 100 ≤ k := hk
  exact ⟨classOf_robustCenterCoeffs k (sepWeight k) (by omega),
    sum_robustCenterCoeffs k (sepWeight k) (by omega) (by omega)⟩

/-- Scalar multiplication of all integral coefficients scales the squared norm. -/
theorem coeffNormSq_mul_int (z : Coeff ℤ q) (t : ℤ) :
    coeffNormSq (fun a => t * z a) = t ^ 2 * coeffNormSq z := by
  rw [coeffNormSq_eq, coeffNormSq_eq]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- A short nonzero element cannot have every coefficient divisible by `q`. -/
theorem residuePolynomial_ne_zero_of_short (z : Coeff ℤ q)
    (hne : classOf z ≠ 0) (hq : 4 ≤ q) (hshort : normSq (classOf z) ≤ 3 * q) :
    residuePolynomial z ≠ 0 := by
  intro hz
  have hd : ∀ a, (q : ℤ) ∣ z a := by
    intro a
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have he := congrArg (fun f : (ZMod q)[X] => f.coeff a.val) hz
    rw [residuePolynomial_coeff, coeff_zero] at he
    exact he
  choose y hy using hd
  have he : z = fun a => (q : ℤ) * y a := funext hy
  have hnorm : normSq (classOf z) = (q : ℤ) ^ 2 * coeffNormSq y := by
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

private theorem support_sub_C_mul_le {R : Type*} [CommRing R]
    (P Q : R[X]) (h : R) :
    (P - C h * Q).support.card ≤ P.support.card + Q.support.card := by
  classical
  have hs : (P - C h * Q).support ⊆ P.support ∪ Q.support := by
    intro n hn
    simp only [Finset.mem_union, mem_support_iff] at hn ⊢
    contrapose! hn
    simp [coeff_sub, coeff_C_mul, hn]
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

private theorem exists_integral_ideal_norm (I : Ideal (IntegerRing q)) (v : IntegerRing q) :
    ∃ n : ℕ, ∃ a ∈ I, (n : ℤ) = normSq (v - a) := by
  refine ⟨(normSq v).toNat, 0, I.zero_mem, ?_⟩
  simpa using Int.toNat_of_nonneg (normSq_nonneg v)

/-- The squared distance to an integral ideal, as an attained integer minimum.
    The norm is the canonical form from the coefficient quotient model. -/
def idealDistanceSq (I : Ideal (IntegerRing q)) (v : IntegerRing q) : ℕ := by
  classical
  exact Nat.find (exists_integral_ideal_norm I v)

theorem idealDistanceSq_attained (I : Ideal (IntegerRing q)) (v : IntegerRing q) :
    ∃ a ∈ I, (idealDistanceSq I v : ℤ) = normSq (v - a) := by
  classical
  exact Nat.find_spec (exists_integral_ideal_norm I v)

section Prime
variable [Fact q.Prime]

omit [NeZero q] in
/-- Sparse multiplicity forces the first congruence in the robust-centre proof
to be an equality of polynomials. -/
theorem robust_sparse_polynomial (k m : ℕ) (hm : m ≤ k)
    (E W : (ZMod q)[X]) (hE : E.natDegree < q) (hW : W.natDegree < q)
    (h : ZMod q) (hs : E.support.card + W.support.card ≤ m)
    (hc : (X - 1 : (ZMod q)[X]) ^ k ∣ E - W * (C h + (1 - X) ^ m)) :
    E = C h * W := by
  have hdiv : (X - 1 : (ZMod q)[X]) ^ m ∣ E - C h * W := by
    have h1 := dvd_trans (pow_dvd_pow (X - 1 : (ZMod q)[X]) hm) hc
    have h2 : (X - 1 : (ZMod q)[X]) ^ m ∣ W * (1 - X) ^ m := by
      rw [show (1 - X : (ZMod q)[X]) = -(X - 1) by ring, neg_pow]
      exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
    convert dvd_add h1 h2 using 1; ring
  by_contra hn
  have hne : E - C h * W ≠ 0 := sub_ne_zero.mpr hn
  have hd : (E - C h * W).natDegree < q := by
    exact (natDegree_sub_le _ _).trans_lt (max_lt hE ((natDegree_C_mul_le _ _).trans_lt hW))
  have hm' := (le_rootMultiplicity_iff hne).mpr (by
    rw [show (C (1 : ZMod q) : (ZMod q)[X]) = 1 from C_1]
    exact hdiv)
  have hs' := support_sub_C_mul_le E W h
  have hsp := sparse_tools_ii (E - C h * W) hne hd
  omega

omit [NeZero q] in
/-- Once the sparse difference vanishes, the second multiplicity contradicts
the support bound for the nonzero short multiplier. -/
theorem robust_polynomial_contradiction (k m : ℕ) (hm : m ≤ k)
    (E W : (ZMod q)[X]) (hE : E.natDegree < q) (hW : W.natDegree < q)
    (h : ZMod q) (hW0 : W ≠ 0) (hs : E.support.card + W.support.card ≤ m)
    (hWs : W.support.card ≤ k - m)
    (hc : (X - 1 : (ZMod q)[X]) ^ k ∣ E - W * (C h + (1 - X) ^ m)) : False := by
  have he := robust_sparse_polynomial k m hm E W hE hW h hs hc
  rw [he] at hc
  have hdiv : (X - 1 : (ZMod q)[X]) ^ (k - m) ∣ W := by
    have hh : (X - 1 : (ZMod q)[X]) ^ k ∣ W * (X - 1) ^ m := by
      have hu : IsUnit ((-1 : (ZMod q)[X]) ^ m) := isUnit_neg_one.pow m
      have heq : C h * W - W * (C h + (1 - X) ^ m) =
          -(((-1 : (ZMod q)[X]) ^ m) * (W * (X - 1) ^ m)) := by
        rw [show (1 - X : (ZMod q)[X]) = -(X - 1) by ring, neg_pow]
        ring
      rw [heq, dvd_neg, hu.dvd_mul_left] at hc
      exact hc
    have heq : k = (k - m) + m := (Nat.sub_add_cancel hm).symm
    rw [heq, pow_add] at hh
    exact (mul_dvd_mul_iff_right (pow_ne_zero m (X_sub_C_ne_zero (1 : ZMod q)))).mp hh
  have hl := (le_rootMultiplicity_iff hW0).mpr (by
    rw [show (C (1 : ZMod q) : (ZMod q)[X]) = 1 from C_1]
    exact hdiv)
  have hu := sparse_tools_ii W hW0 hW
  omega

/-- Robust-centre separation, with explicit finite numerical bounds.
    This pointwise form implies the squared distance bound for the ideal. -/
theorem robust_center_explicit (k h : ℕ) (hk : sepK0 ≤ k) (hkq : k ≤ q - 1)
    (hq : 4 ≤ q) (w e : IntegerRing q) (hw : w ≠ 0) (hwn : normSq w ≤ 3 * q)
    (he : e - w * robustCenter k h ∈ ramifiedIdeal k) :
    (2 * k * q : ℤ) < 10 * normSq e := by
  have hk100 : 100 ≤ k := hk
  by_contra hbad
  have hen : 10 * normSq e ≤ (2 * k * q : ℤ) := le_of_not_gt hbad
  obtain ⟨ze, hze, hse⟩ := sparse_representative e
  obtain ⟨zw, hzw, hsw⟩ := sparse_representative w
  have hqpos : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  have hse' : 5 * supportCard ze ≤ 2 * k := by
    have hq0 : (0 : ℤ) ≤ q := le_of_lt hqpos
    have hh : (q : ℤ) * (5 * supportCard ze) ≤ (q : ℤ) * (2 * k) := by nlinarith
    have hh' := (mul_le_mul_iff_right₀ hqpos).mp hh
    exact_mod_cast hh'
  have hsw' : supportCard zw ≤ 6 := by
    have hh : (q : ℤ) * supportCard zw ≤ (q : ℤ) * 6 := by nlinarith
    exact_mod_cast (mul_le_mul_iff_right₀ hqpos).mp hh
  have hcong : (X - 1 : (ZMod q)[X]) ^ k ∣
      residuePolynomial ze - residuePolynomial zw * (C (h : ZMod q) + (1 - X) ^ (k / 2)) := by
    have heval : cyclotomicEval (q := q)
        (coefficientPolynomial ze - coefficientPolynomial zw * (C (h : ℤ) + (1 - X) ^ (k / 2))) ∈
          ramifiedIdeal k := by
      simpa [hze, hzw, robustCenter, pi] using he
    have hh := (cyclotomicEval_mem_ramifiedIdeal_iff k hkq _).mp heval
    simpa [residuePolynomial] using hh
  have hsE := residuePolynomial_support_le ze
  have hsW := residuePolynomial_support_le zw
  have hW0 := residuePolynomial_ne_zero_of_short zw (by rwa [hzw]) hq (by rwa [hzw])
  exact robust_polynomial_contradiction k (k / 2) (Nat.div_le_self _ _)
    (residuePolynomial ze) (residuePolynomial zw)
    (residuePolynomial_natDegree_lt ze) (residuePolynomial_natDegree_lt zw)
    (h : ZMod q) hW0 (by omega) (by omega) hcong

/-- Theorem 3.7 in coset form. The separation proof is independent of the weight. -/
theorem robust_center (k h : ℕ) (hk : sepK0 ≤ k) (hkq : 2 * k ≤ q)
    (w e : IntegerRing q) (hw : w ≠ 0) (hwn : normSq w ≤ 3 * q)
    (he : e - w * robustCenter k h ∈ ramifiedIdeal k) :
    (2 * k * q : ℤ) < 10 * normSq e := by
  have hk100 : 100 ≤ k := hk
  exact robust_center_explicit k h hk (by omega) (by omega) w e hw hwn he

/-- Pointwise form of v2 Theorem 3.7: `10 ‖wc-a‖² > 2kq`. -/
theorem robust_center_sub_ideal (k h : ℕ) (hk : sepK0 ≤ k) (hkq : 2 * k ≤ q)
    (w a : IntegerRing q) (hw : w ≠ 0) (hwn : normSq w ≤ 3 * q)
    (ha : a ∈ ramifiedIdeal k) :
    (2 * k * q : ℤ) < 10 * normSq (w * robustCenter k h - a) := by
  apply robust_center k h hk hkq w _ hw hwn
  convert (ramifiedIdeal k).neg_mem ha using 1; abel

/-- Squared ideal distance form of v2 Theorem 3.7, with arbitrary weight. -/
theorem robust_center_distance (k h : ℕ) (hk : sepK0 ≤ k) (hkq : 2 * k ≤ q)
    (w : IntegerRing q) (hw : w ≠ 0) (hwn : normSq w ≤ 3 * q) :
    (2 * k * q : ℤ) <
      10 * (idealDistanceSq (ramifiedIdeal k) (w * robustCenter k h) : ℤ) := by
  obtain ⟨a, ha, he⟩ := idealDistanceSq_attained (ramifiedIdeal k) (w * robustCenter k h)
  rw [he]
  exact robust_center_sub_ideal k h hk hkq w a hw hwn ha

/-- V2 Theorem 3.7 as the attained squared ideal distance `> L/10`. -/
theorem separation_distance_v2 (k : ℕ) (hk : sepK0 ≤ k) (hq : (2 * k) ^ sepC0 ≤ q)
    (w : IntegerRing q) (hw : w ≠ 0) (hwn : normSq w ≤ 3 * q) :
    (2 * k * q : ℤ) < 10 * (idealDistanceSq (ramifiedIdeal k) (w * sepCenter k) : ℤ) := by
  exact robust_center_distance k (sepWeight k) hk (by simpa [sepC0] using hq) w hw hwn

end Prime
end
end Rank2ModuleSVP
