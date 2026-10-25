import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Rank2ModuleSVP.Descent

/-! # Polynomial descent to the ramified ideal

Paper v2 Theorem 3.2: polynomial divisibility identifies the lifted
Reed–Solomon lattice with the ramified ideal and its cosets.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Rank2ModuleSVP
noncomputable section
open scoped BigOperators
open Polynomial
variable {q : ℕ} [NeZero q]

/-- The degree-`<q` polynomial attached to an integral coefficient vector. -/
def coefficientPolynomial (z : Coeff ℤ q) : ℤ[X] :=
  ∑ a : ZMod q, Polynomial.monomial a.val (z a)

/-- Reduction of the coefficient polynomial modulo `q`. -/
def residuePolynomial (z : Coeff ℤ q) : (ZMod q)[X] :=
  (coefficientPolynomial z).map (Int.castRingHom (ZMod q))

@[simp] theorem residuePolynomial_eq (z : Coeff ℤ q) :
    residuePolynomial z = ∑ a : ZMod q, Polynomial.monomial a.val (z a : ZMod q) := by
  simp [residuePolynomial, coefficientPolynomial, Polynomial.map_sum]

/-- The Euler differential operator; its eigenvalue on `X^a` is `a`. -/
def eulerOperator (R : Type*) [CommRing R] : R[X] →ₗ[R] R[X] :=
  (LinearMap.mulLeft R (X : R[X])).comp derivative

@[simp] theorem eulerOperator_apply {R : Type*} [CommRing R] (P : R[X]) :
    eulerOperator R P = X * derivative P := rfl

@[simp] theorem eulerOperator_monomial {R : Type*} [CommRing R] (n : ℕ) (c : R) :
    eulerOperator R (Polynomial.monomial n c) = Polynomial.monomial n ((n : R) * c) := by
  cases n with
  | zero => simp
  | succ n => simp [X_mul_monomial, mul_comm]

@[simp] theorem eulerOperator_pow_monomial {R : Type*} [CommRing R]
    (j n : ℕ) (c : R) :
    (eulerOperator R ^ j) (Polynomial.monomial n c) =
      Polynomial.monomial n ((n : R) ^ j * c) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, eulerOperator_monomial]
    congr 1
    rw [pow_succ]
    ring

/-- Power sums are evaluations of iterates of the Euler operator. -/
theorem syndrome_eq_euler (z : Coeff ℤ q) (k : ℕ) (j : Fin k) :
    syndrome k z j = ((eulerOperator (ZMod q) ^ j.val) (residuePolynomial z)).eval 1 := by
  simp [residuePolynomial_eq, map_sum, eval_finsetSum, syndrome, mul_comm]

@[simp] theorem residuePolynomial_coeff (z : Coeff ℤ q) (a : ZMod q) :
    (residuePolynomial z).coeff a.val = (z a : ZMod q) := by
  rw [residuePolynomial_eq, finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    have : b.val ≠ a.val := fun h => hba (ZMod.val_injective q h)
    simp [this]
  · simp

theorem residuePolynomial_natDegree_lt (z : Coeff ℤ q) :
    (residuePolynomial z).natDegree < q := by
  rw [residuePolynomial_eq]
  have hh : (∑ a : ZMod q, Polynomial.monomial a.val (z a : ZMod q)).natDegree ≤ q - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro a _
    exact (natDegree_monomial_le (z a : ZMod q)).trans (by have := ZMod.val_lt a; omega)
  have := NeZero.pos q
  omega

/-- Polynomial evaluation in the coefficient quotient. -/
def cyclotomicEval : ℤ[X] →+* IntegerRing q :=
  Polynomial.eval₂RingHom (Int.castRingHom _) (monomial 1)

@[simp] theorem cyclotomicEval_C (c : ℤ) :
    cyclotomicEval (q := q) (C c) = (c : IntegerRing q) := by
  simp [cyclotomicEval]

@[simp] theorem cyclotomicEval_X :
    cyclotomicEval (q := q) X = (monomial 1 : IntegerRing q) := by
  simp [cyclotomicEval]

@[simp] theorem monomial_zero : (monomial (0 : ZMod q) : IntegerRing q) = 1 := by
  exact (Ideal.Quotient.mk (cyclotomicIdeal : Ideal (Cyclic ℤ q))).map_one

@[simp] theorem monomial_add (a b : ZMod q) :
    (monomial (a + b) : IntegerRing q) = monomial a * monomial b := by
  simp [monomial, ← map_mul, AddMonoidAlgebra.single_mul_single]

theorem monomial_natCast (n : ℕ) :
    (monomial (n : ZMod q) : IntegerRing q) = (monomial 1 : IntegerRing q) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.cast_add, monomial_add, ih, pow_succ]

/-- Evaluation written as a sum of integer multiples of monomials. -/
theorem classOf_eq_sum_monomial (z : Coeff ℤ q) :
    classOf z = ∑ a : ZMod q, (z a : IntegerRing q) * monomial a := by
  unfold classOf monomial
  simp only [← map_intCast (Ideal.Quotient.mk (cyclotomicIdeal : Ideal (Cyclic ℤ q))),
    ← map_mul, ← map_sum]
  congr 1
  ext a
  simp [AddMonoidAlgebra.intCast_def, AddMonoidAlgebra.single_mul_single, Finsupp.single_apply]

@[simp] theorem cyclotomicEval_coefficientPolynomial (z : Coeff ℤ q) :
    cyclotomicEval (coefficientPolynomial z) = classOf z := by
  rw [classOf_eq_sum_monomial]
  simp [coefficientPolynomial, cyclotomicEval, eval₂_monomial,
    ← monomial_natCast]

/-- Polynomial evaluation is onto the integral cyclotomic ring. -/
theorem cyclotomicEval_surjective : Function.Surjective (cyclotomicEval (q := q)) := by
  intro v
  obtain ⟨z, rfl⟩ := classOf_surjective v
  exact ⟨coefficientPolynomial z, cyclotomicEval_coefficientPolynomial z⟩

/-- A degree-`<q` polynomial is recovered from its coefficient vector. -/
theorem coefficientPolynomial_of_degree_lt (P : ℤ[X]) (hP : P.natDegree < q) :
    coefficientPolynomial (fun a : ZMod q => P.coeff a.val) = P := by
  ext n
  simp only [coefficientPolynomial, finsetSum_coeff, coeff_monomial]
  by_cases hn : n < q
  · rw [Finset.sum_eq_single (n : ZMod q)]
    · simp [ZMod.val_natCast_of_lt hn]
    · intro b _ hb
      have hb' : b.val ≠ n := by
        intro he
        apply hb
        rw [← ZMod.natCast_zmod_val b, he]
      simp [hb']
    · simp
  · rw [Finset.sum_eq_zero]
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
    · intro a _
      have : a.val ≠ n := by have := ZMod.val_lt a; omega
      simp [this]

section Prime
variable [Fact q.Prime]

/-- The cyclotomic relation in the quotient model. -/
theorem cyclotomicEval_relation :
    cyclotomicEval (q := q) (Polynomial.cyclotomic q ℤ) = 0 := by
  have hval (i : Fin q) : ((ZMod.finEquiv q).toEquiv i).val = i.val := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  have hpoly : Polynomial.cyclotomic q ℤ = coefficientPolynomial (fun _ : ZMod q => 1) := by
    rw [cyclotomic_prime]
    unfold coefficientPolynomial
    rw [← (Equiv.sum_comp (ZMod.finEquiv q).toEquiv
      (fun a : ZMod q => Polynomial.monomial a.val (1 : ℤ)))]
    simp only [hval, ← C_mul_X_pow_eq_monomial, C_1, one_mul]
    rw [Fin.sum_univ_eq_sum_range]
  rw [hpoly, cyclotomicEval_coefficientPolynomial, ← classOf_zero]
  exact (classOf_eq_iff _ _).mpr ⟨1, fun _ => by simp⟩

/-- The evaluation kernel is generated by the prime cyclotomic polynomial. -/
theorem cyclotomicEval_eq_zero_iff (P : ℤ[X]) :
    cyclotomicEval (q := q) P = 0 ↔ Polynomial.cyclotomic q ℤ ∣ P := by
  constructor
  · intro hp
    let Q := P %ₘ Polynomial.cyclotomic q ℤ
    have hmon := cyclotomic.monic q ℤ
    have hd : Q.natDegree < q - 1 := by
      have hn : Polynomial.cyclotomic q ℤ ≠ 1 := by
        intro he
        have hh := congrArg Polynomial.natDegree he
        have hh' : q - 1 = 0 := by
          simpa [natDegree_cyclotomic, Nat.totient_prime (Fact.out : q.Prime)] using hh
        have := (Fact.out : q.Prime).two_le
        omega
      have hh := natDegree_modByMonic_lt P hmon hn
      simpa [Q, natDegree_cyclotomic, Nat.totient_prime (Fact.out : q.Prime)] using hh
    have hQ : cyclotomicEval (q := q) Q = 0 := by
      have he := congrArg (cyclotomicEval (q := q))
        (modByMonic_add_div P (Polynomial.cyclotomic q ℤ))
      simpa [map_add, map_mul, cyclotomicEval_relation, hp, Q] using he
    have hQzero : Q = 0 := by
      have hz := (classOf_eq_iff (fun a : ZMod q => Q.coeff a.val) 0).mp (by
        rw [← cyclotomicEval_coefficientPolynomial,
          coefficientPolynomial_of_degree_lt Q (by omega), classOf_zero]
        exact hQ)
      obtain ⟨c, hc⟩ := hz
      have hc0 : c = 0 := by
        have hh := hc ((q - 1 : ℕ) : ZMod q)
        simpa [ZMod.val_natCast_of_lt (by have := NeZero.pos q; omega),
          coeff_eq_zero_of_natDegree_lt hd] using hh.symm
      ext n
      by_cases hn : n < q
      · have hh := hc (n : ZMod q)
        simpa [ZMod.val_natCast_of_lt hn, hc0] using hh
      · simp [coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < n)]
    exact (modByMonic_eq_zero_iff_dvd hmon).mp hQzero
  · rintro ⟨Q, rfl⟩
    simp [cyclotomicEval_relation]

/-- Modulo `q`, the prime cyclotomic relation has exactly `q-1` roots at one. -/
theorem residue_cyclotomic :
    (Polynomial.cyclotomic q ℤ).map (Int.castRingHom (ZMod q)) =
      (X - 1 : (ZMod q)[X]) ^ (q - 1) := by
  rw [map_cyclotomic_int]
  apply mul_right_cancel₀ (show (X - 1 : (ZMod q)[X]) ≠ 0 from X_sub_C_ne_zero 1)
  rw [cyclotomic_prime_mul_X_sub_one, ← pow_succ,
    Nat.sub_add_cancel (show 1 ≤ q from NeZero.pos q), sub_pow_char, one_pow]

omit [NeZero q] in
private theorem C_q_dvd_of_map_zero (P : ℤ[X])
    (hP : P.map (Int.castRingHom (ZMod q)) = 0) : C (q : ℤ) ∣ P := by
  rw [C_dvd_iff_dvd_coeff]
  intro n
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa using congrArg (fun f : (ZMod q)[X] => f.coeff n) hP

/-- Total ramification, as divisibility in the actual quotient ring. -/
theorem pi_pow_dvd_prime : (pi : IntegerRing q) ^ (q - 1) ∣ (q : IntegerRing q) := by
  let N := q - 1
  let F := Polynomial.cyclotomic q ℤ - (X - 1 : ℤ[X]) ^ N
  have hF : F.map (Int.castRingHom (ZMod q)) = 0 := by
    dsimp [F, N]
    rw [Polynomial.map_sub, residue_cyclotomic]
    simp
  obtain ⟨G, hG⟩ := C_q_dvd_of_map_zero F hF
  have hG1 : G.eval 1 = 1 := by
    have he := congrArg (Polynomial.eval (1 : ℤ)) hG
    have hN : N ≠ 0 := by have := (Fact.out : q.Prime).two_le; omega
    simp [F, cyclotomic_prime, hN] at he
    have hq : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
    exact mul_left_cancel₀ hq (by simpa using he.symm)
  obtain ⟨B, hB⟩ : (X - 1 : ℤ[X]) ∣ G - 1 := by
    apply dvd_iff_isRoot.mpr
    simp [IsRoot, hG1]
  have hrel : (q : IntegerRing q) =
      (pi : IntegerRing q) * ((q : IntegerRing q) * cyclotomicEval B) -
        (-(pi : IntegerRing q)) ^ N := by
    have he := congrArg (cyclotomicEval (q := q)) hG
    have heB := congrArg (cyclotomicEval (q := q)) hB
    simp [F, cyclotomicEval_relation, pi] at he heB ⊢
    linear_combination - he - (q : IntegerRing q) * heB
  have aux : ∀ t ≤ N, (pi : IntegerRing q) ^ t ∣ (q : IntegerRing q) := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have hi := ih (by omega)
      rw [hrel]
      apply dvd_sub
      · have hh := mul_dvd_mul_left (pi : IntegerRing q) hi
        simpa [pow_succ', mul_assoc] using dvd_mul_of_dvd_left hh (cyclotomicEval B)
      · exact dvd_trans (pow_dvd_pow pi ht) (by rw [neg_pow]; exact dvd_mul_left _ _)
  exact aux N le_rfl

/-- The two principal ideals in the total ramification identity agree. -/
theorem total_ramification :
    Ideal.span {(q : IntegerRing q)} = ramifiedIdeal (q - 1) := by
  apply le_antisymm
  · rw [Ideal.span_singleton_le_iff_mem, ramifiedIdeal, Ideal.mem_span_singleton]
    exact pi_pow_dvd_prime
  · rw [ramifiedIdeal, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    have hF : (Polynomial.cyclotomic q ℤ - (X - 1 : ℤ[X]) ^ (q - 1)).map
        (Int.castRingHom (ZMod q)) = 0 := by
      rw [Polynomial.map_sub, residue_cyclotomic]
      simp
    obtain ⟨G, hG⟩ := C_q_dvd_of_map_zero _ hF
    have he := congrArg (cyclotomicEval (q := q)) hG
    have hh : (q : IntegerRing q) ∣ (-pi : IntegerRing q) ^ (q - 1) := by
      refine ⟨-cyclotomicEval G, ?_⟩
      simpa [pi, cyclotomicEval_relation] using congrArg Neg.neg he
    rw [neg_pow] at hh
    have hunit : IsUnit ((-1 : IntegerRing q) ^ (q - 1)) := (isUnit_neg_one).pow _
    exact (hunit.dvd_mul_left).mp hh

/-- Polynomial ideal preimage, before choosing degree-`<q` representatives. -/
theorem cyclotomicEval_mem_ramifiedIdeal_iff (k : ℕ) (hk : k ≤ q - 1) (P : ℤ[X]) :
    cyclotomicEval (q := q) P ∈ ramifiedIdeal k ↔
      (X - 1 : (ZMod q)[X]) ^ k ∣ P.map (Int.castRingHom (ZMod q)) := by
  constructor
  · intro hp
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp hp
    obtain ⟨Q, rfl⟩ := cyclotomicEval_surjective v
    have hz : cyclotomicEval (q := q) (P - (1 - X) ^ k * Q) = 0 := by
      simpa [pi, mul_comm] using sub_eq_zero.mpr hv.symm
    obtain ⟨S, hS⟩ := (cyclotomicEval_eq_zero_iff _).mp hz
    have he := congrArg (Polynomial.map (Int.castRingHom (ZMod q))) hS
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_one, Polynomial.map_X, residue_cyclotomic] at he
    have hd : (X - 1 : (ZMod q)[X]) ^ k ∣
        P.map (Int.castRingHom (ZMod q)) - (1 - X) ^ k * Q.map (Int.castRingHom (ZMod q)) := by
      rw [he]
      exact dvd_mul_of_dvd_left (pow_dvd_pow _ hk) _
    have hs : (X - 1 : (ZMod q)[X]) ^ k ∣ (1 - X) ^ k * Q.map (Int.castRingHom (ZMod q)) := by
      rw [show (1 - X : (ZMod q)[X]) = -(X - 1) by ring, neg_pow]
      exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    simpa only [sub_add_cancel] using dvd_add hd hs
  · rintro ⟨S, hS⟩
    obtain ⟨Q, hQ⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod q))
      ZMod.intCast_surjective S
    have hz : (P - (X - 1) ^ k * Q).map (Int.castRingHom (ZMod q)) = 0 := by
      simp [hQ, hS]
    obtain ⟨G, hG⟩ := C_q_dvd_of_map_zero _ hz
    have he := congrArg (cyclotomicEval (q := q)) hG
    have hpi : (-pi : IntegerRing q) ^ k * cyclotomicEval Q ∈ ramifiedIdeal k := by
      rw [ramifiedIdeal, Ideal.mem_span_singleton]
      rw [neg_pow]
      exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    have hq : (q : IntegerRing q) * cyclotomicEval G ∈ ramifiedIdeal k := by
      rw [ramifiedIdeal, Ideal.mem_span_singleton]
      exact dvd_mul_of_dvd_left
        (dvd_trans (pow_dvd_pow (pi : IntegerRing q) hk) (pi_pow_dvd_prime (q := q))) _
    have he' : cyclotomicEval (q := q) P =
        (-(pi : IntegerRing q)) ^ k * cyclotomicEval Q +
          (q : IntegerRing q) * cyclotomicEval G := by
      have he'' : cyclotomicEval (q := q) P -
          (-(pi : IntegerRing q)) ^ k * cyclotomicEval Q =
            (q : IntegerRing q) * cyclotomicEval G := by
        simpa [pi] using he
      exact (sub_eq_iff_eq_add.mp he'').trans (add_comm _ _)
    rw [he']
    exact (ramifiedIdeal k).add_mem hpi hq

omit [NeZero q] in
private theorem eq_C_of_derivative_zero (P : (ZMod q)[X])
    (h : P.derivative = 0) (hd : P.natDegree < q) : P = C (P.coeff 0) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    by_cases hn : n + 1 ≤ P.natDegree
    · have hcast : (n + 1 : ZMod q) ≠ 0 := by
        intro hh
        have hdvd := (ZMod.natCast_eq_zero_iff (n + 1) q).mp
          (by simpa only [Nat.cast_add, Nat.cast_one] using hh)
        exact (Nat.le_of_dvd (by omega) hdvd).not_gt (hn.trans_lt hd)
      have he := congrArg (fun f : (ZMod q)[X] => f.coeff n) h
      simp only [coeff_derivative, coeff_zero] at he
      simpa using (mul_eq_zero.mp he).resolve_right hcast
    · simp [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n + 1)]

omit [NeZero q] in
private theorem euler_ne_zero (P : (ZMod q)[X]) (hP : P ≠ 0)
    (hd : P.natDegree < q) (hr : P.IsRoot 1) :
    eulerOperator (ZMod q) P ≠ 0 := by
  intro h
  have hc := eq_C_of_derivative_zero P
    ((mul_eq_zero.mp h).resolve_left X_ne_zero) hd
  rw [hc] at hr
  simp only [IsRoot, eval_C] at hr
  exact hP (by simpa [hr] using hc)

private theorem euler_degree_lt (P : (ZMod q)[X]) (hP : P.natDegree < q) :
    (eulerOperator (ZMod q) P).natDegree < q := by
  by_cases h : P.derivative = 0
  · simp [h, NeZero.pos q]
  · rw [eulerOperator_apply, natDegree_X_mul h]
    have hp0 : P.natDegree ≠ 0 := by
      intro he
      apply h
      rw [eq_C_of_natDegree_eq_zero he, derivative_C]
    exact (Nat.succ_le_of_lt (natDegree_derivative_lt hp0)).trans_lt hP

omit [NeZero q] in
private theorem euler_multiplicity (P : (ZMod q)[X]) (hP : P ≠ 0)
    (hd : P.natDegree < q) (hr : P.IsRoot 1) :
    (eulerOperator (ZMod q) P).rootMultiplicity 1 = P.rootMultiplicity 1 - 1 := by
  have hm : P.rootMultiplicity 1 < q := (show P.rootMultiplicity 1 ≤ P.natDegree from by
    rw [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
    exact (natTrailingDegree_le_natDegree _).trans_eq (natDegree_taylor P 1)).trans_lt hd
  have hp : 0 < P.rootMultiplicity 1 := (rootMultiplicity_pos hP).mpr hr
  have hn : (P.rootMultiplicity 1 : ZMod q) ≠ 0 := by
    exact fun h => (Nat.le_of_dvd hp ((ZMod.natCast_eq_zero_iff _ _).mp h)).not_gt hm
  have hd' := derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hr
    (mem_nonZeroDivisors_iff_ne_zero.mpr hn)
  have hderiv : P.derivative ≠ 0 := by
    intro hz
    exact euler_ne_zero P hP hd hr (by rw [eulerOperator_apply, hz, mul_zero])
  rw [eulerOperator_apply,
    rootMultiplicity_mul (p := (X : (ZMod q)[X])) (q := P.derivative)
      (mul_ne_zero X_ne_zero hderiv),
    rootMultiplicity_eq_zero (show ¬ (X : (ZMod q)[X]).IsRoot 1 by simp [IsRoot]), zero_add]
  exact hd'

/-- The power-sum kernel is the `(X-1)^k` divisibility condition modulo `q`. -/
theorem liftedRS_iff_residue_dvd (k : ℕ) (z : Coeff ℤ q) :
    z ∈ liftedRS k ↔ (X - 1 : (ZMod q)[X]) ^ k ∣ residuePolynomial z := by
  have general (P : (ZMod q)[X]) (hd : P.natDegree < q) (n : ℕ) :
      (∀ j < n, ((eulerOperator (ZMod q) ^ j) P).eval 1 = 0) ↔
        (X - 1 : (ZMod q)[X]) ^ n ∣ P := by
    induction n generalizing P with
    | zero => simp
    | succ n ih =>
      by_cases hP : P = 0
      · simp [hP]
      have he := euler_degree_lt P hd
      have hh : (∀ j < n + 1, ((eulerOperator (ZMod q) ^ j) P).eval 1 = 0) ↔
          P.IsRoot 1 ∧
            ∀ j < n, ((eulerOperator (ZMod q) ^ j) (eulerOperator (ZMod q) P)).eval 1 = 0 := by
        constructor
        · intro h
          refine ⟨by simpa [IsRoot] using h 0 (by omega), ?_⟩
          intro j hj
          simpa [pow_succ, Module.End.mul_apply] using h (j + 1) (by omega)
        · rintro ⟨h0, h⟩ j hj
          cases j with
          | zero => simpa [IsRoot] using h0
          | succ j => simpa [pow_succ, Module.End.mul_apply] using h j (by omega)
      rw [hh, ih _ he]
      constructor
      · rintro ⟨hr, hn⟩
        have hE := euler_ne_zero P hP hd hr
        have hm := (le_rootMultiplicity_iff hE).mpr (by
          rw [show (C (1 : ZMod q) : (ZMod q)[X]) = 1 from C_1]
          exact hn)
        rw [euler_multiplicity P hP hd hr] at hm
        exact (le_rootMultiplicity_iff hP).mp (by
          have := (rootMultiplicity_pos hP).mpr hr
          omega)
      · intro hn
        have hm := (le_rootMultiplicity_iff hP).mpr (by
          rw [show (C (1 : ZMod q) : (ZMod q)[X]) = 1 from C_1]
          exact hn)
        have hr : P.IsRoot 1 := (rootMultiplicity_pos hP).mp (by omega)
        refine ⟨hr, ?_⟩
        have hdiv := pow_sub_one_dvd_derivative_of_pow_dvd hn
        simpa using dvd_mul_of_dvd_right hdiv X
  rw [← general _ (residuePolynomial_natDegree_lt z)]
  constructor
  · intro hz j hj
    simpa [syndrome_eq_euler] using congrFun hz ⟨j, hj⟩
  · intro hz
    ext j
    simpa [syndrome_eq_euler] using hz j.val j.isLt

/-- Equation `ideal-preimage` in the coefficient model. -/
theorem ideal_preimage (k : ℕ) (hk : k ≤ q - 1) (z : Coeff ℤ q) :
    classOf z ∈ ramifiedIdeal k ↔ z ∈ liftedRS k := by
  rw [← cyclotomicEval_coefficientPolynomial, cyclotomicEval_mem_ramifiedIdeal_iff k hk]
  exact (liftedRS_iff_residue_dvd k z).symm

/-- Paper `cyclotomic-descent`: the image is the principal ramified ideal. -/
theorem cyclotomic_descent (k : ℕ) (hk : k ≤ q - 1) :
    reedSolomonImage (q := q) k = (ramifiedIdeal (R := ℤ) (q := q) k).toAddSubgroup := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (ideal_preimage k hk z).mpr hz
  · intro hv
    obtain ⟨z, rfl⟩ := classOf_surjective v
    exact ⟨z, (ideal_preimage k hk z).mp hv, rfl⟩

/-- The coefficient-sum homomorphism. -/
def coefficientSum : Coeff ℤ q →+ ℤ where
  toFun z := ∑ a, z a
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

/-- The integral zero-sum hyperplane inside the lifted lattice. -/
def zeroSumLiftedRS (k : ℕ) : AddSubgroup (Coeff ℤ q) :=
  liftedRS k ⊓ (coefficientSum (q := q)).ker

/-- Evaluation gives the additive isomorphism on `1`-perpendicular. -/
def cyclotomicDescentEquiv (k : ℕ) (hk : 1 ≤ k) (hkq : k ≤ q - 1) :
    zeroSumLiftedRS (q := q) k ≃+ (ramifiedIdeal (R := ℤ) (q := q) k) := by
  let f : zeroSumLiftedRS (q := q) k →+ (ramifiedIdeal (R := ℤ) (q := q) k) :=
    { toFun := fun z => ⟨classOf z.val, (ideal_preimage k hkq z.val).mpr z.property.1⟩
      map_zero' := Subtype.ext classOf_zero
      map_add' := fun x y => Subtype.ext (classOf_add x.val y.val) }
  apply AddEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply classOf_injective_fixed_sum (congrArg Subtype.val hxy)
    exact (show (∑ a, x.val a) = 0 from x.property.2).trans
      (show (∑ a, y.val a) = 0 from y.property.2).symm
  · intro v
    have hv : v.val ∈ reedSolomonImage k := by
      rw [cyclotomic_descent k hkq]
      exact v.property
    obtain ⟨z, hz, hs, he⟩ := reedSolomonImage_zero_sum k hk hkq v.val hv
    exact ⟨⟨z, hz, hs⟩, Subtype.ext he⟩

/-- Canonical minimum of the ramified ideal, with the allowed BP input explicit. -/
theorem ramifiedIdeal_norm_lower (hBP : BennettPeikertMinimum) (k : ℕ)
    (hk : 1 ≤ k) (hkq : 2 * k ≤ q) (v : IntegerRing q)
    (hv : v ∈ ramifiedIdeal k) (hne : v ≠ 0) :
    (2 * k * q : ℤ) ≤ normSq v := by
  have hbound : k ≤ q - 1 := by have := (Fact.out : q.Prime).two_le; omega
  have hv' : v ∈ reedSolomonImage k := by
    rw [cyclotomic_descent k hbound]
    exact hv
  obtain ⟨z, hz, hs, rfl⟩ := reedSolomonImage_zero_sum k hk hbound v hv'
  exact liftedRS_norm_lower hBP Fact.out k hk hkq z hz hs hne

/-- A Vandermonde minor makes every syndrome attainable; the constant kernel
    then sets the integral coefficient sum to any compatible value. -/
theorem syndrome_surjective_fixed_sum (k : ℕ) (hk : 1 ≤ k) (hkq : k ≤ q - 1)
    (u : Fin k → ZMod q) (s : ℤ) (hs : (s : ZMod q) = u ⟨0, hk⟩) :
    ∃ z : Coeff ℤ q, syndrome k z = u ∧ (∑ a, z a) = s := by
  classical
  let a : Fin k → ZMod q := fun i => i.val
  have ha : Function.Injective a := by
    intro i j hij
    apply Fin.ext
    have hi : i.val < q := lt_of_lt_of_le i.isLt (by omega)
    have hj : j.val < q := lt_of_lt_of_le j.isLt (by omega)
    have hh := congrArg ZMod.val hij
    simpa [a, ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using hh
  let M := (Matrix.vandermonde a).transpose
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    change (Matrix.vandermonde a).transpose.det ≠ 0
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr ha
  obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hM u
  let r : ZMod q → ZMod q := fun b => ∑ i : Fin k, if a i = b then y i else 0
  let z0 : Coeff ℤ q := fun b => (r b).val
  have hz0 : syndrome k z0 = u := by
    ext j
    have hhy := congrFun hy j
    change (∑ b : ZMod q, (z0 b : ZMod q) * b ^ j.val) = u j
    simp only [z0, Int.cast_natCast, ZMod.natCast_zmod_val]
    simp only [r, Finset.sum_mul]
    rw [Finset.sum_comm]
    simpa [M, Matrix.mulVec, dotProduct, Matrix.vandermonde, ite_mul, mul_comm] using hhy
  have hd : (q : ℤ) ∣ (∑ b, z0 b) - s := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have he := congrFun hz0 ⟨0, hk⟩
    simpa [syndrome, ← Int.cast_sum, hs] using sub_eq_zero.mpr he
  obtain ⟨c, hc⟩ := hd
  let z := z0 - fun _ => c
  refine ⟨z, ?_, ?_⟩
  · have hconst := constant_mem_liftedRS k hkq c
    ext j
    have hh := congrFun hconst j
    have hh0 := congrFun hz0 j
    change (syndrome k z) j = u j
    simpa [z, syndrome, Int.cast_sub, sub_mul, Finset.sum_sub_distrib] using
      congrArg₂ (·-·) hh0 hh
  · dsimp [z]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    linarith

/-- Paper `coset-syndrome`, now for the actual principal ideal. -/
theorem ramified_coset_syndrome (k : ℕ) (hk : 1 ≤ k) (hkq : k ≤ q - 1)
    (x : Coeff ℤ q) (v : IntegerRing q) :
    v - classOf x ∈ ramifiedIdeal k ↔
      ∃! z : Coeff ℤ q, classOf z = v ∧ syndrome k z = syndrome k x ∧
        (∑ a, z a) = ∑ a, x a := by
  simpa [cyclotomic_descent k hkq] using coset_syndrome k hk hkq x v

end Prime
end
end Rank2ModuleSVP
