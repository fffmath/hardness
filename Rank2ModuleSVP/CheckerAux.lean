import Mathlib.RingTheory.Ideal.Quotient.Operations
import Rank2ModuleSVP.PrimeCyclotomic

/-! # Canonical forms and checker inequalities

Coefficient proofs of the trace, adjointness and quadratic estimates used by
the checker in paper v2 §4, including the positive-checker identity of Lemma 4.2.
No complex embedding or field structure on the quotient is used.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Rank2ModuleSVP.Checker
open scoped BigOperators
noncomputable section
open Rank2ModuleSVP
variable {q : ℕ} [NeZero q]
variable {R : Type*} [CommRing R]

@[simp] theorem conjugate_add (v w : Cyclotomic R q) :
    conjugate (v + w) = conjugate v + conjugate w := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  obtain ⟨y, rfl⟩ := classOf_surjective w
  simp only [← classOf_add, conjugate_classOf]
  rfl

@[simp] theorem conjugate_neg (v : Cyclotomic R q) :
    conjugate (-v) = -conjugate v := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  simp only [← classOf_neg, conjugate_classOf]
  rfl

@[simp] theorem conjugate_mul (v w : Cyclotomic R q) :
    conjugate (v * w) = conjugate v * conjugate w := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  obtain ⟨y, rfl⟩ := classOf_surjective w
  rw [classOf_mul, conjugate_classOf, conjugate_classOf,
    conjugate_classOf, classOf_mul]
  congr 1
  funext a
  change (∑ b, x b * y (-a - b)) = ∑ b, x (-b) * y (-(a - b))
  have he := (Equiv.sum_comp (Equiv.neg (ZMod q))
    (fun b => x b * y (-a - b))).symm
  change (∑ b, x b * y (-a - b)) = ∑ b, x (-b) * y (-a - (-b)) at he
  rw [he]
  congr 1
  funext b
  rw [show - a - (-b) = -(a - b) by abel]

theorem monomial_eq_classOf (j : ZMod q) :
    (monomial j : Cyclotomic R q) = classOf (fun a => if a = j then 1 else 0) := by
  unfold monomial classOf
  congr 1
  ext a
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, coeff_ofCoeff]
  split_ifs <;> simp_all

@[simp] theorem conjugate_monomial (j : ZMod q) :
    conjugate (monomial j : Cyclotomic R q) = monomial (-j) := by
  rw [monomial_eq_classOf, monomial_eq_classOf, conjugate_classOf]
  congr 1
  funext a
  simp only [conjugateCoeff]
  have he : -a = j ↔ a = -j := by constructor <;> intro h <;> simpa using congrArg Neg.neg h
  simp [he]

theorem conjugate_sum {ι : Type*} (s : Finset ι) (f : ι → Cyclotomic R q) :
    conjugate (∑ i ∈ s, f i) = ∑ i ∈ s, conjugate (f i) := by
  classical
  have hz : conjugate (0 : Cyclotomic R q) = 0 := by
    rw [← classOf_zero, conjugate_classOf]
    rfl
  induction s using Finset.induction_on with
  | empty => simpa using hz
  | @insert i s hi ih => simp [Finset.sum_insert, hi, ih]

/-- The coefficient formula for the field trace. -/
def traceCoeff (x : Coeff R q) : R := (q : R) * x 0 - ∑ a, x a

private theorem traceCoeff_class_eq {x y : Coeff R q}
    (h : classOf x = classOf y) : traceCoeff x = traceCoeff y := by
  obtain ⟨c, hc⟩ := (classOf_eq_iff _ _).mp h
  have hx : x = fun a => y a + c := by
    funext a; have := hc a; linear_combination this
  rw [hx]
  simp only [traceCoeff, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul]
  ring

/-- Trace on the cyclotomic quotient, induced by the coefficient trace. -/
def trace (v : Cyclotomic R q) : R :=
  traceCoeff (fun a => (Ideal.Quotient.mk_surjective v).choose.coeff a)

@[simp] theorem trace_classOf (x : Coeff R q) : trace (classOf x) = traceCoeff x := by
  apply traceCoeff_class_eq
  simpa only [classOf, ofCoeff_coeff] using
    (Ideal.Quotient.mk_surjective (classOf x)).choose_spec

@[simp] theorem trace_add (v w : Cyclotomic R q) : trace (v + w) = trace v + trace w := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  obtain ⟨y, rfl⟩ := classOf_surjective w
  simp [← classOf_add, traceCoeff, Finset.sum_add_distrib]
  ring

@[simp] theorem trace_neg (v : Cyclotomic R q) : trace (-v) = -trace v := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  simp [← classOf_neg, traceCoeff, Finset.sum_neg_distrib]
  ring

@[simp] theorem trace_zero : trace (0 : Cyclotomic R q) = 0 := by
  rw [← classOf_zero, trace_classOf]; simp [traceCoeff]

@[simp] theorem trace_sub (v w : Cyclotomic R q) : trace (v - w) = trace v - trace w := by
  simp [sub_eq_add_neg]

private theorem sum_convolution (x y : Coeff R q) :
    (∑ a, ∑ b, x b * y (a - b)) = (∑ a, x a) * (∑ a, y a) := by
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hs (b : ZMod q) : (∑ a, y (a - b)) = ∑ a, y a :=
    Equiv.sum_comp (Equiv.subRight b) y
  simp_rw [hs]
  rw [Finset.sum_mul]

/-- The canonical bilinear form descends to the quotient. -/
def inner (v w : Cyclotomic R q) : R := trace (v * conjugate w)

@[simp] theorem inner_classOf (x y : Coeff R q) :
    inner (classOf x) (classOf y) = canonicalForm x y := by
  rw [inner, conjugate_classOf, classOf_mul, trace_classOf, traceCoeff,
    sum_convolution]
  simp only [conjugateCoeff, zero_sub, neg_neg]
  have hs : (∑ a, y (-a)) = ∑ a, y a := Equiv.sum_comp (Equiv.neg _) y
  rw [hs]
  rfl

theorem inner_symm (v w : Cyclotomic R q) : inner v w = inner w v := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  obtain ⟨y, rfl⟩ := classOf_surjective w
  simpa using canonicalForm_symm x y

@[simp] theorem inner_self (v : Cyclotomic R q) : inner v v = normSq v := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  simp [coeffNormSq]

@[simp] theorem inner_add_left (u v w : Cyclotomic R q) :
    inner (u + v) w = inner u w + inner v w := by simp [inner, add_mul]

@[simp] theorem inner_neg_left (v w : Cyclotomic R q) :
    inner (-v) w = -inner v w := by
  rw [inner, _root_.neg_mul, trace_neg]
  rfl

@[simp] theorem inner_add_right (u v w : Cyclotomic R q) :
    inner u (v + w) = inner u v + inner u w := by simp [inner, mul_add]

@[simp] theorem inner_neg_right (v w : Cyclotomic R q) :
    inner v (-w) = -inner v w := by
  rw [inner, conjugate_neg, _root_.mul_neg, trace_neg]
  rfl

/-- Multiplication and conjugation are adjoint for the canonical form. -/
theorem inner_adjoint (u v w : Cyclotomic R q) :
    inner (u * v) w = inner v (conjugate u * w) := by
  simp only [inner, conjugate_mul, conjugate_conjugate]
  congr 1
  ring

theorem normSq_add (v w : Cyclotomic R q) :
    normSq (v + w) = normSq v + 2 * inner v w + normSq w := by
  rw [← inner_self, inner_add_left, inner_add_right, inner_add_right,
    inner_self, inner_self, inner_symm w v]
  ring

theorem normSq_sub (v w : Cyclotomic R q) :
    normSq (v - w) = normSq v - 2 * inner v w + normSq w := by
  rw [sub_eq_add_neg, normSq_add, inner_neg_right, normSq_neg]
  ring

@[simp] theorem normSq_zero : normSq (0 : Cyclotomic R q) = 0 := by
  rw [← classOf_zero, normSq_classOf]
  simp [coeffNormSq_eq]

@[simp] theorem conjugate_one : conjugate (1 : Cyclotomic R q) = 1 := by
  have h := conjugate_mul (1 : Cyclotomic R q) (conjugate 1)
  simpa only [one_mul, conjugate_conjugate, mul_one] using h.symm

section Rational

@[simp] theorem classOf_smul (c : ℚ) (x : Coeff ℚ q) :
    classOf (c • x) = c • classOf x := by
  change (Ideal.Quotient.mkₐ ℚ _ : Cyclic ℚ q →ₐ[ℚ] RationalRing q)
    (ofCoeff (c • x)) = _
  rw [show ofCoeff (c • x) = c • ofCoeff x by ext a; rfl, map_smul]
  rfl

@[simp] theorem conjugate_smul (c : ℚ) (v : RationalRing q) :
    conjugate (c • v) = c • conjugate v := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  rw [← classOf_smul, conjugate_classOf, conjugate_classOf, ← classOf_smul]
  rfl

@[simp] theorem inner_smul_left (c : ℚ) (v w : RationalRing q) :
    inner (c • v) w = c * inner v w := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  obtain ⟨y, rfl⟩ := classOf_surjective w
  simp only [← classOf_smul, inner_classOf, canonicalForm, Pi.smul_apply,
    smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

@[simp] theorem inner_smul_right (c : ℚ) (v w : RationalRing q) :
    inner v (c • w) = c * inner v w := by
  rw [inner_symm, inner_smul_left, inner_symm]

@[simp] theorem normSq_smul (c : ℚ) (v : RationalRing q) :
    normSq (c • v) = c ^ 2 * normSq v := by
  rw [← inner_self, inner_smul_left, inner_smul_right, inner_self]
  ring

@[simp] theorem inner_zero_left (w : RationalRing q) : inner 0 w = 0 := by
  simp [inner]

@[simp] theorem inner_zero_right (w : RationalRing q) : inner w 0 = 0 := by
  rw [inner_symm, inner_zero_left]

theorem inner_sum_left {ι : Type*} (s : Finset ι) (f : ι → RationalRing q)
    (w : RationalRing q) : inner (∑ i ∈ s, f i) w = ∑ i ∈ s, inner (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert, hi, ih]

theorem inner_sum_right {ι : Type*} (s : Finset ι) (f : ι → RationalRing q)
    (w : RationalRing q) : inner w (∑ i ∈ s, f i) = ∑ i ∈ s, inner w (f i) := by
  rw [inner_symm, inner_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  exact inner_symm _ _

theorem inner_classOf_monomial (x : Coeff ℚ q) (j : ZMod q) :
    inner (classOf x) (monomial j) = (q : ℚ) * x j-∑ a, x a := by
  rw [monomial_eq_classOf, inner_classOf]
  simp [canonicalForm, mul_ite]

theorem normSq_one : normSq (1 : RationalRing q) = (q : ℚ) - 1 := by
  have hm : (monomial 0 : RationalRing q) = 1 := by
    simp [monomial, ← AddMonoidAlgebra.one_def]
  rw [← hm, monomial_eq_classOf, normSq_classOf, coeffNormSq_eq]
  simp

/-- Extension of scalars from the integral coefficient quotient. -/
def rationalize : IntegerRing q →+* RationalRing q :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (cyclotomicIdeal : Ideal (Cyclic ℚ q))).comp
      (AddMonoidAlgebra.mapRingHom (ZMod q) (Int.castRingHom ℚ))) (by
    intro a ha
    obtain ⟨c, hc⟩ := mem_cyclotomicIdeal_iff a |>.mp ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply mem_cyclotomicIdeal_iff _ |>.mpr
    exact ⟨(c : ℚ), fun b => by simp [hc b]⟩)

@[simp] theorem rationalize_classOf (x : Coeff ℤ q) :
    rationalize (classOf x) = classOf (fun a => (x a : ℚ)) := by
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  congr 1
  ext a
  simp

@[simp] theorem rationalize_conjugate (v : IntegerRing q) :
    rationalize (conjugate v) = conjugate (rationalize v) := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  simp only [conjugate_classOf, rationalize_classOf]
  rfl

@[simp] theorem rationalize_monomial (a : ZMod q) :
    rationalize (monomial a : IntegerRing q) = (monomial a : RationalRing q) := by
  rw [monomial_eq_classOf, rationalize_classOf, monomial_eq_classOf]
  congr 1
  funext b
  split_ifs <;> norm_num

@[simp] theorem normSq_rationalize (z : IntegerRing q) :
    normSq (rationalize z) = ((normSq z : ℤ) : ℚ) := by
  obtain ⟨x, rfl⟩ := classOf_surjective z
  simp only [rationalize_classOf, normSq_classOf, coeffNormSq_eq]
  push_cast
  rfl

end Rational

section RationalEstimates

/-- Young's inequality, obtained directly from positivity of the canonical form. -/
theorem inner_young (r : ℚ) (hr : 0 < r) (v w : RationalRing q) :
    2 * inner v w ≤ r * normSq v + r⁻¹ * normSq w := by
  have h := normSq_nonneg (r • v - w)
  rw [normSq_sub, normSq_smul, inner_smul_left] at h
  apply (mul_le_mul_iff_right₀ hr).mp
  have he : r * (r * normSq v + r⁻¹ * normSq w) = r ^ 2 * normSq v + normSq w := by
    have hi : r⁻¹ * r = 1 := inv_mul_cancel₀ (ne_of_gt hr)
    calc
      r * (r * normSq v + r⁻¹ * normSq w) =
        r ^ 2 * normSq v + (r⁻¹ * r) * normSq w := by ring
      _ = _ := by rw [hi, one_mul]
  rw [he]
  nlinarith [h]

theorem normSq_sum_le_card_sum {ι : Type*} (s : Finset ι)
    (f : ι → RationalRing q) :
    normSq (∑ i ∈ s, f i) ≤ (s.card : ℚ) * (∑ i ∈ s, normSq (f i)) := by
  have hh : (∑ i ∈ s, ∑ j ∈ s, 2 * inner (f i) (f j)) ≤
      ∑ i ∈ s, ∑ j ∈ s, (normSq (f i) + normSq (f j)) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    simpa using inner_young 1 (by norm_num) (f i) (f j)
  have he : normSq (∑ i ∈ s, f i) = ∑ i ∈ s, ∑ j ∈ s, inner (f i) (f j) := by
    rw [← inner_self, inner_sum_left]
    simp_rw [inner_sum_right]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul] at hh
  rw [← he] at hh
  linarith

theorem normSq_sum_monomial_mul_le {ι : Type*} (s : Finset ι)
    (a : ι → ZMod q) (w : RationalRing q) :
    normSq ((∑ i ∈ s, monomial (a i)) * w) ≤ (s.card : ℚ) ^ 2 * normSq w := by
  rw [Finset.sum_mul]
  have hh := normSq_sum_le_card_sum s (fun i => monomial (a i) * w)
  simpa [normSq_monomial_mul, pow_two, mul_assoc] using hh

/-- The positive integral checker multiplier, extended to the rational quotient. -/
def positiveChecker (Q : ℚ) (g : RationalRing q) : RationalRing q :=
  Q • 1 + g ^ 2

/-- Self-adjointness converts the cross term to a squared norm. -/
theorem inner_sq_mul (g y : RationalRing q) (hg : conjugate g = g) :
    inner y (g ^ 2 * y) = normSq (g * y) := by
  rw [← inner_self (g * y), inner_adjoint, hg]
  congr 1
  ring

/-- Lemma 4.2's exact identity, proved in the quotient coefficient model. -/
theorem positiveChecker_norm_exact (Q : ℚ) (g y : RationalRing q)
    (hg : conjugate g = g) :
    normSq (positiveChecker Q g * y) =
      Q ^ 2 * normSq y + 2 * Q * normSq (g * y) + normSq (g ^ 2 * y) := by
  rw [positiveChecker, add_mul, smul_mul_assoc, one_mul, normSq_add,
    normSq_smul, inner_smul_left, inner_sq_mul g y hg]
  ring

theorem positiveChecker_norm_lower (Q : ℚ) (hQ : 0 ≤ Q)
    (g y : RationalRing q) (hg : conjugate g = g) :
    Q ^ 2 * normSq y ≤ normSq (positiveChecker Q g * y) := by
  rw [positiveChecker_norm_exact Q g y hg]
  have := normSq_nonneg (g ^ 2 * y)
  have := mul_nonneg (show 0 ≤ 2 * Q by positivity) (normSq_nonneg (g * y))
  linarith

theorem positiveChecker_value_norm (Q : ℚ) (g v y : RationalRing q)
    (hg : conjugate g = g) :
    normSq (positiveChecker Q g * y - v) =
      Q ^ 2 * normSq y + 2 * Q * (normSq (g * y) - inner y v) + normSq (g ^ 2 * y - v) := by
  have he : positiveChecker Q g * y - v = Q • y + (g ^ 2 * y - v) := by
    simp [positiveChecker, add_mul]
    ring
  rw [he, normSq_add, normSq_smul, inner_smul_left]
  have hi : inner y (g ^ 2 * y - v) = normSq (g * y) - inner y v := by
    rw [sub_eq_add_neg, inner_add_right, inner_neg_right, inner_sq_mul g y hg]
    ring
  rw [hi]
  ring

/-- A weighted squared triangle bound suited to Q = 128 W⁴ h. -/
theorem normSq_sub_le_three_halves (v w : RationalRing q) :
    normSq (v - w) ≤ (3 / 2 : ℚ) * normSq v + 3 * normSq w := by
  have h := inner_young (1 / 2) (by norm_num) v (-w)
  simp only [inner_neg_right, normSq_neg] at h
  norm_num at h
  rw [normSq_sub]
  linarith

/-- A model-independent version of the paper's stability estimate. The two
premises are precisely the multiplier bounds proved for U and V. -/
theorem global_stability_exact (u v y w : RationalRing q) (Γ ν : ℚ)
    (hν : 0 < ν) (hν1 : ν < 1)
    (hu : normSq y ≤ normSq (u * y))
    (hv : normSq (v * w) ≤ ν ^ 2 * Γ ^ 2 * normSq w) :
    (1 - ν) * (normSq y + Γ ^ 2 * normSq w) ≤
      normSq (u * y - v * w) + Γ ^ 2 * normSq w := by
  have hy := inner_young ν hν (u * y) (v * w)
  have hn := normSq_nonneg (v * w)
  have hb : ν⁻¹ * normSq (v * w) ≤ ν * Γ ^ 2 * normSq w := by
    have hm := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hν.le)
    have hi : ν⁻¹ * ν = 1 := inv_mul_cancel₀ (ne_of_gt hν)
    calc
      ν⁻¹ * normSq (v * w) ≤ ν⁻¹ * (ν ^ 2 * Γ ^ 2 * normSq w) := hm
      _ = ν * Γ ^ 2 * normSq w := by
        calc
          ν⁻¹ * (ν ^ 2 * Γ ^ 2 * normSq w) = (ν⁻¹ * ν) * ν * Γ ^ 2 * normSq w := by ring
          _ = _ := by rw [hi, one_mul]
  rw [normSq_sub]
  nlinarith [mul_nonneg (show 0 ≤ 1 - ν by linarith) (sub_nonneg.mpr hu)]

end RationalEstimates
end
end Rank2ModuleSVP.Checker
