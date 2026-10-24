import Rank2ModuleSVP.GaussSum
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Coefficient proofs of the trace, adjointness and quadratic estimates used by
 the checker. No complex embedding or field structure on the quotient is used. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Rank2ModuleSVP.Checker
open scoped BigOperators
noncomputable section
open Rank2ModuleSVP
variable {q : ℕ} [NeZero q]
variable {R : Type*} [CommRing R]

@[simp] theorem conjugate_add (v w : Cyclotomic R q) :
    conjugate (v+w) = conjugate v + conjugate w := by
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
    conjugate (v*w) = conjugate v * conjugate w := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  obtain ⟨y, rfl⟩ := classOf_surjective w
  rw [classOf_mul, conjugate_classOf, conjugate_classOf,
    conjugate_classOf, classOf_mul]
  congr 1
  funext a
  change (∑ b, x b * y (-a-b)) = ∑ b, x (-b) * y (-(a-b))
  have he := (Equiv.sum_comp (Equiv.neg (ZMod q))
    (fun b => x b * y (-a-b))).symm
  change (∑ b, x b * y (-a-b)) = ∑ b, x (-b) * y (-a-(-b)) at he
  rw [he]
  congr 1
  funext b
  rw [show -a-(-b) = -(a-b) by abel]


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

def trace (v : Cyclotomic R q) : R :=
  traceCoeff (fun a => (Ideal.Quotient.mk_surjective v).choose.coeff a)

@[simp] theorem trace_classOf (x : Coeff R q) : trace (classOf x) = traceCoeff x := by
  apply traceCoeff_class_eq
  simpa only [classOf, ofCoeff_coeff] using
    (Ideal.Quotient.mk_surjective (classOf x)).choose_spec

@[simp] theorem trace_add (v w : Cyclotomic R q) : trace (v+w) = trace v + trace w := by
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

@[simp] theorem trace_sub (v w : Cyclotomic R q) : trace (v-w) = trace v - trace w := by
  simp [sub_eq_add_neg]

private theorem sum_convolution (x y : Coeff R q) :
    (∑ a, ∑ b, x b * y (a-b)) = (∑ a, x a) * (∑ a, y a) := by
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hs (b : ZMod q) : (∑ a, y (a-b)) = ∑ a, y a :=
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
    inner (u+v) w = inner u w + inner v w := by simp [inner, add_mul]

@[simp] theorem inner_neg_left (v w : Cyclotomic R q) :
    inner (-v) w = -inner v w := by simp [inner, _root_.neg_mul, _root_.mul_neg]

@[simp] theorem inner_add_right (u v w : Cyclotomic R q) :
    inner u (v+w) = inner u v + inner u w := by simp [inner, mul_add]

@[simp] theorem inner_neg_right (v w : Cyclotomic R q) :
    inner v (-w) = -inner v w := by simp [inner, _root_.neg_mul, _root_.mul_neg]

/-- Multiplication and conjugation are adjoint for the canonical form. -/
theorem inner_adjoint (u v w : Cyclotomic R q) :
    inner (u*v) w = inner v (conjugate u*w) := by
  simp only [inner, conjugate_mul, conjugate_conjugate]
  congr 1
  ring

theorem normSq_add (v w : Cyclotomic R q) :
    normSq (v+w) = normSq v + 2*inner v w + normSq w := by
  rw [← inner_self, inner_add_left, inner_add_right, inner_add_right,
    inner_self, inner_self, inner_symm w v]
  ring

theorem normSq_sub (v w : Cyclotomic R q) :
    normSq (v-w) = normSq v - 2*inner v w + normSq w := by
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
    normSq (c • v) = c^2 * normSq v := by
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
    inner (classOf x) (monomial j) = (q : ℚ)*x j-∑ a, x a := by
  rw [monomial_eq_classOf, inner_classOf]
  simp [canonicalForm, mul_ite]

theorem normSq_one : normSq (1 : RationalRing q) = (q : ℚ)-1 := by
  have hm : (monomial 0 : RationalRing q) = 1 := by
    simp [monomial, ← AddMonoidAlgebra.one_def]
  rw [← hm, monomial_eq_classOf, normSq_classOf, coeffNormSq_eq]
  simp

/-- Extension of scalars, used to transport the already proved integral
Gauss-sum identities. -/
def rationalize : IntegerRing q →+* RationalRing q :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (cyclotomicIdeal : Ideal (Cyclic ℚ q))).comp
      (AddMonoidAlgebra.mapRingHom (ZMod q) (Int.castRingHom ℚ))) (by
    intro a ha
    obtain ⟨c,hc⟩ := mem_cyclotomicIdeal_iff a |>.mp ha
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
  obtain ⟨x,rfl⟩ := classOf_surjective v
  simp only [conjugate_classOf, rationalize_classOf]
  rfl

variable [Fact q.Prime]

def thetaQ : RationalRing q := rationalize (theta (q := q))

theorem conjugate_thetaQ (hq : q % 4 = 3) : conjugate (thetaQ (q := q)) = -thetaQ := by
  simpa [thetaQ, ← rationalize_conjugate] using congrArg rationalize (conjugate_theta hq)

theorem thetaQ_sq (hq : q % 4 = 3) : thetaQ (q := q)^2 = -(q : RationalRing q) := by
  simpa [thetaQ] using congrArg rationalize (theta_sq hq)

end Rational

section RationalEstimates

/-- Young's inequality, obtained directly from positivity of the canonical form. -/
theorem inner_young (r : ℚ) (hr : 0 < r) (v w : RationalRing q) :
    2*inner v w ≤ r*normSq v + r⁻¹*normSq w := by
  have h := normSq_nonneg (r • v-w)
  rw [normSq_sub, normSq_smul, inner_smul_left] at h
  apply (mul_le_mul_iff_right₀ hr).mp
  have he : r*(r*normSq v+r⁻¹*normSq w) = r^2*normSq v+normSq w := by
    have hi : r⁻¹*r = 1 := inv_mul_cancel₀ (ne_of_gt hr)
    calc
      r*(r*normSq v+r⁻¹*normSq w) =
        r^2*normSq v+(r⁻¹*r)*normSq w := by ring
      _ = _ := by rw [hi, one_mul]
  rw [he]
  nlinarith [h]

theorem normSq_sum_le_card_sum {ι : Type*} (s : Finset ι)
    (f : ι → RationalRing q) :
    normSq (∑ i ∈ s, f i) ≤ (s.card : ℚ)*(∑ i ∈ s, normSq (f i)) := by
  have hh : (∑ i ∈ s, ∑ j ∈ s, 2*inner (f i) (f j)) ≤
      ∑ i ∈ s, ∑ j ∈ s, (normSq (f i)+normSq (f j)) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    simpa using inner_young 1 (by norm_num) (f i) (f j)
  have he : normSq (∑ i ∈ s, f i) = ∑ i ∈ s, ∑ j ∈ s, inner (f i) (f j) := by
    rw [← inner_self, inner_sum_left]
    simp_rw [inner_sum_right]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Finset.sum_mul] at hh
  rw [← he] at hh
  linarith

theorem normSq_sum_monomial_mul_le {ι : Type*} (s : Finset ι)
    (a : ι → ZMod q) (w : RationalRing q) :
    normSq ((∑ i ∈ s, monomial (a i))*w) ≤ (s.card : ℚ)^2*normSq w := by
  rw [Finset.sum_mul]
  have hh := normSq_sum_le_card_sum s (fun i => monomial (a i)*w)
  simpa [normSq_monomial_mul, pow_two, mul_assoc] using hh

/-- Cauchy--Schwarz for the descended canonical form. -/
theorem inner_sq_le (v w : RationalRing q) : (inner v w)^2 ≤ normSq v*normSq w := by
  by_cases hw : normSq w = 0
  · have hw0 := (normSq_eq_zero_iff w).mp hw
    subst w
    simp
  have hwpos : 0 < normSq w := lt_of_le_of_ne (normSq_nonneg w) (Ne.symm hw)
  have hh := normSq_nonneg (normSq w • v-inner v w • w)
  rw [normSq_sub, normSq_smul, normSq_smul, inner_smul_left, inner_smul_right] at hh
  have he : (normSq w)^2*normSq v-
      2*(normSq w*(inner v w*inner v w))+(inner v w)^2*normSq w =
      normSq w*(normSq v*normSq w-(inner v w)^2) := by ring
  rw [he] at hh
  have hnonneg : 0 ≤ normSq v*normSq w-(inner v w)^2 := by
    by_contra hn
    have hneg := mul_neg_of_pos_of_neg hwpos (lt_of_not_ge hn)
    linarith
  linarith

/-- A finite dimensional model is enough to invert any norm-expanding multiplier. -/
def classLinear : Coeff ℚ q →ₗ[ℚ] RationalRing q where
  toFun := classOf
  map_add' := classOf_add
  map_smul' := classOf_smul

instance finiteDimensional : FiniteDimensional ℚ (RationalRing q) :=
  Module.Finite.of_surjective (classLinear (q := q)) classOf_surjective

theorem isUnit_of_norm_expanding (u : RationalRing q)
    (hu : ∀ y, normSq y ≤ normSq (u*y)) : IsUnit u := by
  have hinj : Function.Injective (LinearMap.mulLeft ℚ u) := by
    intro v w h
    apply sub_eq_zero.mp
    apply (normSq_eq_zero_iff _).mp
    have hh := hu (v-w)
    have hz : u*(v-w) = 0 := by simpa [mul_sub] using sub_eq_zero.mpr h
    rw [hz] at hh
    have hn := normSq_nonneg (v-w)
    have h0 : normSq (0 : RationalRing q) = 0 := (normSq_eq_zero_iff _).mpr rfl
    rw [h0] at hh
    exact le_antisymm hh hn
  obtain ⟨v, hv⟩ := LinearMap.surjective_of_injective hinj 1
  change u*v = 1 at hv
  exact ⟨⟨u,v,hv,by simpa only [mul_comm] using hv⟩,rfl⟩

section U
variable [Fact q.Prime]

/-- Paper eq. checker-U. -/
def U (p : RationalRing q) : RationalRing q :=
  1 + (1/(q : ℚ)) • (thetaQ*p)

private theorem skew_product (hq : q % 4 = 3) (p : RationalRing q)
    (hp : conjugate p = p) : conjugate (thetaQ*p) = -(thetaQ*p) := by
  rw [conjugate_mul, conjugate_thetaQ hq, hp, _root_.neg_mul]

theorem thetaQ_norm_mul (hq : q % 4 = 3) (z : RationalRing q) :
    normSq (thetaQ*z) = (q : ℚ)*normSq z := by
  rw [← inner_self, inner_adjoint]
  have he : conjugate (thetaQ (q := q))*(thetaQ*z) = (q : ℚ) • z := by
    rw [conjugate_thetaQ hq]
    calc
      -thetaQ*(thetaQ*z) = -(thetaQ^2)*z := by ring
      _ = (q : ℚ) • z := by rw [thetaQ_sq hq, Algebra.smul_def]; simp only [map_natCast, neg_neg]
  rw [he, inner_smul_right, inner_self]

theorem U_norm_exact (hq : q % 4 = 3) (p : RationalRing q)
    (hp : conjugate p = p) (y : RationalRing q) :
    normSq (U p*y) = normSq y + (1/(q : ℚ))*normSq (p*y) := by
  have hc : inner y (thetaQ*p*y) = 0 := by
    have he := inner_adjoint (thetaQ*p) y y
    rw [skew_product hq p hp, _root_.neg_mul, inner_neg_right,
      inner_symm (thetaQ*p*y) y] at he
    linarith
  rw [U, add_mul, one_mul, smul_mul_assoc, normSq_add,
    inner_smul_right, hc, normSq_smul]
  rw [mul_assoc, thetaQ_norm_mul hq]
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  field_simp <;> ring

theorem U_mul_conjugate (hq : q % 4 = 3) (p : RationalRing q)
    (hp : conjugate p = p) :
    U p*conjugate (U p) = 1+(1/(q : ℚ)) • (p^2) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hs : ((1/(q : ℚ)) • (thetaQ*p))^2 =
      -(1/(q : ℚ)) • (p^2) := by
    rw [smul_pow, mul_pow, thetaQ_sq hq]
    rw [show -(q : RationalRing q)*p^2 = (-(q : ℚ)) • (p^2) by
      rw [Algebra.smul_def]; simp only [map_neg, map_natCast]]
    rw [smul_smul]
    congr 1
    field_simp <;> ring
  rw [U, conjugate_add, conjugate_one, conjugate_smul, skew_product hq p hp,
    smul_neg]
  calc
    (1+(1/(q : ℚ)) • (thetaQ*p))*(1+ -((1/(q : ℚ)) • (thetaQ*p))) =
        1-((1/(q : ℚ)) • (thetaQ*p))^2 := by ring
    _ = _ := by rw [hs, neg_smul]; ring

theorem U_norm_expanding (hq : q % 4 = 3) (p : RationalRing q)
    (hp : conjugate p = p) (y : RationalRing q) :
    normSq y ≤ normSq (U p*y) := by
  rw [U_norm_exact hq p hp]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (normSq_nonneg _))

theorem U_isUnit (hq : q % 4 = 3) (p : RationalRing q)
    (hp : conjugate p = p) : IsUnit (U p) :=
  isUnit_of_norm_expanding (U p) (U_norm_expanding hq p hp)

/-- A chosen inverse, justified by finite-dimensional injectivity. -/
def inverseU (hq : q % 4 = 3) (p : RationalRing q) (hp : conjugate p = p) :
    RationalRing q := ↑((U_isUnit hq p hp).unit⁻¹)

@[simp] theorem U_mul_inverseU (hq : q % 4 = 3) (p : RationalRing q)
    (hp : conjugate p = p) : U p*inverseU hq p hp = 1 := by
  exact (U_isUnit hq p hp).mul_val_inv

/-- Eq. checker-V, using a proved inverse rather than an assumed field. -/
def V (hq : q % 4 = 3) (p : RationalRing q) (hp : conjugate p = p)
    (D : RationalRing q) : RationalRing q :=
  -(1/(q : ℚ)) • (conjugate (inverseU hq p hp)*D)

theorem conjugateU_mul_V (hq : q % 4 = 3) (p : RationalRing q)
    (hp : conjugate p = p) (D : RationalRing q) :
    conjugate (U p)*V hq p hp D = -(1/(q : ℚ)) • D := by
  rw [V, mul_smul_comm, ← mul_assoc, ← conjugate_mul, U_mul_inverseU,
    conjugate_one, one_mul]

/-- The inverse construction satisfies the denominator equation in the paper. -/
theorem V_denominator (hq : q % 4 = 3) (p : RationalRing q)
    (hp : conjugate p = p) (D : RationalRing q) :
    ((q : RationalRing q)-thetaQ*p)*V hq p hp D = -D := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hd : ((q : ℚ) • conjugate (U p)) = (q : RationalRing q)-thetaQ*p := by
    rw [U, conjugate_add, conjugate_one, conjugate_smul, skew_product hq p hp,
      smul_add, smul_smul]
    rw [show (q : ℚ)*(1/(q : ℚ)) = 1 by field_simp, one_smul]
    rw [Algebra.smul_def]
    simp only [map_natCast, mul_one]
    ring
  rw [← hd, smul_mul_assoc, conjugateU_mul_V, smul_smul,
    show (q : ℚ)*(-(1/(q : ℚ))) = -1 by field_simp]
  simp

theorem checker_value_norm (hq : q % 4 = 3) (p : RationalRing q)
    (hp : conjugate p = p) (D y : RationalRing q) :
    normSq (U p*y-V hq p hp D) = normSq y+(1/(q : ℚ))*normSq (p*y)+
      (2/(q : ℚ))*inner y D+normSq (V hq p hp D) := by
  rw [normSq_sub, U_norm_exact hq p hp, inner_adjoint,
    conjugateU_mul_V hq p hp, inner_smul_right]
  ring

theorem conjugateU_norm_expanding (hq : q % 4 = 3) (p : RationalRing q)
    (hp : conjugate p = p) (y : RationalRing q) :
    normSq y ≤ normSq (conjugate (U p)*y) := by
  calc
    normSq y = normSq (conjugate y) := (normSq_conjugate y).symm
    _ ≤ normSq (U p*conjugate y) := U_norm_expanding hq p hp _
    _ = normSq (conjugate (U p)*y) := by
      rw [← normSq_conjugate (U p*conjugate y), conjugate_mul, conjugate_conjugate]

theorem V_norm_bound (hq : q % 4 = 3) (p : RationalRing q)
    (hp : conjugate p = p) (D : RationalRing q) (W : ℚ)
    (hD : ∀ w : RationalRing q, normSq (D*w) ≤ W^2*normSq w)
    (w : RationalRing q) :
    normSq (V hq p hp D*w) ≤ (W/(q : ℚ))^2*normSq w := by
  have hh := conjugateU_norm_expanding hq p hp (V hq p hp D*w)
  rw [← mul_assoc, conjugateU_mul_V, smul_mul_assoc, normSq_smul] at hh
  have hb := mul_le_mul_of_nonneg_left (hD w) (sq_nonneg (-(1/(q : ℚ))))
  calc
    normSq (V hq p hp D*w) ≤ (-(1/(q : ℚ)))^2*normSq (D*w) := hh
    _ ≤ (-(1/(q : ℚ)))^2*(W^2*normSq w) := hb
    _ = _ := by ring


theorem U_ne_zero (hq : q % 4 = 3) (p : RationalRing q)
    (hp : conjugate p = p) : U p ≠ 0 := by
  intro hz
  have hh := U_norm_expanding hq p hp 1
  rw [hz, zero_mul, normSq_one] at hh
  have h0 : normSq (0 : RationalRing q) = 0 := (normSq_eq_zero_iff _).mpr rfl
  rw [h0] at hh
  have hq1 : (1 : ℚ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  linarith

end U

/-- A model-independent version of the paper's stability estimate. The two
premises are precisely the multiplier bounds proved for U and V. -/
theorem global_stability_exact (u v y w : RationalRing q) (Γ ν : ℚ)
    (hν : 0 < ν) (hν1 : ν < 1)
    (hu : normSq y ≤ normSq (u*y))
    (hv : normSq (v*w) ≤ ν^2*Γ^2*normSq w) :
    (1-ν)*(normSq y+Γ^2*normSq w) ≤
      normSq (u*y-v*w)+Γ^2*normSq w := by
  have hy := inner_young ν hν (u*y) (v*w)
  have hn := normSq_nonneg (v*w)
  have hb : ν⁻¹*normSq (v*w) ≤ ν*Γ^2*normSq w := by
    have hm := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hν.le)
    have hi : ν⁻¹*ν = 1 := inv_mul_cancel₀ (ne_of_gt hν)
    calc
      ν⁻¹*normSq (v*w) ≤ ν⁻¹*(ν^2*Γ^2*normSq w) := hm
      _ = ν*Γ^2*normSq w := by
        calc
          ν⁻¹*(ν^2*Γ^2*normSq w) = (ν⁻¹*ν)*ν*Γ^2*normSq w := by ring
          _ = _ := by rw [hi, one_mul]
  rw [normSq_sub]
  nlinarith [mul_nonneg (show 0 ≤ 1-ν by linarith) (sub_nonneg.mpr hu)]

private theorem real_young_of_sq_le (a b c r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 < r) (hc : c^2 ≤ a*b) : 2*c ≤ r*a+r⁻¹*b := by
  have hp : (r*a)*(r⁻¹*b) = a*b := by
    calc
      (r*a)*(r⁻¹*b) = (r*r⁻¹)*(a*b) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt hr), one_mul]
  have h₁ := mul_nonneg hr.le ha
  have h₂ := mul_nonneg (inv_nonneg.mpr hr.le) hb
  rw [← hp] at hc
  nlinarith [sq_nonneg (r*a-r⁻¹*b)]

/-- The real-parameter version allows every positive real Γ in the paper. -/
theorem global_stability_exact_real (u v y w : RationalRing q) (Γ ν : ℝ)
    (hν : 0 < ν) (hν1 : ν < 1)
    (hu : normSq y ≤ normSq (u*y))
    (hv : ((normSq (v*w) : ℚ) : ℝ) ≤ ν^2*Γ^2*((normSq w : ℚ) : ℝ)) :
    (1-ν)*(((normSq y : ℚ) : ℝ)+Γ^2*((normSq w : ℚ) : ℝ)) ≤
      ((normSq (u*y-v*w) : ℚ) : ℝ)+Γ^2*((normSq w : ℚ) : ℝ) := by
  have ha : (0 : ℝ) ≤ ((normSq (u*y) : ℚ) : ℝ) := by exact_mod_cast normSq_nonneg (u*y)
  have hb : (0 : ℝ) ≤ ((normSq (v*w) : ℚ) : ℝ) := by exact_mod_cast normSq_nonneg (v*w)
  have hc : ((inner (u*y) (v*w) : ℚ) : ℝ)^2 ≤
      ((normSq (u*y) : ℚ) : ℝ)*((normSq (v*w) : ℚ) : ℝ) := by
    exact_mod_cast inner_sq_le (u*y) (v*w)
  have hy := real_young_of_sq_le _ _ _ ν ha hb hν hc
  have hbound : ν⁻¹*((normSq (v*w) : ℚ) : ℝ) ≤ ν*Γ^2*((normSq w : ℚ) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hν.le)
    calc
      ν⁻¹*((normSq (v*w) : ℚ) : ℝ) ≤ ν⁻¹*(ν^2*Γ^2*((normSq w : ℚ) : ℝ)) := hm
      _ = ν*Γ^2*((normSq w : ℚ) : ℝ) := by
        calc
          _ = (ν⁻¹*ν)*ν*Γ^2*((normSq w : ℚ) : ℝ) := by ring
          _ = _ := by rw [inv_mul_cancel₀ (ne_of_gt hν), one_mul]
  have hu' : ((normSq y : ℚ) : ℝ) ≤ ((normSq (u*y) : ℚ) : ℝ) := by exact_mod_cast hu
  have he := congrArg (fun a : ℚ => (a : ℝ)) (normSq_sub (u*y) (v*w))
  push_cast at he
  rw [he]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1-ν by linarith) (sub_nonneg.mpr hu')]


end RationalEstimates
end
end Rank2ModuleSVP.Checker
