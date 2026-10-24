import IdealCVP.Lattice
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Data.ZMod.Basic

/-! Prime cyclotomic coefficients. The cyclic group algebra is quotiented by the
all-ones element. All coefficient identities are also available over ℚ. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Rank2ModuleSVP
open scoped BigOperators
noncomputable section

variable {q : ℕ} [NeZero q]

abbrev Coeff (R : Type*) (q : ℕ) := ZMod q → R
abbrev Cyclic (R : Type*) [CommRing R] (q : ℕ) := AddMonoidAlgebra R (ZMod q)

variable {R : Type*} [CommRing R]

def ofCoeff (x : Coeff R q) : Cyclic R q :=
  .ofCoeff (Finsupp.equivFunOnFinite.symm x)

@[simp] theorem coeff_ofCoeff (x : Coeff R q) (a : ZMod q) :
    (ofCoeff x).coeff a = x a := rfl

@[simp] theorem ofCoeff_coeff (x : Cyclic R q) : ofCoeff (fun a => x.coeff a) = x := by
  apply AddMonoidAlgebra.coeff_injective
  ext a
  rfl

@[simp] theorem ofCoeff_sub (x y : Coeff R q) : ofCoeff (x-y) = ofCoeff x - ofCoeff y := by
  ext a
  rfl

@[simp] theorem ofCoeff_add (x y : Coeff R q) : ofCoeff (x+y) = ofCoeff x + ofCoeff y := by
  ext a
  rfl

@[simp] theorem ofCoeff_zero : ofCoeff (0 : Coeff R q) = 0 := by ext; rfl

def allOnes : Cyclic R q := ofCoeff (fun _ => 1)
def cyclotomicIdeal : Ideal (Cyclic R q) := Ideal.span {allOnes}
abbrev Cyclotomic (R : Type*) [CommRing R] (q : ℕ) [NeZero q] :=
  Cyclic R q ⧸ (cyclotomicIdeal : Ideal (Cyclic R q))
abbrev IntegerRing (q : ℕ) [NeZero q] := Cyclotomic ℤ q
abbrev RationalRing (q : ℕ) [NeZero q] := Cyclotomic ℚ q

def classOf (x : Coeff R q) : Cyclotomic R q := Ideal.Quotient.mk _ (ofCoeff x)

theorem convolution (x y : Coeff R q) (a : ZMod q) :
    (ofCoeff x * ofCoeff y).coeff a = ∑ b, x b * y (a-b) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  · simp [sub_eq_add_neg, add_comm]
  · intro; simp

theorem mul_allOnes (x : Cyclic R q) :
    x * allOnes = ofCoeff (fun _ => ∑ a, x.coeff a) := by
  ext a
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  · simp [allOnes]
  · intro; simp

theorem mem_cyclotomicIdeal_iff (x : Cyclic R q) :
    x ∈ cyclotomicIdeal ↔ ∃ c : R, ∀ a, x.coeff a = c := by
  rw [cyclotomicIdeal, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨∑ a, y.coeff a, fun a => by rw [mul_allOnes]; rfl⟩
  · rintro ⟨c, hc⟩
    refine ⟨AddMonoidAlgebra.single 0 c, ?_⟩
    rw [mul_allOnes]
    ext a
    simpa using (hc a).symm

/-- Equality is exactly difference by a constant coefficient vector. -/
theorem classOf_eq_iff (x y : Coeff R q) :
    classOf x = classOf y ↔ ∃ c : R, ∀ a, x a - y a = c := by
  rw [classOf, classOf, Ideal.Quotient.eq, mem_cyclotomicIdeal_iff]
  rfl

@[simp] theorem classOf_zero : classOf (0 : Coeff R q) = 0 := by
  simp [classOf]

@[simp] theorem classOf_sub (x y : Coeff R q) :
    classOf (x-y) = classOf x - classOf y := by simp [classOf]

@[simp] theorem classOf_add (x y : Coeff R q) :
    classOf (x+y) = classOf x + classOf y := by simp [classOf]

theorem classOf_add_constant (x : Coeff R q) (c : R) :
    classOf (fun a => x a + c) = classOf x := by
  apply (classOf_eq_iff _ _).mpr
  exact ⟨c, fun _ => by ring⟩


@[simp] theorem classOf_neg (x : Coeff R q) : classOf (-x) = -classOf x := by
  simpa only [zero_sub, classOf_zero] using classOf_sub (0 : Coeff R q) x

theorem classOf_mul (x y : Coeff R q) :
    classOf x * classOf y = classOf (fun a => ∑ b, x b * y (a-b)) := by
  unfold classOf
  rw [← map_mul]
  congr 1
  ext a
  exact convolution x y a

theorem classOf_single_zero (c : ℤ) :
    classOf (fun a : ZMod q => if a = 0 then c else 0) = (c : IntegerRing q) := by
  calc
    classOf (fun a : ZMod q => if a = 0 then c else 0) =
        Ideal.Quotient.mk _ (c : Cyclic ℤ q) := by
      unfold classOf
      congr 1
      ext a
      simp only [AddMonoidAlgebra.intCast_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply, coeff_ofCoeff, Int.cast_id]
      split_ifs <;> simp_all
    _ = (c : IntegerRing q) := map_intCast _ c

/-- The integral trace form (and its rational extension). -/
def canonicalForm (x y : Coeff R q) : R :=
  (q : R) * ∑ a, x a * y a - (∑ a, x a) * (∑ a, y a)
def coeffNormSq (x : Coeff R q) : R := canonicalForm x x

theorem canonicalForm_symm (x y : Coeff R q) : canonicalForm x y = canonicalForm y x := by
  simp [canonicalForm, mul_comm]

theorem canonicalForm_add_constant_left (x y : Coeff R q) (c : R) :
    canonicalForm (fun a => x a + c) y = canonicalForm x y := by
  simp only [canonicalForm, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
  ring

theorem canonicalForm_add_constant_right (x y : Coeff R q) (c : R) :
    canonicalForm x (fun a => y a + c) = canonicalForm x y := by
  rw [canonicalForm_symm, canonicalForm_add_constant_left, canonicalForm_symm]

theorem coeffNormSq_add_constant (x : Coeff R q) (c : R) :
    coeffNormSq (fun a => x a + c) = coeffNormSq x := by
  unfold coeffNormSq
  rw [canonicalForm_add_constant_left, canonicalForm_add_constant_right]

theorem coeffNormSq_eq (x : Coeff R q) :
    coeffNormSq x = (q : R) * ∑ a, x a ^ 2 - (∑ a, x a)^2 := by
  simp [coeffNormSq, canonicalForm, pow_two]

/-- Twice the norm is the sum over all ordered pairs. -/
theorem two_mul_coeffNormSq (x : Coeff R q) :
    2 * coeffNormSq x = ∑ a, ∑ b, (x a - x b)^2 := by
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [coeffNormSq_eq]
  ring

/-- The sum over `a.val < b.val` counts each unordered pair once. -/
theorem coeffNormSq_pairs (x : Coeff R q) [IsDomain R] [CharZero R] :
    coeffNormSq x = ∑ a, ∑ b with a.val < b.val, (x a - x b)^2 := by
  have split (a b : ZMod q) : (x a-x b)^2 =
      (if a.val < b.val then (x a-x b)^2 else 0) +
      (if b.val < a.val then (x b-x a)^2 else 0) := by
    rcases lt_trichotomy a.val b.val with h | h | h
    · simp [h, Nat.not_lt.mpr h.le]
    · have hab : a = b := ZMod.val_injective q h
      simp [hab]
    · simp [h, Nat.not_lt.mpr h.le, sub_sq]; ring
  have hs : (∑ a, ∑ b, (x a-x b)^2) =
      2 * (∑ a, ∑ b with a.val < b.val, (x a-x b)^2) := by
    conv_lhs => arg 2; ext a; arg 2; ext b; rw [split a b]
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun a b => if b.val < a.val then (x b-x a)^2 else 0)]
    simp only [Finset.sum_filter]
    ring
  have := (two_mul_coeffNormSq x).trans hs
  exact mul_left_cancel₀ (show (2 : R) ≠ 0 by norm_num) this


theorem coeffNormSq_of_classOf_eq {x y : Coeff R q} (h : classOf x = classOf y) :
    coeffNormSq x = coeffNormSq y := by
  obtain ⟨c, hc⟩ := (classOf_eq_iff x y).mp h
  have he : x = fun a => y a + c := by funext a; have := hc a; linear_combination this
  rw [he, coeffNormSq_add_constant]

/-- Squared canonical norm on the quotient, independent of representatives. -/
def normSq (v : Cyclotomic R q) : R :=
  coeffNormSq (fun a => (Ideal.Quotient.mk_surjective v).choose.coeff a)

@[simp] theorem normSq_classOf (x : Coeff R q) : normSq (classOf x) = coeffNormSq x := by
  apply coeffNormSq_of_classOf_eq
  simp only [classOf, ofCoeff_coeff]
  exact (Ideal.Quotient.mk_surjective (classOf x)).choose_spec

theorem classOf_surjective : Function.Surjective (classOf : Coeff R q → Cyclotomic R q) := by
  intro v
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective v
  exact ⟨fun a => x.coeff a, by simp [classOf]⟩

section Ordered
variable [LinearOrder R] [IsStrictOrderedRing R]

theorem coeffNormSq_nonneg (x : Coeff R q) : 0 ≤ coeffNormSq x := by
  have := Finset.sum_nonneg (s := Finset.univ) (fun a _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun b _ => sq_nonneg (x a-x b)))
  rw [← two_mul_coeffNormSq] at this
  nlinarith

theorem coeffNormSq_eq_zero_iff (x : Coeff R q) :
    coeffNormSq x = 0 ↔ ∃ c, ∀ a, x a = c := by
  constructor
  · intro hx
    have hz : ∀ a b, (x a-x b)^2 = 0 := by
      have hh : (∑ a, ∑ b, (x a-x b)^2) = 0 := by rw [← two_mul_coeffNormSq, hx, mul_zero]
      have hsum := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
        Finset.sum_nonneg (fun b _ => sq_nonneg (x a-x b)))).mp hh
      intro a b
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg (x a-x b))).mp
        (hsum a (Finset.mem_univ a)) b (Finset.mem_univ b)
    exact ⟨x 0, fun a => sub_eq_zero.mp (sq_eq_zero_iff.mp (hz a 0))⟩
  · rintro ⟨c, hc⟩
    have he : x = fun _ => c := funext hc
    rw [he, coeffNormSq_eq]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    ring

theorem normSq_nonneg (v : Cyclotomic R q) : 0 ≤ normSq v := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  rw [normSq_classOf]
  exact coeffNormSq_nonneg x

@[simp] theorem normSq_eq_zero_iff (v : Cyclotomic R q) : normSq v = 0 ↔ v = 0 := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  rw [normSq_classOf, coeffNormSq_eq_zero_iff, ← classOf_zero, classOf_eq_iff]
  simp

end Ordered

/-- Negation of exponents is complex conjugation in coefficient coordinates. -/
def conjugateCoeff (x : Coeff R q) : Coeff R q := fun a => x (-a)
def shiftCoeff (j : ZMod q) (x : Coeff R q) : Coeff R q := fun a => x (a-j)

theorem coeffNormSq_equiv (x : Coeff R q) (e : Equiv.Perm (ZMod q)) :
    coeffNormSq (fun a => x (e a)) = coeffNormSq x := by
  simp only [coeffNormSq_eq]
  rw [Equiv.sum_comp e (fun a => x a ^ 2), Equiv.sum_comp e x]

theorem coeffNormSq_conjugate (x : Coeff R q) :
    coeffNormSq (conjugateCoeff x) = coeffNormSq x :=
  coeffNormSq_equiv x (Equiv.neg _)

theorem coeffNormSq_shift (j : ZMod q) (x : Coeff R q) :
    coeffNormSq (shiftCoeff j x) = coeffNormSq x :=
  coeffNormSq_equiv x (Equiv.subRight j)

@[simp] theorem coeffNormSq_neg (x : Coeff R q) : coeffNormSq (-x) = coeffNormSq x := by
  simp [coeffNormSq_eq, Finset.sum_neg_distrib]

/-- The monomial ζ^j in the cyclotomic model. -/
def monomial (j : ZMod q) : Cyclotomic R q :=
  Ideal.Quotient.mk _ (AddMonoidAlgebra.single j 1)

theorem monomial_mul_classOf (j : ZMod q) (x : Coeff R q) :
    monomial j * classOf x = classOf (shiftCoeff j x) := by
  change Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ _ = _
  rw [← map_mul]
  congr 1
  ext a
  simp [shiftCoeff, sub_eq_add_neg, add_comm]

theorem normSq_monomial_mul (j : ZMod q) (v : Cyclotomic R q) :
    normSq (monomial j * v) = normSq v := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  rw [monomial_mul_classOf, normSq_classOf, normSq_classOf, coeffNormSq_shift]

@[simp] theorem normSq_neg (v : Cyclotomic R q) : normSq (-v) = normSq v := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  have he : -classOf x = classOf (-x) := by
    rw [classOf, classOf, ← map_neg]
    congr 1
    ext a
    rfl
  rw [he, normSq_classOf, normSq_classOf, coeffNormSq_neg]

theorem normSq_neg_monomial_mul (j : ZMod q) (v : Cyclotomic R q) :
    normSq ((-(monomial j : Cyclotomic R q)) * v) = normSq v := by
  calc
    normSq ((-(monomial j : Cyclotomic R q)) * v) = normSq (-(monomial j * v)) :=
      congrArg normSq (_root_.neg_mul (monomial j) v)
    _ = normSq (monomial j * v) := normSq_neg _
    _ = normSq v := normSq_monomial_mul j v


/-- Conjugation on classes, defined using any coefficient representative. -/
def conjugate (v : Cyclotomic R q) : Cyclotomic R q :=
  classOf (conjugateCoeff (fun a => (Ideal.Quotient.mk_surjective v).choose.coeff a))

@[simp] theorem conjugate_classOf (x : Coeff R q) :
    conjugate (classOf x) = classOf (conjugateCoeff x) := by
  have he : classOf (fun a => (Ideal.Quotient.mk_surjective (classOf x)).choose.coeff a) =
      classOf x := by
    simp only [classOf, ofCoeff_coeff]
    exact (Ideal.Quotient.mk_surjective (classOf x)).choose_spec
  obtain ⟨c, hc⟩ := (classOf_eq_iff _ _).mp he
  apply (classOf_eq_iff _ _).mpr
  exact ⟨c, fun a => hc (-a)⟩

@[simp] theorem conjugate_conjugate (v : Cyclotomic R q) : conjugate (conjugate v) = v := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  rw [conjugate_classOf, conjugate_classOf]
  congr 1
  funext a
  simp only [conjugateCoeff, neg_neg]

theorem normSq_conjugate (v : Cyclotomic R q) : normSq (conjugate v) = normSq v := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  rw [conjugate_classOf, normSq_classOf, normSq_classOf, coeffNormSq_conjugate]

/-- A pair carries the product canonical norm. -/
def pairNormSq (v : Cyclotomic R q × Cyclotomic R q) : R := normSq v.1 + normSq v.2

def pi : Cyclotomic R q := 1 - monomial 1

def ramifiedIdeal (k : ℕ) : Ideal (Cyclotomic R q) := Ideal.span {(pi : Cyclotomic R q) ^ k}

end
end Rank2ModuleSVP
