import Rank2ModuleSVP.PrimeCyclotomic
import IdealCVP.CertificateBound
import Rank2ModuleSVP.SparsePolynomial
import Mathlib.FieldTheory.Finite.Basic

/-! Lifted Reed--Solomon lattices and the fixed-sum binary shell. -/
namespace Rank2ModuleSVP
open scoped BigOperators
noncomputable section
variable {q : ℕ} [NeZero q]

/-- Power-sum parity checks, with integer coefficients reduced modulo q. -/
def syndrome (k : ℕ) (z : Coeff ℤ q) : Fin k → ZMod q :=
  fun j => ∑ a, (z a : ZMod q) * a ^ j.val

/-- The lifted Reed--Solomon lattice as an actual additive subgroup. -/
def liftedRS (k : ℕ) : AddSubgroup (Coeff ℤ q) where
  carrier := {z | syndrome k z = 0}
  zero_mem' := by ext j; simp [syndrome]
  add_mem' := by
    intro x y hx hy
    ext j
    have hxj := congrFun hx j
    have hyj := congrFun hy j
    simpa [syndrome, Int.cast_add, add_mul, Finset.sum_add_distrib] using congrArg₂ (·+·) hxj hyj
  neg_mem' := by
    intro x hx
    ext j
    have hxj := congrFun hx j
    simpa [syndrome, Int.cast_neg, neg_mul, Finset.sum_neg_distrib] using congrArg Neg.neg hxj

/-- The only cited lattice minimum bound allowed by the plan. It is an explicit
proposition supplied only as an explicit argument. -/
def BennettPeikertMinimum : Prop :=
  ∀ (q : ℕ) (hq : q.Prime),
    letI : NeZero q := ⟨hq.ne_zero⟩
    ∀ k : ℕ, 1 ≤ k → 2*k ≤ q → ∀ z ∈ liftedRS (q := q) k,
      z ≠ 0 → (2*k : ℤ) ≤ IdealCVP.sqNorm z

/-- The norm scaling used in cyclotomic descent on the zero-sum hyperplane. -/
theorem normSq_zero_sum (z : Coeff ℤ q) (hz : ∑ a, z a = 0) :
    normSq (classOf z) = (q : ℤ) * IdealCVP.sqNorm z := by
  rw [normSq_classOf, coeffNormSq_eq, hz]
  simp [IdealCVP.sqNorm]

/-- The cited minimum immediately transfers to zero-sum lattice representatives.
The identification of the image with `ramifiedIdeal k` is a separate theorem. -/
theorem liftedRS_norm_lower (hBP : BennettPeikertMinimum) (hq : q.Prime)
    (k : ℕ) (hk : 1 ≤ k) (hkq : 2*k ≤ q) (z : Coeff ℤ q)
    (hz : z ∈ liftedRS k) (hs : ∑ a, z a = 0) (hne : classOf z ≠ 0) :
    (2*k*q : ℤ) ≤ normSq (classOf z) := by
  rw [normSq_zero_sum z hs]
  have hn : z ≠ 0 := by intro hh; apply hne; rw [hh, classOf_zero]
  have hb := hBP q hq k hk hkq z hz hn
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℤ) q) (sub_nonneg.mpr hb)]

/-- Evaluation is injective on every hyperplane with fixed coefficient sum. -/
theorem classOf_injective_fixed_sum {x y : Coeff ℤ q}
    (hxy : classOf x = classOf y) (hs : ∑ a, x a = ∑ a, y a) : x = y := by
  obtain ⟨c, hc⟩ := (classOf_eq_iff x y).mp hxy
  have he : (q : ℤ)*c = 0 := by
    have he := congrArg (fun z : Coeff ℤ q => ∑ a, z a) (funext hc)
    simpa [Finset.sum_sub_distrib, hs, Finset.card_univ, ZMod.card] using he.symm
  have hc0 : c = 0 := (mul_eq_zero.mp he).resolve_left (by exact_mod_cast NeZero.ne q)
  funext a
  have := hc a
  simp only [hc0, sub_eq_zero] at this
  exact this


/-- Evaluation of coefficient vectors as an additive homomorphism. -/
def classOfAddHom : Coeff ℤ q →+ IntegerRing q where
  toFun := classOf
  map_zero' := classOf_zero
  map_add' := classOf_add

/-- The additive image of the lifted lattice under cyclotomic evaluation. -/
def reedSolomonImage (k : ℕ) : AddSubgroup (IntegerRing q) :=
  (liftedRS k).map classOfAddHom

section Prime
variable [Fact q.Prime]

theorem constant_mem_liftedRS (k : ℕ) (hk : k ≤ q-1) (c : ℤ) :
    (fun _ : ZMod q => c) ∈ liftedRS k := by
  ext j
  change (∑ a : ZMod q, (c : ZMod q)*a^j.val) = 0
  rw [← Finset.mul_sum]
  have hj : j.val < Fintype.card (ZMod q)-1 := by rw [ZMod.card]; omega
  rw [FiniteField.sum_pow_lt_card_sub_one (ZMod q) j.val hj, mul_zero]


omit [Fact q.Prime] in
/-- An integral vector has ℓ₁ norm at most its squared Euclidean norm. -/
theorem sum_abs_le_sqNorm (z : Coeff ℤ q) : (∑ a, |z a|) ≤ IdealCVP.sqNorm z := by
  exact Finset.sum_le_sum (fun a _ => IdealCVP.int_abs_le_sq (z a))

/-- First step of the elementary Newton-identity proof of Bennett--Peikert:
a hypothetical vector below 2k has integer sum zero, not merely sum zero mod q. -/
theorem short_liftedRS_sum_zero (k : ℕ) (hk : 1 ≤ k) (hkq : 2*k ≤ q)
    (z : Coeff ℤ q) (hz : z ∈ liftedRS k) (hshort : IdealCVP.sqNorm z < (2*k : ℤ)) :
    (∑ a, z a) = 0 := by
  have hmod : ((∑ a, z a : ℤ) : ZMod q) = 0 := by
    have hj := congrFun hz ⟨0, hk⟩
    simpa [syndrome, ← Int.cast_sum] using hj
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
  have habs : |∑ a, z a| < (q : ℤ) := by
    have hsum := Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := z)
    have hsq := sum_abs_le_sqNorm z
    have hkq' : (2*k : ℤ) ≤ q := by exact_mod_cast hkq
    omega
  by_contra hn
  have hle : (q : ℤ) ≤ |∑ a, z a| :=
    Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs (q : ℤ) (∑ a, z a)).mpr hdvd)
  omega

/-- Every image element has a zero-sum lattice representative. -/
theorem reedSolomonImage_zero_sum (k : ℕ) (hk : 1 ≤ k) (hkq : k ≤ q-1)
    (v : IntegerRing q) (hv : v ∈ reedSolomonImage k) :
    ∃ z : Coeff ℤ q, z ∈ liftedRS k ∧ (∑ a, z a) = 0 ∧ classOf z = v := by
  obtain ⟨x, hx, hclass⟩ := hv
  have hmod : ((∑ a, x a : ℤ) : ZMod q) = 0 := by
    have hj := congrFun hx ⟨0, hk⟩
    simpa [syndrome, ← Int.cast_sum] using hj
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
  let z : Coeff ℤ q := x - fun _ => c
  refine ⟨z, (liftedRS k).sub_mem hx (constant_mem_liftedRS k hkq c), ?_, ?_⟩
  · simp only [z, Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hc]
    simp [Finset.card_univ, ZMod.card]
  · rw [← hclass]
    apply (classOf_eq_iff _ _).mpr
    exact ⟨-c, fun a => by simp only [z, Pi.sub_apply]; ring⟩

/-- Coset-syndrome correspondence with a fixed base representative. The principal
ideal identification is not needed for this additive statement. -/
theorem coset_syndrome (k : ℕ) (hk : 1 ≤ k) (hkq : k ≤ q-1)
    (x : Coeff ℤ q) (v : IntegerRing q) :
    v - classOf x ∈ reedSolomonImage k ↔
      ∃! z : Coeff ℤ q, classOf z = v ∧ syndrome k z = syndrome k x ∧
        (∑ a, z a) = ∑ a, x a := by
  constructor
  · intro hv
    obtain ⟨y, hy, hys, hyv⟩ := reedSolomonImage_zero_sum k hk hkq _ hv
    refine ⟨x+y, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [classOf_add, hyv]
      abel
    · ext j
      have hyj := congrFun hy j
      simpa [syndrome, Int.cast_add, add_mul, Finset.sum_add_distrib] using
        congrArg (fun t => (syndrome k x) j + t) hyj
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hys, add_zero]
    · intro z hz
      apply classOf_injective_fixed_sum (hz.1.trans ?_) (hz.2.2.trans ?_)
      · rw [classOf_add, hyv]; abel
      · simp only [Pi.add_apply, Finset.sum_add_distrib, hys, add_zero]
  · rintro ⟨z, hz, _⟩
    refine ⟨z-x, ?_, ?_⟩
    · ext j
      have hj := congrFun hz.2.1 j
      simpa [syndrome, Int.cast_sub, sub_mul, Finset.sum_sub_distrib] using sub_eq_zero.mpr hj
    · change classOf (z-x) = v-classOf x
      rw [classOf_sub, hz.1]

end Prime

def IsBinary (z : Coeff ℤ q) : Prop := ∀ a, z a = 0 ∨ z a = 1

private theorem integer_binary_penalty (t : ℤ) : 0 ≤ t*(t-1) := by
  have : t ≤ 0 ∨ 1 ≤ t := by omega
  rcases this with h | h <;> nlinarith

/-- Binary representatives of sum h have norm h(q-h). -/
theorem binary_norm (z : Coeff ℤ q) (h : ℤ) (hs : ∑ a, z a = h) (hb : IsBinary z) :
    normSq (classOf z) = h*((q : ℤ)-h) := by
  have hsq : ∑ a, z a^2 = h := by
    calc
      (∑ a, z a^2) = ∑ a, z a := by
        apply Finset.sum_congr rfl
        intro a _
        rcases hb a with he | he <;> simp [he]
      _ = h := hs
  rw [normSq_classOf, coeffNormSq_eq, hs, hsq]
  ring

/-- The quantitative part of paper `binary-shell`, for any integral representative
with the prescribed sum. -/
theorem binary_shell (z : Coeff ℤ q) (h : ℤ) (hs : ∑ a, z a = h) (hb : ¬ IsBinary z) :
    h*((q : ℤ)-h) + 2*q ≤ normSq (classOf z) := by
  classical
  have hex : ∃ a, z a ≠ 0 ∧ z a ≠ 1 := by simpa [IsBinary] using hb
  obtain ⟨a, ha0, ha1⟩ := hex
  have ha : 2 ≤ z a*(z a-1) := by
    have : z a ≤ -1 ∨ 2 ≤ z a := by omega
    rcases this with hh | hh <;> nlinarith
  have hsum : 2 ≤ ∑ b, z b*(z b-1) :=
    ha.trans (Finset.single_le_sum (fun b _ => integer_binary_penalty (z b)) (Finset.mem_univ a))
  have he : (∑ b, z b*(z b-1)) = (∑ b, z b^2)-h := by
    simp_rw [mul_sub, mul_one, ← pow_two]
    rw [Finset.sum_sub_distrib, hs]
  rw [he] at hsum
  rw [normSq_classOf, coeffNormSq_eq, hs]
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℤ) q) (sub_nonneg.mpr hsum)]

end
end Rank2ModuleSVP
