import Hardness.Main
import Mathlib.RingTheory.AdjoinRoot

/-! # The genuine negacyclic quotient ring

The coefficient model is additively equivalent to ℤ[X]/(X^d+1), and its
explicit convolution agrees with quotient multiplication.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Hardness.Cyclotomic
open Polynomial

/-- The defining negacyclic polynomial. -/
def modulus (d : ℕ) : Polynomial ℤ := X ^ d + 1

/-- The actual quotient ring, with Mathlib's quotient ring operations. -/
abbrev QuotRing (d : ℕ) := AdjoinRoot (modulus d)

/-- Send coefficients to their degree-<d polynomial class. -/
def toQuot {d : ℕ} (f : R d) : QuotRing d :=
  ∑ i : Fin d, f i • (AdjoinRoot.root (modulus d)) ^ i.val

/-- This is literally the class of the polynomial with the given coefficients. -/
theorem toQuot_eq_mk {d : ℕ} (f : R d) :
    toQuot f = Ideal.Quotient.mk (Ideal.span {modulus d})
      (∑ i : Fin d, Polynomial.C (f i) * X ^ i.val) := by
  change toQuot f = AdjoinRoot.mk (modulus d) _
  simp [toQuot, ← AdjoinRoot.mk_X]

theorem modulus_monic {d : ℕ} (hd : 0 < d) : (modulus d).Monic := by
  simpa [modulus] using (Polynomial.monic_X_pow_add_C (1 : ℤ) (by omega : d ≠ 0))

@[simp] theorem modulus_natDegree (d : ℕ) : (modulus d).natDegree = d := by
  simpa [modulus] using (Polynomial.natDegree_X_pow_add_C (n := d) (r := (1 : ℤ)))

/-- The standard monomial basis, indexed by `Fin d`. -/
noncomputable def coefficientBasis {d : ℕ} (hd : 0 < d) :
    Module.Basis (Fin d) ℤ (QuotRing d) :=
  (AdjoinRoot.powerBasis' (modulus_monic hd)).basis.reindex
    (finCongr (modulus_natDegree d))

@[simp] theorem coefficientBasis_apply {d : ℕ} (hd : 0 < d) (i : Fin d) :
    coefficientBasis hd i = AdjoinRoot.root (modulus d) ^ i.val := by
  rw [coefficientBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- The coefficient embedding is an additive (indeed ℤ-linear) bijection. -/
noncomputable def quotEquiv {d : ℕ} (hd : 0 < d) : R d ≃ₗ[ℤ] QuotRing d :=
  (coefficientBasis hd).equivFun.symm

@[simp] theorem quotEquiv_apply {d : ℕ} (hd : 0 < d) (f : R d) :
    quotEquiv hd f = toQuot f := by
  simp [quotEquiv, Module.Basis.equivFun_symm_apply, toQuot]

theorem toQuot_bijective {d : ℕ} (hd : 0 < d) : Function.Bijective (@toQuot d) := by
  have he : (fun f : R d => quotEquiv hd f) = toQuot := funext (quotEquiv_apply hd)
  rw [← he]
  exact (quotEquiv hd).bijective

@[simp] theorem toQuot_zero (d : ℕ) : toQuot (0 : R d) = 0 := by simp [toQuot]

@[simp] theorem toQuot_add {d : ℕ} (f g : R d) :
    toQuot (f + g) = toQuot f + toQuot g := by
  simp [toQuot, add_smul, Finset.sum_add_distrib]

@[simp] theorem root_pow_dimension (d : ℕ) :
    AdjoinRoot.root (modulus d) ^ d = -1 := by
  have h := AdjoinRoot.mk_self (f := modulus d)
  change AdjoinRoot.mk (modulus d) (X ^ d + 1) = 0 at h
  simpa only [map_add, map_pow, AdjoinRoot.mk_X, map_one, add_eq_zero_iff_eq_neg] using h

/-- Folding a product of two basis powers gives exactly the convolution sign. -/
theorem root_pow_fold {d : ℕ} (_hd : 0 < d) (i j : Fin d) :
    AdjoinRoot.root (modulus d) ^ (i.val + j.val) =
      (if i.val + j.val < d then (1 : ℤ) else -1) •
        AdjoinRoot.root (modulus d) ^ ((i.val + j.val) % d) := by
  by_cases h : i.val + j.val < d
  · simp [h, Nat.mod_eq_of_lt h]
  · have he : i.val + j.val = d + ((i.val + j.val) % d) := by
      have hb : i.val + j.val < d + d := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [he, pow_add, root_pow_dimension]
    simp [show ¬ d + (i.val + j.val) % d < d by omega]

/-- Negacyclic convolution is multiplication in the genuine quotient ring. -/
theorem toQuot_mul {d : ℕ} (hd : 0 < d) (f g : R d) :
    toQuot (mul f g) = toQuot f * toQuot g := by
  let x := AdjoinRoot.root (modulus d)
  have step (i j : Fin d) :
      (∑ r : Fin d, (if (i.val + j.val) % d = r.val then
        (if i.val + j.val < d then (1 : ℤ) else -1) * f i * g j else 0) • x ^ r.val) =
      (f i * g j) • x ^ (i.val + j.val) := by
    let r₀ : Fin d := ⟨(i.val + j.val) % d, Nat.mod_lt _ hd⟩
    rw [Finset.sum_eq_single r₀]
    · simp only [r₀, ite_true]
      rw [show x ^ (i.val + j.val) = _ from root_pow_fold hd i j, smul_smul]
      congr 1
      ring
    · intro r _ hr
      have hne : (i.val + j.val) % d ≠ r.val := by
        intro he
        apply hr
        exact Fin.ext he.symm
      simp [hne]
    · simp
  calc
    toQuot (mul f g) = ∑ i : Fin d, ∑ j : Fin d, ∑ r : Fin d,
        (if (i.val + j.val) % d = r.val then
          (if i.val + j.val < d then (1 : ℤ) else -1) * f i * g j else 0) • x ^ r.val := by
      simp only [toQuot, mul, Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin d, ∑ j : Fin d, (f i * g j) • x ^ (i.val + j.val) := by
      simp_rw [step]
    _ = toQuot f * toQuot g := by
      simp only [toQuot]
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum, smul_mul_smul_comm, ← pow_add]
      rfl

/-- Polynomial representatives of the explicit product differ by a multiple
of the defining polynomial. This form is useful when mapping to other rings. -/
theorem polynomial_mul_difference_dvd {d : ℕ} (hd : 0 < d) (f g : R d) :
    modulus d ∣ (∑ i : Fin d, C (mul f g i) * X ^ i.val) -
      (∑ i : Fin d, C (f i) * X ^ i.val) * (∑ i : Fin d, C (g i) * X ^ i.val) := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  rw [map_sub, map_mul, ← toQuot_eq_mk, ← toQuot_eq_mk, ← toQuot_eq_mk,
    toQuot_mul hd, sub_self]

/-- Ideal membership in coefficients is precisely membership in the genuine
principal quotient-ring ideal. -/
theorem mem_principalIdealLattice_iff {d : ℕ} (hd : 0 < d) (g v : R d) :
    v ∈ principalIdealLattice g ↔ toQuot v ∈ Ideal.span {toQuot g} := by
  rw [mem_principalIdealLattice, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨toQuot q, toQuot_mul hd g q⟩
  · rintro ⟨q', hq'⟩
    obtain ⟨q, rfl⟩ := (toQuot_bijective hd).surjective q'
    exact ⟨q, (toQuot_bijective hd).injective ((toQuot_mul hd g q).trans hq'.symm)⟩

/-- Equality with the preimage of the principal ideal under the additive
coefficient equivalence. -/
theorem principalIdealLattice_eq_comap {d : ℕ} (hd : 0 < d) (g : R d) :
    principalIdealLattice g =
      (Ideal.span {toQuot g}).toAddSubgroup.comap (quotEquiv hd).toAddEquiv.toAddMonoidHom := by
  ext v
  change v ∈ principalIdealLattice g ↔ quotEquiv hd v ∈ Ideal.span {toQuot g}
  rw [quotEquiv_apply]
  exact mem_principalIdealLattice_iff hd g v

end Hardness.Cyclotomic

namespace Hardness
open Hardness.Cyclotomic

/-- Theorem `thm:cyclotomic-cvp` in the actual ring ℤ[X]/(X^d+1),
with the ordinary coefficient-vector distance. -/
theorem x3c_correct_quotient (I : X3CInstance) :
    I.HasExactCover ↔ ∃ v : R (x3cToCVP I).d,
      toQuot v ∈ Ideal.span {toQuot (x3cToCVP I).g} ∧
      sqNorm (v - (x3cToCVP I).T) ≤ (x3cToCVP I).Δ := by
  rw [x3c_correct]
  have hd : 0 < (x3cToCVP I).d := by
    obtain ⟨k, hk⟩ := (x3cToCVP I).power_two
    rw [hk]
    positivity
  simp only [CVPYes, mem_principalIdealLattice_iff hd]

end Hardness
