import IdealCVP.Quotient
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! # Full rank for every nonzero power-of-two cyclotomic generator -/
noncomputable section
namespace IdealCVP.Cyclotomic
open Polynomial

/-- Includes the case `k = 0`, where the polynomial is `X + 1`. -/
theorem pow_two_cyclotomic (k : ℕ) (A : Type*) [CommRing A] :
    (X : Polynomial A) ^ (2 ^ k) + 1 = cyclotomic (2 * 2 ^ k) A := by
  rw [show 2 * 2 ^ k = 2 ^ (k + 1) by omega,
    cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  simp [Finset.sum_range_succ, add_comm]

theorem modulus_irreducible {d : ℕ} (hd : ∃ k, d = 2 ^ k) :
    Irreducible (modulus d) := by
  obtain ⟨k, rfl⟩ := hd
  rw [modulus, pow_two_cyclotomic]
  exact cyclotomic.irreducible (by positivity)

theorem modulus_irreducible_rat {d : ℕ} (hd : ∃ k, d = 2 ^ k) :
    Irreducible ((X : Polynomial ℚ) ^ d + 1) := by
  obtain ⟨k, rfl⟩ := hd
  rw [pow_two_cyclotomic]
  exact cyclotomic.irreducible_rat (by positivity)

/-- The genuine integral quotient is a domain; no coefficient ring structure
is assumed. -/
theorem quotRing_isDomain {d : ℕ} (hd : ∃ k, d = 2 ^ k) : IsDomain (QuotRing d) :=
  AdjoinRoot.isDomain_of_prime (modulus_irreducible hd).prime

theorem power_two_pos {d : ℕ} (hd : ∃ k, d = 2 ^ k) : 0 < d := by
  obtain ⟨k, rfl⟩ := hd
  positivity

/-- Multiplication by any nonzero element is injective. -/
theorem mul_injective {d : ℕ} (hd : ∃ k, d = 2 ^ k) {g : R d} (hg : g ≠ 0) :
    Function.Injective (mul g) := by
  let := quotRing_isDomain hd
  have hp := power_two_pos hd
  have hinj := (toQuot_bijective hp).injective
  have hgz : toQuot g ≠ 0 := by
    intro h
    exact hg (hinj (h.trans (toQuot_zero d).symm))
  intro a b hab
  apply hinj
  apply mul_left_cancel₀ hgz
  simpa only [← toQuot_mul hp] using congrArg toQuot hab

noncomputable def principalMultiplicationEquiv {d : ℕ} (hd : ∃ k, d = 2 ^ k)
    (g : R d) (hg : g ≠ 0) : R d ≃+ principalIdealLattice g :=
  AddEquiv.ofBijective (mulHom g).rangeRestrict
    ⟨(fun _ _ h => mul_injective hd hg (congrArg Subtype.val h)),
      (mulHom g).rangeRestrict_surjective⟩

/-- The multiplication basis has exactly `d` columns for every nonzero `g`. -/
noncomputable def principalMultiplicationBasis {d : ℕ} (hd : ∃ k, d = 2 ^ k)
    (g : R d) (hg : g ≠ 0) : Module.Basis (Fin d) ℤ (principalIdealLattice g) :=
  (Pi.basisFun ℤ (Fin d)).map (principalMultiplicationEquiv hd g hg).toIntLinearEquiv

/-- Each column is the generator times the corresponding unit coefficient vector. -/
@[simp] theorem principalMultiplicationBasis_apply {d : ℕ} (hd : ∃ k, d = 2 ^ k)
    (g : R d) (hg : g ≠ 0) (j : Fin d) :
    (principalMultiplicationBasis hd g hg j).val = mul g (Cyclotomic.monomial j 1) := by
  simp only [principalMultiplicationBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change mul g (Pi.single j 1) = _
  congr 1
  funext i
  simp [Pi.single_apply, Cyclotomic.monomial, eq_comm]

/-- General full rank, with no supplied injectivity hypothesis. -/
theorem principal_full_rank {d : ℕ} (hd : ∃ k, d = 2 ^ k)
    (g : R d) (hg : g ≠ 0) :
    Nonempty (Module.Basis (Fin d) ℤ (principalIdealLattice g)) :=
  ⟨principalMultiplicationBasis hd g hg⟩

end IdealCVP.Cyclotomic
