import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Prime exponent separation (`lem:sidon-reciprocal`)

The algebraic obstruction is proved over the rationals and evaluated in the
complex numbers. The hypotheses are only reciprocity, the degree bound,
nonvanishing at one, and primality of `2L-T`.

Paper: `paper/power2svp.pdf`, Section 4 (Proposition 2 and Lemmas 5–6).
-/
namespace Power2ModuleSVP
namespace Sidon
noncomputable section
open Polynomial

/-- The monic modulus of the Boolean source. -/
def modulus (P : ℚ[X]) (L : ℕ) : ℚ[X] := X ^ L + P

/-- The explicit reciprocal, when `P` is reciprocal of degree at most `T`. -/
def reciprocalModulus (P : ℚ[X]) (T L : ℕ) : ℚ[X] :=
  1 + X ^ (L - T) * P

theorem modulus_natDegree {P : ℚ[X]} {T L : ℕ}
    (hP : P.natDegree ≤ T) (hTL : T < L) :
    (modulus P L).natDegree = L := by
  unfold modulus
  rw [natDegree_add_eq_left_of_natDegree_lt (by simpa using hP.trans_lt hTL)]
  simp

theorem modulus_ne_zero {P : ℚ[X]} {T L : ℕ}
    (hP : P.natDegree ≤ T) (hTL : T < L) : modulus P L ≠ 0 := by
  intro hz
  have := modulus_natDegree hP hTL
  rw [hz, natDegree_zero] at this
  omega

/-- This identifies the explicit expression with Mathlib's polynomial reversal. -/
theorem reverse_modulus {P : ℚ[X]} {T L : ℕ}
    (hP : P.natDegree ≤ T) (hTL : T < L) (hrec : P.reflect T = P) :
    (modulus P L).reverse = reciprocalModulus P T L := by
  have he : L - T + T = L := Nat.sub_add_cancel hTL.le
  have href : P.reflect L = X ^ (L - T) * P := by
    have h := reflect_mul (1 : ℚ[X]) P (F := L-T) (G := T) (by simp) hP
    simpa [he, reflect_one, hrec] using h
  rw [reverse, modulus_natDegree hP hTL]
  simp [modulus, reciprocalModulus, reflect_add, reflect_monomial,
    revAt_le le_rfl, href]

/-- A prime root of unity different from one cannot annihilate a nonzero
rational polynomial of degree less than `p-1`. -/
theorem prime_root_degree_obstruction {p : ℕ} (hp : p.Prime)
    {f : ℚ[X]} (hf : f ≠ 0) (hdeg : f.natDegree < p - 1)
    {a : ℂ} (ha : a ^ p = 1) (ha1 : a ≠ 1) : aeval a f ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have he := congrArg (fun q : ℚ[X] => aeval a q)
    (cyclotomic_prime_mul_X_sub_one ℚ p)
  simp only [map_mul, map_sub, map_pow, aeval_X, map_one] at he
  rw [ha, sub_self] at he
  have hc : aeval a (cyclotomic p ℚ) = 0 :=
    (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr ha1)
  intro hz
  have hdvd := ((cyclotomic.irreducible_rat hp.pos).dvd_iff_aeval_eq_zero hc).mp hz
  have hd := natDegree_le_of_dvd hdvd hf
  rw [natDegree_cyclotomic, Nat.totient_prime hp] at hd
  omega

/-- No common complex zero of the modulus and its explicit reciprocal. -/
theorem no_common_root {P : ℚ[X]} {T L p : ℕ}
    (hP : P.natDegree ≤ T) (hTL : T < L) (hp : p.Prime)
    (hexp : L - T + L = p) (hdeg : L < p - 1)
    (hone : aeval (1 : ℂ) (modulus P L) ≠ 0) (a : ℂ) :
    ¬ (aeval a (modulus P L) = 0 ∧
      aeval a (reciprocalModulus P T L) = 0) := by
  rintro ⟨hw, hs⟩
  have ha1 : a ≠ 1 := by
    intro he
    subst a
    exact hone hw
  have hw' : a ^ L + aeval a P = 0 := by simpa [modulus] using hw
  have hs' : 1 + a ^ (L - T) * aeval a P = 0 := by
    simpa [reciprocalModulus] using hs
  have hpow : a ^ p = 1 := by
    rw [← hexp, pow_add]
    linear_combination a ^ (L - T) * hw' - hs'
  exact prime_root_degree_obstruction hp (modulus_ne_zero hP hTL)
    (by rw [modulus_natDegree hP hTL]; exact hdeg) hpow ha1 hw

/-- The actual reciprocal-polynomial version of `lem:sidon-reciprocal`. -/
theorem no_common_root_reverse {P : ℚ[X]} {T L p : ℕ}
    (hP : P.natDegree ≤ T) (hTL : T < L) (hrec : P.reflect T = P)
    (hp : p.Prime) (hexp : L - T + L = p) (hdeg : L < p - 1)
    (hone : aeval (1 : ℂ) (modulus P L) ≠ 0) (a : ℂ) :
    ¬ (aeval a (modulus P L) = 0 ∧ aeval a (modulus P L).reverse = 0) := by
  rw [reverse_modulus hP hTL hrec]
  exact no_common_root hP hTL hp hexp hdeg hone a

/-- Rational coefficients commute with complex conjugation. -/
theorem aeval_conj_rat (f : ℚ[X]) (a : ℂ) :
    aeval (starRingEnd ℂ a) f = starRingEnd ℂ (aeval a f) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [map_add, hf, hg]
  | monomial n c => simp [aeval_monomial]

/-- In particular, the modulus has no zero on the unit circle. -/
theorem no_unit_circle_root {P : ℚ[X]} {T L p : ℕ}
    (hP : P.natDegree ≤ T) (hTL : T < L) (hrec : P.reflect T = P)
    (hp : p.Prime) (hexp : L - T + L = p) (hdeg : L < p - 1)
    (hone : aeval (1 : ℂ) (modulus P L) ≠ 0)
    (a : ℂ) (ha : ‖a‖ = 1) : aeval a (modulus P L) ≠ 0 := by
  intro hw
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hi : aeval a⁻¹ (modulus P L) = 0 := by
    rw [Complex.inv_eq_conj ha, aeval_conj_rat, hw, map_zero]
  let : Invertible a⁻¹ := invertibleOfNonzero (inv_ne_zero ha0)
  have hr : aeval a (modulus P L).reverse = 0 := by
    have h := (eval₂_reverse_eq_zero_iff (algebraMap ℚ ℂ) a⁻¹ (modulus P L)).mpr hi
    simpa [aeval_def] using h
  exact no_common_root_reverse hP hTL hrec hp hexp hdeg hone a ⟨hw, hr⟩

/-- Coprimality over the rationals; in particular no reciprocal irreducible
factor can divide the modulus. -/
theorem modulus_coprime_reverse {P : ℚ[X]} {T L p : ℕ}
    (hP : P.natDegree ≤ T) (hTL : T < L) (hrec : P.reflect T = P)
    (hp : p.Prime) (hexp : L - T + L = p) (hdeg : L < p - 1)
    (hone : aeval (1 : ℂ) (modulus P L) ≠ 0) :
    IsCoprime (modulus P L) (modulus P L).reverse := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ ℂ _ _).mpr
  intro a
  exact not_and_or.mp (no_common_root_reverse hP hTL hrec hp hexp hdeg hone a)

/-- A factor fixed by reversal is a unit. Applied to an irreducible factor,
this rules out reciprocal irreducible factors as in `lem:sidon-reciprocal`. -/
theorem reciprocal_factor_isUnit {P q : ℚ[X]} {T L p : ℕ}
    (hP : P.natDegree ≤ T) (hTL : T < L) (hrec : P.reflect T = P)
    (hp : p.Prime) (hexp : L - T + L = p) (hdeg : L < p - 1)
    (hone : aeval (1 : ℂ) (modulus P L) ≠ 0)
    (hq : q.reverse = q) (hdvd : q ∣ modulus P L) : IsUnit q := by
  have hr : q ∣ (modulus P L).reverse := by
    obtain ⟨g,hg⟩ := hdvd
    rw [hg,reverse_mul_of_domain,hq]
    exact dvd_mul_right _ _
  exact (modulus_coprime_reverse hP hTL hrec hp hexp hdeg hone).isUnit_of_dvd' hdvd hr

end

end Sidon
end Power2ModuleSVP
