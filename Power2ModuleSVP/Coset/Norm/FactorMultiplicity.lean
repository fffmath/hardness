module

public import Power2ModuleSVP.Coset.Norm.Separation
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Factor and root multiplicities for divided derivatives

These tools support the repeated-factor step of `lem:elementary-separation`.
The integer factor is made monic using its unit leading coefficient.  Gauss's
lemma and characteristic-zero separability then identify its exponent with
the multiplicity at every complex root.  Taylor coefficients give the Hasse
derivative statements without division by factorials.

Paper: `paper/power2svp.pdf`, Section 3.2 (Lemmas 2–4, algebraic norm separation).
-/

@[expose] public section

namespace Power2ModuleSVP

open Polynomial

noncomputable section

/-- Failure of divisibility is detected by a monic irreducible factor and
a power dividing `w` but not `e`. -/
theorem exists_monic_irreducible_power_gap {w e : ℤ[X]}
    (hw : w.Monic) (he : e ≠ 0) (hndvd : ¬w ∣ e) :
    ∃ (p : ℤ[X]) (j : ℕ), p.Monic ∧ Irreducible p ∧ p ∣ w ∧
      p ^ j ∣ e ∧ ¬p ^ (j + 1) ∣ e ∧ p ^ (j + 1) ∣ w := by
  classical
  have hgap : ∃ a : ℤ[X], Prime a ∧ multiplicity a e < multiplicity a w := by
    by_contra! h
    apply hndvd
    exact (UniqueFactorizationMonoid.dvd_iff_multiplicity_le hw.ne_zero he).mpr
      (fun a ha => h a ha)
  obtain ⟨a, ha, hlt⟩ := hgap
  have hfe := FiniteMultiplicity.of_prime_left ha he
  have hfw := FiniteMultiplicity.of_prime_left ha hw.ne_zero
  have haw : a ∣ w := by
    have h : a ^ 1 ∣ w := hfw.pow_dvd_iff_le_multiplicity.mpr (by omega)
    simpa using h
  have hu := hw.isUnit_leadingCoeff_of_dvd haw
  let p : ℤ[X] := C a.leadingCoeff * a
  have hp : p.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rcases Int.isUnit_iff.mp hu with h | h <;> simp [h]
  have hassoc : Associated a p :=
    associated_unit_mul_right a (C a.leadingCoeff) (isUnit_C.mpr hu)
  have hpw : p ∣ w := hassoc.dvd_iff_dvd_left.mp haw
  refine ⟨p, multiplicity a e, hp, hassoc.irreducible ha.irreducible, hpw, ?_, ?_, ?_⟩
  · exact hassoc.pow_pow.dvd_iff_dvd_left.mp (pow_multiplicity_dvd a e)
  · intro hd
    have := hassoc.pow_pow.dvd_iff_dvd_left.mpr hd
    exact (hfe.multiplicity_eq_iff.mp rfl).2 this
  · exact hassoc.pow_pow.dvd_iff_dvd_left.mp
      (hfw.pow_dvd_iff_le_multiplicity.mpr hlt)

/-- A divisor inherits the unit constant coefficient. -/
theorem hasUnitConstant_of_dvd {p w : ℤ[X]}
    (hw : HasUnitConstant w) (h : p ∣ w) : HasUnitConstant p := by
  apply Int.isUnit_iff.mp
  have hwunit : IsUnit (w.coeff 0) := Int.isUnit_iff.mpr hw
  obtain ⟨q, rfl⟩ := h
  rw [mul_coeff_zero] at hwunit
  exact isUnit_of_mul_isUnit_left hwunit

/-- Root multiplicity is the index of the first nonzero Hasse derivative. -/
theorem hasseDeriv_eval_at_rootMultiplicity {f : ℂ[X]} (hf : f ≠ 0) (z : ℂ) :
    (hasseDeriv (f.rootMultiplicity z) f).eval z ≠ 0 ∧
      ∀ k < f.rootMultiplicity z, (hasseDeriv k f).eval z = 0 := by
  have hm : f.rootMultiplicity z = (taylor z f).natTrailingDegree :=
    rootMultiplicity_eq_natTrailingDegree
  rw [hm]
  constructor
  · rw [← taylor_coeff]
    exact coeff_natTrailingDegree_ne_zero.mpr (fun h => hf ((taylor_eq_zero z f).mp h))
  · intro k hk
    rw [← taylor_coeff]
    exact coeff_eq_zero_of_lt_natTrailingDegree hk

/-- Root multiplicities of powers in the complex polynomial ring. -/
theorem complex_rootMultiplicity_pow {f : ℂ[X]} (hf : f ≠ 0) (z : ℂ) (n : ℕ) :
    (f ^ n).rootMultiplicity z = n * f.rootMultiplicity z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hf) hf), ih]
      simp [Nat.succ_mul]

/-- Evaluation is compatible with passing from integers through the rationals. -/
theorem rat_map_aeval_eq_complex_eval (f : ℤ[X]) (z : ℂ) :
    aeval z (f.map (algebraMap ℤ ℚ)) = (complexPolynomial f).eval z := by
  have hcomp : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ :=
    Subsingleton.elim _ _
  rw [← eval_map_algebraMap, map_map, hcomp]
  rfl

/-- An integer polynomial not divisible by a monic irreducible polynomial
cannot vanish at any of its complex roots. -/
theorem complex_eval_ne_zero_of_not_dvd {p q : ℤ[X]}
    (hp : p.Monic) (hirr : Irreducible p) (hndvd : ¬p ∣ q)
    {z : ℂ} (hz : (complexPolynomial p).IsRoot z) :
    (complexPolynomial q).eval z ≠ 0 := by
  have hirrQ : Irreducible (p.map (algebraMap ℤ ℚ)) :=
    (hp.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hirr
  have hpQroot : aeval z (p.map (algebraMap ℤ ℚ)) = 0 := by
    rw [rat_map_aeval_eq_complex_eval]
    exact hz
  intro hqroot
  have hqQroot : aeval z (q.map (algebraMap ℤ ℚ)) = 0 := by
    rwa [rat_map_aeval_eq_complex_eval]
  exact hndvd ((map_dvd_map (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ) hp).mp
    ((hirrQ.dvd_iff_aeval_eq_zero hpQroot).mp hqQroot))

/-- Every complex root of a monic irreducible integer polynomial is simple. -/
theorem rootMultiplicity_complex_irreducible {p : ℤ[X]}
    (hp : p.Monic) (hirr : Irreducible p)
    {z : ℂ} (hz : (complexPolynomial p).IsRoot z) :
    (complexPolynomial p).rootMultiplicity z = 1 := by
  have hirrQ : Irreducible (p.map (algebraMap ℤ ℚ)) :=
    (hp.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hirr
  have hsep : (complexPolynomial p).Separable := by
    have h := hirrQ.separable.map (f := algebraMap ℚ ℂ)
    have hcomp : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ :=
      Subsingleton.elim _ _
    simpa only [complexPolynomial, map_map, hcomp] using h
  exact le_antisymm (rootMultiplicity_le_one_of_separable hsep z)
    ((rootMultiplicity_pos (complexPolynomial_monic hp).ne_zero).mpr hz)

/-- The exponent of an irreducible integer factor is the same at every
complex root of that factor. -/
theorem rootMultiplicity_complex_eq_multiplicity {p f : ℤ[X]}
    (hp : p.Monic) (hirr : Irreducible p) (hf : f ≠ 0)
    {z : ℂ} (hz : (complexPolynomial p).IsRoot z) :
    (complexPolynomial f).rootMultiplicity z = multiplicity p f := by
  have hfin := FiniteMultiplicity.of_not_isUnit hirr.not_isUnit hf
  obtain ⟨q, hq, hndvd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hqeval := complex_eval_ne_zero_of_not_dvd hp hirr hndvd hz
  have hq0 : complexPolynomial q ≠ 0 := by
    intro h
    apply hqeval
    simp [h]
  have hfactor : complexPolynomial f =
      complexPolynomial p ^ multiplicity p f * complexPolynomial q := by
    conv_lhs => rw [hq]
    simp only [complexPolynomial, Polynomial.map_mul, Polynomial.map_pow]
  rw [hfactor, rootMultiplicity_mul
      (mul_ne_zero (pow_ne_zero _ (complexPolynomial_monic hp).ne_zero) hq0),
    complex_rootMultiplicity_pow (complexPolynomial_monic hp).ne_zero,
    rootMultiplicity_complex_irreducible hp hirr hz,
    rootMultiplicity_eq_zero hqeval, mul_one, add_zero]

end

end Power2ModuleSVP
