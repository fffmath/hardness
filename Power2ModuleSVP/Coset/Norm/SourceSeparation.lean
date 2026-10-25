import Power2ModuleSVP.Coset.Norm.Mahler
import Power2ModuleSVP.Coset.Norm.Resultant
import Power2ModuleSVP.Coset.Norm.Divided
import Power2ModuleSVP.Source.Boolean.Reduction

/-!
# Unconditional bounded-remainder separation and its Boolean source instance

The three inputs to `lem:elementary-separation` are proved in the imported
norm files. This file assembles them and transfers the source's rational
reciprocal-root exclusion to its integer modulus. The finite exponent data
of `BooleanSource.threeSATEncode` determine that modulus directly.

Audit: the source has constant coefficient one and degree at least 64.
Neither a dyadic exponent nor squarefreeness is required for separation.
The remainder height bound is an explicit premise, as in the separation
export contract; decoded-remainder estimates belong to packing.

Paper: `paper/power2svp.pdf`, Section 3.2 (Lemmas 2–4, algebraic norm separation).
-/

namespace Power2ModuleSVP

open Polynomial
open scoped BigOperators

noncomputable section

/-- All three algebraic and analytic inputs to separation hold unconditionally. -/
theorem normSeparationHypothesis_holds : NormSeparationHypothesis where
  toElementaryMahlerHypothesis := elementaryMahlerHypothesis_holds
  toReciprocalResultantHypothesis := reciprocalResultantHypothesis_holds
  toDividedDerivativeWitnessHypothesis := dividedDerivativeWitnessHypothesis_holds

/-- Unconditional `lem:elementary-separation`, including repeated factors. -/
theorem elementary_separation_unconditional
    {w e : ℤ[X]} {L D : ℕ} (hw : w.Monic) (hdeg : w.natDegree = L)
    (hu : HasUnitConstant w) (hroot : NoCommonReciprocalRoot w)
    (hL : 64 ≤ L) (hD : 16 * L ^ 3 ≤ D)
    (he : e.degree < L) (hH : CoefficientBound e (L ^ 2))
    (hcong : SeparationCongruence w e D) : e = 0 :=
  elementary_separation normSeparationHypothesis_holds hw hdeg hu hroot hL hD he hH hcong

/-- Unconditional form accepting the lifted integer-polynomial identity. -/
theorem elementary_separation_of_eq_unconditional
    {w e : ℤ[X]} {L D : ℕ} (hw : w.Monic) (hdeg : w.natDegree = L)
    (hu : HasUnitConstant w) (hroot : NoCommonReciprocalRoot w)
    (hL : 64 ≤ L) (hD : 16 * L ^ 3 ≤ D)
    (he : e.degree < L) (hH : CoefficientBound e (L ^ 2))
    (q u : ℤ[X]) (hlift : e = (1 + X ^ D) * q + w * u) : e = 0 :=
  elementary_separation_of_eq normSeparationHypothesis_holds
    hw hdeg hu hroot hL hD he hH q u hlift

/-- The `natDegree` separation export requested by the reduction interface. -/
theorem bounded_remainder_separation (w e : ℤ[X]) (L D : ℕ)
    (hw : w.Monic) (hdeg : w.natDegree = L) (hL : 64 ≤ L)
    (hunit : HasUnitConstant w) (hrec : NoCommonReciprocalRoot w)
    (hD : 16 * L ^ 3 ≤ D) (hedeg : e.natDegree < L)
    (heheight : CoefficientBound e (L ^ 2))
    (hmem : SeparationCongruence w e D) : e = 0 := by
  apply elementary_separation_unconditional hw hdeg hunit hrec hL hD ?_ heheight hmem
  exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hedeg)

/-- Rational root exclusion transfers to the original integer polynomial. -/
theorem noCommonReciprocalRoot_of_rational {w : ℤ[X]}
    (h : ∀ z : ℂ, ¬ (aeval z (w.map (Int.castRingHom ℚ)) = 0 ∧
      aeval z (w.map (Int.castRingHom ℚ)).reverse = 0)) :
    NoCommonReciprocalRoot w := by
  have hreverse : (w.map (Int.castRingHom ℚ)).reverse =
      w.reverse.map (Int.castRingHom ℚ) := by
    simp only [reverse,
      natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective, reflect_map]
  have heval (p : ℤ[X]) (z : ℂ) :
      aeval z (p.map (Int.castRingHom ℚ)) = (complexPolynomial p).eval z := by
    simp only [aeval_def, eval₂_map, complexPolynomial, eval_map]
    congr 1
  intro z hw hr
  apply h z
  rw [hreverse, heval, heval]
  exact ⟨hw, hr⟩

/-- Interpret the actual finite-data source output as an integer modulus. -/
def sourceModulus (s : SparseEncoding.EncodedSource) : ℤ[X] :=
  X ^ s.dimension + ∑ k ∈ s.exponents, X ^ k

/-- The interpretation agrees with the modulus used in the source proofs. -/
theorem sourceModulus_encode {v r : ℕ} (C : SparseEncoding.Clauses v r) :
    sourceModulus (SparseEncoding.encode C) =
      X ^ (SparseEncoding.L (SparseEncoding.positionPrime v) v r) +
        SparseEncoding.P C (SparseEncoding.positionPrime v) := rfl

/-- The integer sparse modulus inherits the rational reciprocal-root promise. -/
theorem sparse_modulus_noCommonReciprocalRoot {v r : ℕ}
    (C : SparseEncoding.Clauses v r) {ell : ℕ} (hell : 0 < ell) :
    NoCommonReciprocalRoot (X ^ (SparseEncoding.L ell v r) + SparseEncoding.P C ell) := by
  apply noCommonReciprocalRoot_of_rational
  simpa only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    SparseEncoding.rationalP, Sidon.modulus] using
      SparseEncoding.encoding_no_common_root C hell

/-- The sparse polynomial satisfies the separation premises whenever its
dimension meets the required numerical cutoff. -/
theorem sparse_modulus_promises {v r ell : ℕ} (C : SparseEncoding.Clauses v r)
    (hell : 0 < ell) (hL : 64 ≤ SparseEncoding.L ell v r) :
    let w : ℤ[X] := X ^ (SparseEncoding.L ell v r) + SparseEncoding.P C ell
    w.Monic ∧ w.natDegree = SparseEncoding.L ell v r ∧
      64 ≤ SparseEncoding.L ell v r ∧ HasUnitConstant w ∧ NoCommonReciprocalRoot w := by
  have hPL : (SparseEncoding.P C ell).natDegree <
      SparseEncoding.L ell v r := by
    rw [SparseEncoding.degree_P C hell]
    have := (SparseEncoding.L_spec ell v r).1
    omega
  have hPdeg : (SparseEncoding.P C ell).degree < SparseEncoding.L ell v r :=
    degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hPL)
  refine ⟨monic_X_pow_add hPdeg, ?_, hL, ?_, sparse_modulus_noCommonReciprocalRoot C hell⟩
  · rw [natDegree_add_eq_left_of_natDegree_lt (by simpa using hPL)]
    simp
  · apply Or.inl
    have hL0 : SparseEncoding.L ell v r ≠ 0 := by omega
    simp [coeff_add, coeff_X_pow, Ne.symm hL0, SparseEncoding.constant_coeff]

/-- Every CNF, including a malformed source input, yields all modulus premises
of bounded-remainder separation. The source normalization is total. -/
theorem source_modulus_promises (f : Cslib.Logic.PL.CNF ℕ) :
    let s := BooleanSource.threeSATEncode f
    (sourceModulus s).Monic ∧ (sourceModulus s).natDegree = s.dimension ∧
      64 ≤ s.dimension ∧ HasUnitConstant (sourceModulus s) ∧
        NoCommonReciprocalRoot (sourceModulus s) := by
  exact sparse_modulus_promises
    (BooleanSource.finiteClauses (BooleanSource.fromThreeSAT f).formula)
    (SparseEncoding.positionPrime_spec _).1.pos
    (BooleanSource.boolean_source_dimension (BooleanSource.fromThreeSAT f).formula)

/-- Source-facing separation for the modulus produced from any CNF.
The degree and coefficient bounds are exactly the bounded-remainder contract. -/
theorem source_separation (f : Cslib.Logic.PL.CNF ℕ) (e : ℤ[X]) (D : ℕ)
    (hD : 16 * (BooleanSource.threeSATEncode f).dimension ^ 3 ≤ D)
    (hedeg : e.natDegree < (BooleanSource.threeSATEncode f).dimension)
    (heheight : CoefficientBound e ((BooleanSource.threeSATEncode f).dimension ^ 2))
    (hmem : SeparationCongruence (sourceModulus (BooleanSource.threeSATEncode f)) e D) :
    e = 0 := by
  obtain ⟨hw, hdeg, hL, hunit, hrec⟩ := source_modulus_promises f
  exact bounded_remainder_separation _ e _ D hw hdeg hL hunit hrec hD hedeg heheight hmem

end

end Power2ModuleSVP
