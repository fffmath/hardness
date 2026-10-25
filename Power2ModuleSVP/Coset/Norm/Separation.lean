module

public import Power2ModuleSVP.Coset.Norm.Estimates

/-!
# Bounded-remainder separation interfaces

Prove bounded-remainder separation from explicit Mahler, reciprocal-resultant, and divided-
derivative contracts. Coset/Norm/SourceSeparation.lean assembles their unconditional proofs and
the sparse-source instance. Root multisets retain repeated factors; the remainder degree cutoff
is less than L. The root-disjointness promise is supplied by the prime-exponent construction.

Paper: `paper/power2svp.pdf`, Section 3.2 (Lemmas 2–4, algebraic norm separation).
-/

@[expose] public section

namespace Power2ModuleSVP

open Polynomial

noncomputable section

/-- Outstanding Newton/power-sum input for `lem:elementary-mahler`.
For a nonreciprocal monic integer unit polynomial, a positive power sum of
order at most its degree differs from the inverse power sum by a nonzero
integer.  Bounding this difference gives precisely the witness below.
Only this witness, rather than the Mahler conclusion, is assumed. -/
structure ElementaryMahlerHypothesis : Prop where
  power_sum_witness : ∀ p : ℤ[X], p.Monic → HasUnitConstant p →
    p ≠ normalizedReciprocal p →
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ p.natDegree ∧
      1 ≤ 4 * (m : ℝ) *
        Real.exp ((m : ℝ) * Real.log (integerMahlerMeasure p)) *
          Real.log (integerMahlerMeasure p)

/-- Outstanding reciprocal-root product input for
`lem:reciprocal-resultant`.  This is the radial-gap estimate obtained from
the nonzero integer reciprocal resultant by bounding its off-diagonal
factors.  The subsequent binomial estimate is proved in the auxiliary file. -/
structure ReciprocalResultantHypothesis : Prop where
  radial_gap_bound : ∀ p : ℤ[X], p.Monic → HasUnitConstant p →
    NoCommonReciprocalRoot p →
    1 ≤ (2 : ℝ) ^ (p.natDegree * (p.natDegree - 1)) *
      integerMahlerMeasure p ^ (2 * (p.natDegree - 1)) * radialGapProduct p

/-- Outstanding factor/multiplicity extraction in `lem:elementary-separation`.
The witness is an irreducible monic factor `p` and the first nonzero divided
derivative of `e` at its roots.  All divided derivatives of `w` through that
order vanish.  This hypothesis contains no congruence, binomial exponent,
height, or analytic estimate and does not assume the separation conclusion.

The budget `(j+1)*degree p ≤ L` must be retained: dropping it loses the
polynomial bound on the norm when `w` has repeated factors. -/
structure DividedDerivativeWitnessHypothesis : Prop where
  witness : ∀ (w e : ℤ[X]) (L : ℕ), w.Monic → w.natDegree = L →
    HasUnitConstant w → e.degree < L → e ≠ 0 →
    ∃ (p : ℤ[X]) (j : ℕ),
      p.Monic ∧ Irreducible p ∧ p ∣ w ∧ HasUnitConstant p ∧
      0 < p.natDegree ∧ (j + 1) * p.natDegree ≤ L ∧
      ∀ z ∈ (complexPolynomial p).roots,
        (complexPolynomial (hasseDeriv j e)).eval z ≠ 0 ∧
          (∀ k < j, (complexPolynomial (hasseDeriv k e)).eval z = 0) ∧
          (∀ k ≤ j, (complexPolynomial (hasseDeriv k w)).eval z = 0)

/-- The explicitly unproved inputs of this partial formalization. -/
structure NormSeparationHypothesis : Prop extends
    ElementaryMahlerHypothesis, ReciprocalResultantHypothesis,
    DividedDerivativeWitnessHypothesis

/-- `lem:elementary-mahler`, conditional only on the named power-sum input.
The real-variable argument and its constant `12` are proved. -/
theorem elementary_mahler (h : ElementaryMahlerHypothesis)
    {p : ℤ[X]} (hp : p.Monic) (hu : HasUnitConstant p)
    (hneq : p ≠ normalizedReciprocal p) :
    1 / (12 * (p.natDegree : ℝ)) ≤ Real.log (integerMahlerMeasure p) := by
  have hw := h.power_sum_witness p hp hu hneq
  obtain ⟨m, hm, hmd, hbound⟩ := hw
  exact mahler_log_lower_bound_of_power_sum_witness p.natDegree _ (by omega)
    (log_integerMahlerMeasure_nonneg hp) ⟨m, hm, hmd, hbound⟩

/-- `lem:reciprocal-resultant`, conditional on the radial-gap input.
Real subtraction is used in the exponent, since this statement also allows
`D < 2*degree p`. -/
theorem reciprocal_resultant (h : ReciprocalResultantHypothesis)
    {p : ℤ[X]} (hp : p.Monic) (hu : HasUnitConstant p)
    (hroot : NoCommonReciprocalRoot p) (D : ℕ) (hD : 1 ≤ D) :
    (2 : ℝ) ^ (-((p.natDegree : ℝ) ^ 2)) *
      integerMahlerMeasure p ^ ((D : ℝ) - 2 * p.natDegree) ≤
        ‖(Polynomial.resultant p (separationBinomial D) : ℤ)‖ := by
  have hb := reciprocal_resultant_lower_bound_of_radial_gap_bound hp hu
    (h.radial_gap_bound p hp hu hroot) hD
  rw [rootEvaluationProduct_eq_resultant hp] at hb
  simpa only [Complex.norm_intCast, Int.norm_eq_abs, Int.cast_abs] using hb

/-- The algebraic norm comparison follows from the divided-derivative
witness; its coefficient growth and integer-norm lower bound are proved. -/
theorem exists_factor_norm_comparison (h : DividedDerivativeWitnessHypothesis)
    {w e : ℤ[X]} {L D : ℕ} (hw : w.Monic) (hdeg : w.natDegree = L)
    (hu : HasUnitConstant w) (hroot : NoCommonReciprocalRoot w)
    (hL : 1 ≤ L) (hD : 1 ≤ D) (he : e.degree < L) (hH : CoefficientBound e (L ^ 2))
    (he0 : e ≠ 0) (hcong : SeparationCongruence w e D) :
    ∃ p : ℤ[X], p.Monic ∧ HasUnitConstant p ∧ NoCommonReciprocalRoot p ∧
      0 < p.natDegree ∧ p.natDegree ≤ L ∧
      ‖(Polynomial.resultant p (separationBinomial D) : ℤ)‖ ≤
        (L : ℝ) ^ (3 * L) * integerMahlerMeasure p ^ (L - 1) := by
  obtain ⟨p, j, hp, _hirr, hpw, hpu, hpd, hbudget, hvan⟩ :=
    h.witness w e L hw hdeg hu he he0
  have hpr := noCommonReciprocalRoot_of_dvd hroot hpw
  obtain ⟨q, u, hlift⟩ := hcong
  have hlift' : complexPolynomial e = complexPolynomial (separationBinomial D) *
      complexPolynomial q + complexPolynomial w * complexPolynomial u := by
    simpa [complexPolynomial] using congrArg complexPolynomial hlift
  have hlocal (z : ℂ) (hz : z ∈ (complexPolynomial p).roots) :
      (complexPolynomial (hasseDeriv j e)).eval z =
        (complexPolynomial (separationBinomial D)).eval z *
          (complexPolynomial (hasseDeriv j q)).eval z ∧
      (complexPolynomial (hasseDeriv j q)).eval z ≠ 0 := by
    obtain ⟨hej, helow, hwlow⟩ := hvan z hz
    have ht := separationBinomial_eval_ne_zero hp hpu hpr hz hD
    have hsimp (a : ℤ[X]) (k : ℕ) :
        hasseDeriv k (complexPolynomial a) = complexPolynomial (hasseDeriv k a) :=
      hasseDeriv_map _ _ _
    simpa only [hsimp] using first_hasseDeriv_lift hlift' z j ht
      (by simpa only [hsimp] using hej)
      (by simpa only [hsimp] using helow)
      (by simpa only [hsimp] using hwlow)
  have hb : rootEvaluationProduct p (hasseDeriv j q) ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro ha
    obtain ⟨z, hz, hzero⟩ := Multiset.mem_map.mp ha
    exact (hlocal z hz).2 hzero
  have heval := fun z hz => (hlocal z hz).1
  refine ⟨p, hp, hpu, noCommonReciprocalRoot_of_dvd hroot hpw, hpd, ?_, ?_⟩
  · nlinarith
  have hprod := rootEvaluationProduct_eq_mul heval
  have hb1 := one_le_norm_rootEvaluationProduct hp (hasseDeriv j q) hb
  have hsmall := norm_hasseDeriv_rootEvaluationProduct_le hp hL he hH hbudget
  have hprodle : ‖rootEvaluationProduct p (separationBinomial D)‖ ≤
      ‖rootEvaluationProduct p (hasseDeriv j e)‖ := by
    rw [hprod, norm_mul]
    nlinarith [norm_nonneg (rootEvaluationProduct p (separationBinomial D))]
  rw [rootEvaluationProduct_eq_resultant hp] at hprodle
  simpa only [Complex.norm_intCast, Int.norm_eq_abs, Int.cast_abs] using
    hprodle.trans hsmall

/-- Combining the two norm bounds with the Mahler lower bound forces the
logarithmic inequality that the numerical lemma rules out. -/
theorem norm_bounds_impossible {L d D : ℕ} {M : ℝ}
    (hL : 64 ≤ L) (hd : 0 < d) (hdL : d ≤ L) (hD : 16 * L ^ 3 ≤ D)
    (hM : 0 < M) (hmahler : 1 / (12 * (d : ℝ)) ≤ Real.log M)
    (hbounds : (2 : ℝ) ^ (-((d : ℝ) ^ 2)) * M ^ ((D : ℝ) - 2 * d) ≤
      (L : ℝ) ^ (3 * L) * M ^ (L - 1)) : False := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlower : 0 < (2 : ℝ) ^ (-((d : ℝ) ^ 2)) * M ^ ((D : ℝ) - 2 * d) :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hM _)
  have hlog := Real.log_le_log hlower hbounds
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_rpow (by norm_num), Real.log_rpow hM,
    Real.log_pow, Real.log_pow] at hlog
  have hsub : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hsub] at hlog
  push_cast at hlog
  have hD' : 16 * (L : ℝ) ^ 3 ≤ D := by exact_mod_cast hD
  have hL' : (64 : ℝ) ≤ L := by exact_mod_cast hL
  have hdL' : (d : ℝ) ≤ L := by exact_mod_cast hdL
  have hc : 0 ≤ (D : ℝ) - 2 * d - L + 1 := by
    have : (L : ℝ) ^ 3 ≥ 3 * L := by nlinarith [sq_nonneg ((L : ℝ) - 1)]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hmahler hc
  rw [mul_one_div] at hmul
  have hineq : ((D : ℝ) - 2 * d - L + 1) / (12 * d) ≤
      (d : ℝ) ^ 2 * Real.log 2 + 3 * (L : ℝ) * Real.log L := by
    nlinarith
  exact (not_lt_of_ge hineq) (separation_logarithmic_gap L d D hL hd hdL hD)

/-- `lem:elementary-separation`, with its three algebraic contracts explicit.
No restriction on the coefficients of `w`, squarefreeness of `w`, or
power-of-two condition on `D` is needed. -/
theorem elementary_separation (h : NormSeparationHypothesis)
    {w e : ℤ[X]} {L D : ℕ} (hw : w.Monic) (hdeg : w.natDegree = L)
    (hu : HasUnitConstant w) (hroot : NoCommonReciprocalRoot w)
    (hL : 64 ≤ L) (hD : 16 * L ^ 3 ≤ D)
    (he : e.degree < L) (hH : CoefficientBound e (L ^ 2))
    (hcong : SeparationCongruence w e D) : e = 0 := by
  by_contra he0
  have hD1 : 1 ≤ D := by
    have : 1 ≤ L ^ 3 := one_le_pow₀ (by omega : 1 ≤ L)
    omega
  obtain ⟨p, hp, hpu, hpr, hpd, hpdL, hupper⟩ :=
    exists_factor_norm_comparison h.toDividedDerivativeWitnessHypothesis
      hw hdeg hu hroot (by omega) hD1 he hH he0 hcong
  have hneq := ne_normalizedReciprocal hp hpd hpu hpr
  have hm := elementary_mahler h.toElementaryMahlerHypothesis hp hpu hneq
  have hlower := reciprocal_resultant h.toReciprocalResultantHypothesis hp hpu hpr D hD1
  exact norm_bounds_impossible hL hpd hpdL hD (integerMahlerMeasure_pos hp) hm
    (hlower.trans hupper)

/-- Convenience form accepting the lifted polynomial identity directly. -/
theorem elementary_separation_of_eq (h : NormSeparationHypothesis)
    {w e : ℤ[X]} {L D : ℕ} (hw : w.Monic) (hdeg : w.natDegree = L)
    (hu : HasUnitConstant w) (hroot : NoCommonReciprocalRoot w)
    (hL : 64 ≤ L) (hD : 16 * L ^ 3 ≤ D)
    (he : e.degree < L) (hH : CoefficientBound e (L ^ 2))
    (q u : ℤ[X]) (hlift : e = (1 + X ^ D) * q + w * u) : e = 0 :=
  elementary_separation h hw hdeg hu hroot hL hD he hH ⟨q, u, hlift⟩

end

end Power2ModuleSVP
