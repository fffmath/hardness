module

public import Power2ModuleSVP.Coset.Norm.FactorMultiplicity

/-!
# Unconditional divided-derivative witnesses

This discharges the factor/multiplicity extraction in
`lem:elementary-separation`, including repeated factors of the modulus.
An irreducible factor with insufficient exponent in the nonzero remainder
exists because a polynomial of smaller degree cannot be divisible by the
monic modulus.  Its exponent gives the first nonzero Hasse derivative at
all its complex roots and retains the required degree budget.

Audit: the existing witness hypothesis is correct without any squarefree
assumption on the modulus.  Separability is used only for the selected
irreducible factor, after passing to the rational polynomial ring.

Paper: `paper/power2svp.pdf`, Section 3.2 (Lemmas 2–4, algebraic norm separation).
-/

@[expose] public section

namespace Power2ModuleSVP

open Polynomial

noncomputable section

/-- The algebraic factor/multiplicity input to bounded-remainder separation
holds unconditionally over the integers. -/
theorem dividedDerivativeWitnessHypothesis_holds : DividedDerivativeWitnessHypothesis := by
  constructor
  intro w e L hw hdeg hu he he0
  have hndvd : ¬w ∣ e := by
    intro hdvd
    have hle := degree_le_of_dvd hdvd he0
    rw [degree_eq_natDegree hw.ne_zero, hdeg] at hle
    exact (not_le_of_gt he) hle
  obtain ⟨p, j, hp, hirr, hpw, hepow, hendvd, hwpow⟩ :=
    exists_monic_irreducible_power_gap hw he0 hndvd
  have hpdeg : 0 < p.natDegree := hp.natDegree_pos.mpr (by
    intro h
    exact hirr.not_isUnit (h ▸ isUnit_one))
  have hbudget := natDegree_le_of_dvd hwpow hw.ne_zero
  rw [natDegree_pow, hdeg] at hbudget
  refine ⟨p, j, hp, hirr, hpw, hasUnitConstant_of_dvd hu hpw, hpdeg, hbudget, ?_⟩
  intro z hz
  have hzroot := isRoot_of_mem_roots hz
  have hfe := FiniteMultiplicity.of_not_isUnit hirr.not_isUnit he0
  have hfw := FiniteMultiplicity.of_not_isUnit hirr.not_isUnit hw.ne_zero
  have hej : multiplicity p e = j := hfe.multiplicity_eq_iff.mpr ⟨hepow, hendvd⟩
  have hwj : j < multiplicity p w := hfw.pow_dvd_iff_le_multiplicity.mp hwpow
  have hme : (complexPolynomial e).rootMultiplicity z = j := by
    rw [rootMultiplicity_complex_eq_multiplicity hp hirr he0 hzroot, hej]
  have hmw : j < (complexPolynomial w).rootMultiplicity z := by
    rwa [rootMultiplicity_complex_eq_multiplicity hp hirr hw.ne_zero hzroot]
  have heC0 : complexPolynomial e ≠ 0 := by
    intro h
    apply he0
    apply Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
    simpa only [complexPolynomial, Polynomial.map_zero] using h
  have hehasse := hasseDeriv_eval_at_rootMultiplicity heC0 z
  have hwhasse := (hasseDeriv_eval_at_rootMultiplicity (complexPolynomial_monic hw).ne_zero z).2
  rw [hme] at hehasse
  have hmap (f : ℤ[X]) (k : ℕ) :
      hasseDeriv k (complexPolynomial f) = complexPolynomial (hasseDeriv k f) :=
    hasseDeriv_map _ _ _
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hmap] using hehasse.1
  · intro k hk
    simpa only [hmap] using hehasse.2 k hk
  · intro k hk
    simpa only [hmap] using hwhasse k (hk.trans_lt hmw)

end

end Power2ModuleSVP
