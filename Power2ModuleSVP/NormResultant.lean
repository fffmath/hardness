module

public import Power2ModuleSVP.NormResultantAux

/-!
# The reciprocal resultant bound

This file discharges `ReciprocalResultantHypothesis`, the radial-gap input
to `lem:reciprocal-resultant`.  The normalized reciprocal resultant is a
nonzero integer.  Its root product is bounded by keeping the diagonal
radial gaps and estimating the remaining factors by Mahler maxima.

Audit: the existing hypothesis is correct as stated, including constant
polynomials and repeated roots.  No replacement separation interface is
needed.  The other two inputs to `NormSeparationHypothesis` are independent
of this result.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Power2ModuleSVP

open Polynomial
open scoped BigOperators

noncomputable section

/-- The nonzero integer reciprocal resultant bounds the radial-gap product.
All roots are counted with their multiplicities. -/
theorem reciprocal_radial_gap_bound {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) (hroot : NoCommonReciprocalRoot p) :
    1 ≤ (2 : ℝ) ^ (p.natDegree * (p.natDegree - 1)) *
      integerMahlerMeasure p ^ (2 * (p.natDegree - 1)) * radialGapProduct p := by
  classical
  let s := (complexPolynomial p).roots
  have hcard : Fintype.card s = p.natDegree := by
    rw [Multiset.card_coe, ← (IsAlgClosed.splits _).natDegree_eq_card_roots,
      complexPolynomial_natDegree hp]
  have hprod (f : ℂ → ℝ) : (∏ z : s, f (z : ℂ)) = (s.map f).prod :=
    congrArg Multiset.prod (Multiset.map_univ s f)
  have hmahler : (s.map (fun z => max 1 ‖z‖)).prod = integerMahlerMeasure p := by
    rw [integerMahlerMeasure, mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
      (complexPolynomial_monic hp).leadingCoeff, norm_one, one_mul]
  have hforward : (∏ z : s, max 1 ‖(z : ℂ)‖) = integerMahlerMeasure p :=
    (hprod _).trans hmahler
  have hinverse : (∏ z : s, max 1 ‖(z : ℂ)‖⁻¹) = integerMahlerMeasure p :=
    (hprod _).trans (prod_max_inv_norm_eq_mahler hp hu)
  have hgap : (∏ z : s, |‖(z : ℂ)‖ - ‖(z : ℂ)‖⁻¹|) = radialGapProduct p :=
    hprod (fun z => |‖z‖ - ‖z‖⁻¹|)
  have hupper := prod_norm_sub_inv_conj_le (fun z : s => (z : ℂ))
    (fun z => root_ne_zero_of_unitConstant hu (show (z : ℂ) ∈ s from Multiset.coe_mem))
  rw [hcard, hforward, hinverse, hgap, ← pow_two, ← pow_mul] at hupper
  have hlower := one_le_norm_rootEvaluationProduct hp (normalizedReciprocal p)
    (rootEvaluationProduct_normalizedReciprocal_ne_zero hp hu hroot)
  rw [rootEvaluationProduct_normalizedReciprocal hp hu] at hlower
  simp only [norm_prod] at hlower
  exact hlower.trans hupper

/-- The reciprocal-resultant input to bounded-remainder separation is proved. -/
theorem reciprocalResultantHypothesis_holds : ReciprocalResultantHypothesis where
  radial_gap_bound _p hp hu hroot := reciprocal_radial_gap_bound hp hu hroot

/-- Unconditional `lem:reciprocal-resultant` under its polynomial premises. -/
theorem reciprocal_resultant_bound {p : ℤ[X]} (hp : p.Monic)
    (hu : HasUnitConstant p) (hroot : NoCommonReciprocalRoot p)
    (D : ℕ) (hD : 1 ≤ D) :
    (2 : ℝ) ^ (-((p.natDegree : ℝ) ^ 2)) *
      integerMahlerMeasure p ^ ((D : ℝ) - 2 * p.natDegree) ≤
        ‖(Polynomial.resultant p (separationBinomial D) : ℤ)‖ :=
  reciprocal_resultant reciprocalResultantHypothesis_holds hp hu hroot D hD

end

end Power2ModuleSVP
