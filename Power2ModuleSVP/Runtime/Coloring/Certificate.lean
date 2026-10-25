import Power2ModuleSVP.Runtime.Coloring.Gram.Identification
import Power2ModuleSVP.Runtime.Coloring.HeavyIndices
import Power2ModuleSVP.Runtime.Coloring.PartialCertificate
import Power2ModuleSVP.Runtime.Coloring.PartialCallGrowth

/-!
# Certificate

Native certificates for the unchanged partial and full coloring programs.

The canonical-projector denominator bound is unconditional. It follows
from exact integer scaling, the Gram inverse/adjugate formula, a rational
Gram kernel argument, and the certified determinant's polynomial bit bound.
All walk and recursive-input size invariants are proved for the actual
programs, including malformed-input branches.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open PartialColoringAlg

/-- Complete native partial-coloring certificate from the local projector
arithmetic bound; preparation, sorting and all walk prefixes are certified. -/
theorem partialColoringNative_of_projector
    (h : CanonicalProjectorDenominatorHypothesis) : PartialColoringNativeHypothesis :=
  partialColorNative_of_projector_and_sort h heavyIndicesNative

/-- The selected full recursion has uniformly bounded intermediate inputs;
no universal closure assertion for arbitrary partial programs is used. -/
theorem fullColoringNative_partialColor_of_projector
    (h : CanonicalProjectorDenominatorHypothesis) : FullColoringNativeHypothesis partialColor :=
  fullColor_partialColor_native_of_denominator_growth
    (partialColoringNative_of_projector h) (partialDenominatorGrowth_of_projector h)

/-- Derive the native partial-coloring certificate from the Gram projector formula. -/
theorem partialColoringNative_of_gramFormula (h : GramProjectorFormulaHypothesis) :
    PartialColoringNativeHypothesis :=
  partialColoringNative_of_projector (canonicalProjectorDenominator_of_gramFormula h)

/-- Derive the full-coloring runtime certificate from the Gram projector formula. -/
theorem fullColoringNative_partialColor_of_gramFormula (h : GramProjectorFormulaHypothesis) :
    FullColoringNativeHypothesis partialColor :=
  fullColoringNative_partialColor_of_projector (canonicalProjectorDenominator_of_gramFormula h)

/-- Both original native contracts reduce to one purely local matrix
identity, with no coloring-correctness or machine fields in that premise. -/
theorem coloringNative_of_schur (h : GramSchurUpdateHypothesis) :
    PartialColoringNativeHypothesis ∧ FullColoringNativeHypothesis partialColor :=
  ⟨partialColoringNative_of_projector (canonicalProjectorDenominator_of_schur h),
    fullColoringNative_partialColor_of_projector (canonicalProjectorDenominator_of_schur h)⟩

/-- The unchanged concrete partial-coloring program has a uniform native
multitape polynomial-time certificate on every raw input. -/
theorem partialColoringNative_holds : PartialColoringNativeHypothesis :=
  partialColoringNative_of_projector canonicalProjectorDenominator

/-- The unchanged selected full-coloring recursion has a uniform native
certificate, with polynomial encoding bounds at every recursive call. -/
theorem fullColoringNative_partialColor : FullColoringNativeHypothesis partialColor :=
  fullColoringNative_partialColor_of_projector canonicalProjectorDenominator

end Power2ModuleSVP.ColoringRuntime
