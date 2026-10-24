import Power2ModuleSVP.SourceMap
import Power2ModuleSVP.Homogenization
import Power2ModuleSVP.NormFinal

/-! Total reductions and their semantic specifications. The coset degree is
cubic in the affine dimension. Module packing starts at its final degree,
which also accommodates the fixed anchor cutoff. -/
namespace Power2ModuleSVP
open Cslib.Logic.PL Cslib.Complexity

/-- The executable source and the semantic packing interface agree exactly. -/
theorem sourceMap_eq_threeSATToAffine (f : CNF ℕ) :
    sourceMap f = threeSATToAffine f := by
  rw [sourceMap_eq]
  rfl

/-- Total SAT-to-coset reduction, including all malformed CNFs. -/
def cosetReduction (f : CNF ℕ) : CosetInput :=
  let q := sourceMap f
  packCoset (packingDegree q.1) q

theorem cosetReduction_eq (f : CNF ℕ) :
    cosetReduction f = threeSATToCoset f := by
  simp only [cosetReduction, sourceMap_eq_threeSATToAffine, threeSATToCoset]

theorem cosetReduction_correct (f : CNF ℕ) :
    f ∈ ThreeSAT ↔ cosetReduction f ∈ CosetLang := by
  rw [cosetReduction_eq]
  exact threeSATToCoset_correct normSeparationHypothesis_holds f

theorem sourceMap_wellFormed (f : CNF ℕ) : AffineInput.WellFormed (sourceMap f) := by
  rw [sourceMap_eq_threeSATToAffine]
  exact threeSATToAffine_wellFormed f

theorem cosetReduction_wellFormed (f : CNF ℕ) :
    (cosetReduction f).WellFormed :=
  packCoset_wellFormed _ (sourceMap_wellFormed f) _
    (dyadicCeil_dyadic _) (le_dyadicCeil _)

theorem cosetReduction_degree_bound (f : CNF ℕ) :
    (cosetReduction f).1 < 32 * (sourceMap f).1 ^ 3 :=
  packingDegree_lt (by have := (sourceMap_wellFormed f).L_large; omega)

/-- An explicit polynomial bound in the number of input clauses. -/
theorem cosetReduction_degree_polynomial_bound (f : CNF ℕ) :
    (cosetReduction f).1 <
      32 * (1125 * (7 * f.length + 17) * (12 * f.length + 28) ^ 2) ^ 3 :=
  (cosetReduction_degree_bound f).trans_le
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (sourceMap_dimension_bound f) _))

/-- The coset outputs have the restricted coefficient alphabets. -/
theorem cosetReduction_alphabet (f : CNF ℕ) :
    (∀ i : Fin (cosetReduction f).1,
      IdealCVP.ofList (cosetReduction f).2.1 i = 0 ∨
      IdealCVP.ofList (cosetReduction f).2.1 i = 2) ∧
    (∀ i : Fin (cosetReduction f).1,
      IdealCVP.ofList (cosetReduction f).2.2 i = -1 ∨
      IdealCVP.ofList (cosetReduction f).2.2 i = 0 ∨
      IdealCVP.ofList (cosetReduction f).2.2 i = 1 ∨
      IdealCVP.ofList (cosetReduction f).2.2 i = 3) :=
  packCoset_alphabet _ (sourceMap_wellFormed f) _

/-- The ring degree required by the uniform anchor algorithm. -/
def moduleReductionDegree (k0 : ℕ) (f : CNF ℕ) : ℕ :=
  modulePackingDegree k0 (sourceMap f).1

/-- A module reduction parameterized by a fixed cutoff and a uniform family. -/
def moduleReduction (k0 : ℕ) (J : ℕ → List ℤ) (f : CNF ℕ) : SVPInput :=
  triangularInput (packCoset (moduleReductionDegree k0 f) (sourceMap f))
    (J (moduleReductionDegree k0 f))

theorem moduleReduction_eq (k0 : ℕ) (J : ℕ → List ℤ) (f : CNF ℕ) :
    moduleReduction k0 J f = threeSATToModule k0 J f := by
  simp only [moduleReduction, moduleReductionDegree, sourceMap_eq_threeSATToAffine,
    threeSATToModule]

theorem moduleReductionDegree_dyadic (k0 : ℕ) (f : CNF ℕ) :
    Dyadic (moduleReductionDegree k0 f) := modulePackingDegree_dyadic _ _

theorem moduleReductionDegree_cutoff (k0 : ℕ) (f : CNF ℕ) :
    2 ^ k0 ≤ moduleReductionDegree k0 f := modulePackingDegree_cutoff _ _

theorem moduleReduction_degree_bound (k0 : ℕ) (J : ℕ → List ℤ) (f : CNF ℕ) :
    (moduleReduction k0 J f).1 < 2 ^ k0 + 32 * (sourceMap f).1 ^ 3 :=
  modulePackingDegree_lt k0 (by have := (sourceMap_wellFormed f).L_large; omega)

theorem moduleReduction_degree_polynomial_bound
    (k0 : ℕ) (J : ℕ → List ℤ) (f : CNF ℕ) :
    (moduleReduction k0 J f).1 < 2 ^ k0 +
      32 * (1125 * (7 * f.length + 17) * (12 * f.length + 28) ^ 2) ^ 3 :=
  (moduleReduction_degree_bound k0 J f).trans_le
    (Nat.add_le_add_left (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (sourceMap_dimension_bound f) _)) _)

/-- Correctness uses only the anchor specification at the final degree. -/
theorem moduleReduction_correct (k0 : ℕ) (J : ℕ → List ℤ)
    (hfamily : ∀ d, Dyadic d → 2 ^ k0 ≤ d →
      (J d).length = d ∧ Signs (IdealCVP.ofList (d := d) (J d)) ∧
        Rigid (IdealCVP.ofList (d := d) (J d))) (f : CNF ℕ) :
    f ∈ ThreeSAT ↔ moduleReduction k0 J f ∈ ModuleSVPLang := by
  obtain ⟨hlen, hJs, hJ⟩ := hfamily _ (moduleReductionDegree_dyadic k0 f)
    (moduleReductionDegree_cutoff k0 f)
  rw [moduleReduction_eq]
  unfold moduleReductionDegree at hlen hJs hJ
  rw [sourceMap_eq_threeSATToAffine] at hlen hJs hJ
  exact threeSAT_module_correct normSeparationHypothesis_holds f k0 J hlen hJs hJ

theorem moduleReduction_wellFormed (k0 : ℕ) (J : ℕ → List ℤ)
    (hfamily : ∀ d, Dyadic d → 2 ^ k0 ≤ d →
      (J d).length = d ∧ Signs (IdealCVP.ofList (d := d) (J d)) ∧
        Rigid (IdealCVP.ofList (d := d) (J d))) (f : CNF ℕ) :
    (moduleReduction k0 J f).WellFormed := by
  obtain ⟨hlen, hJs, _⟩ := hfamily _ (moduleReductionDegree_dyadic k0 f)
    (moduleReductionDegree_cutoff k0 f)
  exact triangularInput_wellFormed _
    (packCoset_wellFormed _ (sourceMap_wellFormed f) _
      (moduleReductionDegree_dyadic k0 f) (modulePackingDegree_large _ _))
    _ hlen hJs

/-- All four stored columns meet the hardness-output coefficient promises. -/
theorem moduleReduction_alphabet (k0 : ℕ) (J : ℕ → List ℤ)
    (hfamily : ∀ d, Dyadic d → 2 ^ k0 ≤ d →
      (J d).length = d ∧ Signs (IdealCVP.ofList (d := d) (J d)) ∧
        Rigid (IdealCVP.ofList (d := d) (J d))) (f : CNF ℕ) :
    let x := moduleReduction k0 J f
    (∀ i : Fin x.1, IdealCVP.ofList x.2.1.1 i = 0 ∨
      IdealCVP.ofList x.2.1.1 i = 2) ∧
    (∀ i : Fin x.1, IdealCVP.ofList x.2.1.2 i = 0) ∧
    (∀ i : Fin x.1, IdealCVP.ofList x.2.2.1 i = -1 ∨
      IdealCVP.ofList x.2.2.1 i = 0 ∨ IdealCVP.ofList x.2.2.1 i = 1 ∨
      IdealCVP.ofList x.2.2.1 i = 3) ∧
    Signs (IdealCVP.ofList (d := x.1) x.2.2.2) := by
  obtain ⟨_, hJs, _⟩ := hfamily _ (moduleReductionDegree_dyadic k0 f)
    (moduleReductionDegree_cutoff k0 f)
  have ha := packCoset_alphabet _ (sourceMap_wellFormed f) (moduleReductionDegree k0 f)
  refine ⟨ha.1, ?_, ha.2, hJs⟩
  intro i
  exact congrFun (ofList_replicate_zero (moduleReductionDegree k0 f)) i

end Power2ModuleSVP
