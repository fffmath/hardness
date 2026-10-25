import Power2ModuleSVP.Seed.Flat.Bounds
import Power2ModuleSVP.Seed.Flat.Rounding
import Power2ModuleSVP.Runtime.Seed.Composition
import Power2ModuleSVP.Seed.SineKernel.Specification

/-!
# Semantic and runtime assembly of the flat seed

Compose rational preprocessing, two full-coloring calls, sine-kernel estimates, Taylor
propagation, and Laurent assembly into a spectral seed family. The preparation interfaces in
this file are discharged for the concrete frontend in FlatFrontend/Geometry/Certificate.lean;
Seed/Family.lean assembles the unconditional family.

Paper: `paper/power2svp.pdf`, Appendix A (Theorem 5, the deterministic flat seed).
-/
namespace Power2ModuleSVP
open Turing.MultiTapeTM

/-- The number of derivative constraints in the second seed coloring call. -/
def seedDerivativeRows (d : ℕ) : ℕ := 16 * seedN d * (seedN d + 1)

/-- An empty interval family uses an empty first coloring problem. Keeping
`N` rows when `J = 0` would make the entropy premise impossible. -/
def seedIntervalRows (N J : ℕ) : ℕ := if J = 0 then 0 else N

/-- Mathematical data for a single prepared degree. These witnesses are
used only in proofs; the executable frontend is `FlatSeedFrontend`. -/
structure FlatSeedAnalyticData (d : ℕ) where
  J : ℕ
  intervals : SeedKernelIntervals (seedN d) J
  foldAngle : ℝ → ℝ
  cosine : ℝ → ℝ
  evenPart : ℝ → ℝ
  firstV : Fin (seedIntervalRows (seedN d) J) → Fin J → ℚ
  firstX : Fin J → ℚ
  firstC : Fin (seedIntervalRows (seedN d) J) → ℚ
  target : (Fin J → ℚ) → ℝ → ℝ
  fractional : (Fin J → ℚ) → Fin (seedN d) → ℝ
  secondV : (Fin J → ℚ) → Fin (seedDerivativeRows d) → Fin (seedN d) → ℚ
  secondX : (Fin J → ℚ) → Fin (seedN d) → ℚ
  secondC : (Fin J → ℚ) → Fin (seedDerivativeRows d) → ℚ
  oddPart : (Fin (seedN d) → ℚ) → ℝ → ℝ

namespace FlatSeedAnalyticData

/-- The full-coloring specification for the first, interval-based seed coloring call. -/
def FirstSpec {d : ℕ} (D : FlatSeedAnalyticData d) (α : Fin D.J → ℚ) : Prop :=
  FullColoringSpec D.firstV D.firstX α D.firstC

/-- The full-coloring specification for the second, coefficient-based seed coloring call. -/
def SecondSpec {d : ℕ} (D : FlatSeedAnalyticData d)
    (α : Fin D.J → ℚ) (y : Fin (seedN d) → ℚ) : Prop :=
  FullColoringSpec (D.secondV α) (D.secondX α) y (D.secondC α)

end FlatSeedAnalyticData

/-- Preparation interface connecting from the rational cell program to the geometric
interval data and the real Rudin--Shapiro parts. This includes the parameter
choice and exact rational-grid construction, rather than assuming that a
generic sublevel-component lemma already constructs that grid. -/
structure FlatSeedGeometryHypothesis (A : FlatSeedFrontend) {d : ℕ}
    (D : FlatSeedAnalyticData d) : Prop where
  interval_input : A.intervalInput d = partialColoringInput D.firstV D.firstX D.firstC
  first_cube : RationalCube D.firstX
  first_nonnegative : ∀ i, 0 ≤ D.firstC i
  first_entropy : coloringEntropy D.firstC ≤ (D.J : ℝ) / 64
  interval_count : D.J * 2 ^ 66 ≤ seedN d
  fold_mem : ∀ θ, D.foldAngle θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
  cosine_good : ∀ θ, ¬ D.intervals.contains (D.foldAngle θ) →
    seedCosineMargin * Real.sqrt (seedN d) ≤ |D.cosine θ|
  even_bound : ∀ θ, |D.evenPart θ| ≤ 6 * Real.sqrt (seedN d)

/-- First rational coloring bridge. `kernel` is the precise
absolute-value reflection identity, not the sine-kernel lower estimate.
The latter is obtained from `SineKernelDecompositionHypothesis`. -/
structure FlatSeedIntervalRoundingHypothesis (A : FlatSeedFrontend) {d : ℕ}
    (D : FlatSeedAnalyticData d) : Prop where
  kernel : ∀ α, D.FirstSpec α → ∀ θ,
    |D.target α θ| = |9000 * Real.sqrt (seedN d) *
      D.intervals.transform (fun i => (α i : ℝ)) (D.foldAngle θ)|
  coefficient_input : ∀ α, D.FirstSpec α →
    A.coefficientInput (d, List.ofFn α) =
      partialColoringInput (D.secondV α) (D.secondX α) (D.secondC α)
  second_cube : ∀ α, D.FirstSpec α → RationalCube (D.secondX α)
  second_nonnegative : ∀ α, D.FirstSpec α → ∀ i, 0 ≤ D.secondC α i
  second_entropy : ∀ α, D.FirstSpec α →
    coloringEntropy (D.secondC α) ≤ (seedN d : ℝ) / 64

/-- Identification and enclosures for the rational derivative
matrices. No discrepancy or Taylor bound is assumed: those are proved from
the row identities, entry enclosures and the full-coloring specification.
The trivial whole-circle bound and reflections are recorded explicitly. -/
structure FlatSeedDerivativeRoundingHypothesis {d : ℕ}
    (D : FlatSeedAnalyticData d) : Prop where
  error_degree : ∀ α y, D.FirstSpec α → D.SecondSpec α y →
    HasTrigDegree (2 * seedN d) (fun θ => D.oddPart y θ - D.target α θ)
  error_global : ∀ α y, D.FirstSpec α → D.SecondSpec α y → ∀ θ,
    |D.oddPart y θ - D.target α θ| ≤ 2 * seedN d
  error_reflect : ∀ α y, D.FirstSpec α → D.SecondSpec α y → ∀ θ,
    |D.oddPart y θ - D.target α θ| =
      |D.oddPart y (D.foldAngle θ) - D.target α (D.foldAngle θ)|
  starting_error : ∀ α, D.FirstSpec α → ∀ j,
    |(D.secondX α j : ℝ) - D.fractional α j| ≤ (seedRoundingError (seedN d) : ℝ)
  sample_rows : ∀ α, D.FirstSpec α →
    ∀ k : Fin (16 * seedN d), ∀ ell ≤ seedN d,
      ∃ (i : Fin (seedDerivativeRows d)) (v : Fin (seedN d) → ℝ),
        D.secondC α i = 12 + (ell : ℚ) ∧
        (∀ j, |v j| ≤ 1) ∧
        (∀ j, |v j - D.secondV α i j| ≤ (seedRoundingError (seedN d) : ℝ)) ∧
        ∀ y, D.SecondSpec α y →
          (deriv^[ell] (fun θ => D.oddPart y θ - D.target α θ))
            (seedDerivativeAngle (seedN d) k) =
          (2 * (seedN d : ℝ)) ^ ell * ∑ j, v j * ((y j : ℝ) - D.fractional α j)

/-- Algebraic connection between the executable background word
and the even Laurent pieces. This is an exact evaluation identity and a
three-monomial tail bound; it contains no spectral lower bound. -/
structure FlatSeedCoefficientHypothesis (A : FlatSeedFrontend) {d : ℕ}
    (D : FlatSeedAnalyticData d) : Prop where
  evaluation : ∀ y : Fin (seedN d) → ℚ, (∀ j, y j = -1 ∨ y j = 1) → ∀ θ : ℝ,
    ∃ u tail : ℂ, ‖u‖ = 1 ∧ ‖tail‖ ≤ 3 ∧
      coeffEval (IdealCVP.ofList (d := d)
        (seedAssemble d (A.background d) (List.ofFn y)))
        (Complex.exp ((θ : ℂ) * Complex.I)) =
      u * ((1 + 2 * D.cosine θ : ℝ) +
        2 * Complex.I * ((D.evenPart θ + D.oddPart y θ : ℝ) : ℂ)) + tail

/-- Uniform semantic preprocessing obligation. No algorithm is selected
from these real witnesses; the three total rational routines belong to `A`.
The four obligations are listed separately and discharged by the concrete
frontend preparation certificate. -/
structure FlatSeedPreparationHypothesis (A : FlatSeedFrontend) : Prop where
  prepare : ∀ d, Dyadic d → 2 ^ 512 ≤ d →
    ∃ D : FlatSeedAnalyticData d,
      FlatSeedGeometryHypothesis A D ∧ FlatSeedIntervalRoundingHypothesis A D ∧
      FlatSeedDerivativeRoundingHypothesis D ∧ FlatSeedCoefficientHypothesis A D

/-- Derive the sampled jet estimate, including all rational approximation
losses, from the finite row identities and the full-coloring output. -/
theorem flatSeed_sample_jets {d : ℕ} {D : FlatSeedAnalyticData d}
    (hN : 1 ≤ seedN d) (hI : FlatSeedIntervalRoundingHypothesis A D)
    (hR : FlatSeedDerivativeRoundingHypothesis D)
    {α : Fin D.J → ℚ} {y : Fin (seedN d) → ℚ}
    (hα : D.FirstSpec α) (hy : D.SecondSpec α y)
    (k : Fin (16 * seedN d)) (ell : ℕ) (hell : ell ≤ seedN d) :
    |(deriv^[ell] (fun θ => D.oddPart y θ - D.target α θ))
      (seedDerivativeAngle (seedN d) k)| ≤
    (5281 + 240 * (ell : ℝ)) * Real.sqrt (seedN d) * (2 * (seedN d : ℝ)) ^ ell := by
  obtain ⟨i, v, hi, hv, hq, hid⟩ := hR.sample_rows α hα k ell hell
  have hd : coloringDiscrepancy (D.secondV α i) (D.secondX α) y ≤
      (5280 + 240 * (ell : ℝ)) * Real.sqrt (seedN d) * coloringRowSup (D.secondV α i) := by
    have hh := hy.2 i
    rw [hi] at hh
    push_cast at hh
    convert hh using 1
    ring
  have hh := seed_rounding_row_bound hN hell v (D.fractional α)
    (D.secondV α i) (D.secondX α) y hv hq (hI.second_cube α hα) hy.1
    (hR.starting_error α hα) hd
  rw [hid y hy, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ (2 * (seedN d : ℝ)) ^ ell)]
  have hm := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ (2 * (seedN d : ℝ)) ^ ell by positivity)
  nlinarith

/-- First-quadrant sample estimates extend to the full circle by the
explicit reflection identity. No infinite Taylor series is assumed. -/
theorem flatSeed_rounding_bound {d : ℕ} {D : FlatSeedAnalyticData d}
    (hN : 1 ≤ seedN d) (hG : FlatSeedGeometryHypothesis A D)
    (hI : FlatSeedIntervalRoundingHypothesis A D)
    (hR : FlatSeedDerivativeRoundingHypothesis D)
    {α : Fin D.J → ℚ} {y : Fin (seedN d) → ℚ}
    (hα : D.FirstSpec α) (hy : D.SecondSpec α y) (θ : ℝ) :
    |D.oddPart y θ - D.target α θ| ≤ 5900 * Real.sqrt (seedN d) := by
  obtain ⟨k, hk⟩ := seed_derivative_grid_covers (by omega : 0 < seedN d) (hG.fold_mem θ)
  rw [hR.error_reflect α y hα hy θ]
  exact (seed_taylor_nearby hN (hR.error_degree α y hα hy)
    (hR.error_global α y hα hy) hk (flatSeed_sample_jets hN hI hR hα hy k)).le

/-- All-circle semantic output of the actual two-coloring list program,
conditional on the explicitly named rational preparation obligations. -/
theorem seed_circle_lower (A : FlatSeedFrontend)
    (hA : FlatSeedPreparationHypothesis A)
    (hK : SineKernelDecompositionHypothesis)
    (F : PartialColoringInput → List ℚ) (hF : FullColoringCorrect F)
    {d : ℕ} (hd : Dyadic d) (hlarge : 2 ^ 512 ≤ d) (θ : ℝ) :
    (seedConstant : ℝ) * Real.sqrt d ≤
      ‖coeffEval (IdealCVP.ofList (d := d) (seed A F d))
        (Complex.exp ((θ : ℂ) * Complex.I))‖ := by
  obtain ⟨D, hG, hI, hR, hC⟩ := hA.prepare d hd hlarge
  obtain ⟨α, hαout, hα⟩ := hF D.J (seedIntervalRows (seedN d) D.J) D.firstV D.firstX D.firstC
    hG.first_cube hG.first_nonnegative hG.first_entropy
  obtain ⟨y, hyout, hy⟩ := hF (seedN d) (seedDerivativeRows d)
    (D.secondV α) (D.secondX α) (D.secondC α)
    (hI.second_cube α hα) (hI.second_nonnegative α hα) (hI.second_entropy α hα)
  have hword : seed A F d = seedAssemble d (A.background d) (List.ofFn y) := by
    simp only [seed, hG.interval_input, hαout, hI.coefficient_input α hα, hyout]
  rw [hword]
  obtain ⟨u, tail, hu, ht, he⟩ := hC.evaluation y hy.1 θ
  have hN : 2 ^ 20 ≤ seedN d := by
    have := (seed_degree_bounds hlarge).1
    omega
  apply (seed_final_margin hlarge).trans
  apply seed_core_lower (sb := D.target α θ) hu ht he (hG.even_bound θ)
  by_cases hbad : D.intervals.contains (D.foldAngle θ)
  · right
    constructor
    · have hsign : ∀ i, (α i : ℝ) = -1 ∨ (α i : ℝ) = 1 := by
        intro i
        rcases hα.1 i with hi | hi <;> simp [hi]
      have hk := sine_kernel_scaled_of_decomposition hK D.intervals
        (fun i => (α i : ℝ)) hN hsign (K := 9000) (by norm_num) (hG.fold_mem θ)
      rw [hI.kernel α hα θ]
      norm_num at hk
      simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9000)] using hk.2 hbad
    · exact flatSeed_rounding_bound (by omega) hG hI hR hα hy θ
  · exact Or.inl (hG.cosine_good θ hbad)

/-- The requested root-only spectral statement, with cutoff exponent 512. -/
theorem seed_spectral (A : FlatSeedFrontend) (hA : FlatSeedPreparationHypothesis A)
    (hK : SineKernelDecompositionHypothesis)
    (F : PartialColoringInput → List ℚ) (hF : FullColoringCorrect F)
    {d : ℕ} (hd : Dyadic d) (hlarge : 2 ^ 512 ≤ d) :
    SpectralSeed d (IdealCVP.ofList (d := d) (seed A F d)) := by
  refine ⟨seed_signs A F d, ?_⟩
  intro z hz
  have hone : ‖z‖ = 1 := by
    apply Complex.norm_eq_one_of_pow_eq_one (n := 2 * d) ?_ (by have := hd.pos; omega)
    rw [mul_comm 2 d, pow_mul, hz]
    norm_num
  obtain ⟨θ, rfl⟩ := (Complex.norm_eq_one_iff z).mp hone
  exact seed_circle_lower A hA hK F hF hd hlarge θ

/-- A fully explicit native-machine family composition. This theorem does
not assert any of the preprocessing contracts as an unconditional fact. -/
theorem spectralSeedFamily_of_fullColor (A : FlatSeedFrontend)
    (hA : FlatSeedPreparationHypothesis A) (hAt : FlatSeedFrontendRuntimeHypothesis A)
    (hK : SineKernelDecompositionHypothesis)
    (F : PartialColoringInput → List ℚ) (hF : FullColoringCorrect F)
    (hFt : ComputableTidilyInPolyTime F encPartialColoring (encList encColoringRational)) :
    SpectralSeedFamilyHypothesis := by
  refine ⟨512, seed A F, seed_polytime A hAt F hFt, ?_⟩
  intro d hd hlarge
  exact ⟨seed_length A F d, seed_spectral A hA hK F hF hd hlarge⟩

end Power2ModuleSVP
