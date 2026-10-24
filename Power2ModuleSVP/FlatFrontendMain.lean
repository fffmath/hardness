import Power2ModuleSVP.FlatFrontendInputs
import Power2ModuleSVP.FlatFrontendDerivatives
import Power2ModuleSVP.FlatFrontendEnclosures
import Power2ModuleSVP.SineKernelProof

/-!
Preparation contracts for the concrete frontend. The interval-coloring
contract and Laurent coefficient contract are proved below. The remaining
geometric certificate and quantitative rational enclosure estimates are
named separately; they are not asserted to hold here.
-/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators
noncomputable section

def intervalCount (d : ℕ) : ℕ := (intervals (seedN d)).length

def fractional {d : ℕ} (I : SeedKernelIntervals (seedN d) (intervalCount d))
    (α : Fin (intervalCount d) → ℚ) (j : Fin (seedN d)) : ℝ :=
  9000 * Real.sqrt (seedN d) * I.sineCoefficient (fun i => (α i : ℝ)) j

def analyticData (d : ℕ) (I : SeedKernelIntervals (seedN d) (intervalCount d)) :
    FlatSeedAnalyticData d where
  J := intervalCount d
  intervals := I
  foldAngle := foldAngle
  cosine := cosine d
  evenPart := evenPart d
  firstV := inputMatrix (intervalInput d)
  firstX := inputStart (intervalInput d)
  firstC := inputThreshold (intervalInput d)
  target := fun α θ => 9000 * Real.sqrt (seedN d) * I.transform (fun i => (α i : ℝ)) θ
  fractional := fractional I
  secondV := fun α => inputMatrix (coefficientInput (d, List.ofFn α))
  secondX := fun α => inputStart (coefficientInput (d, List.ofFn α))
  secondC := fun α => inputThreshold (coefficientInput (d, List.ofFn α))
  oddPart := oddPart

theorem target_eq_oddSineSum {d : ℕ}
    (I : SeedKernelIntervals (seedN d) (intervalCount d)) (α : Fin (intervalCount d) → ℚ) :
    (analyticData d I).target α = oddSineSum (fractional I α) := by
  funext θ
  simp only [analyticData, SeedKernelIntervals.transform_eq_sine_sum, Finset.mul_sum,
    oddSineSum, fractional]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- This entire original contract holds for the concrete frontend. Clipping
the recomputed starting point makes its cube premise unconditional. -/
theorem interval_contract {d : ℕ}
    (I : SeedKernelIntervals (seedN d) (intervalCount d)) :
    FlatSeedIntervalRoundingHypothesis flatFrontend (analyticData d I) := by
  constructor
  · intro α _ θ
    dsimp only [analyticData]
    simp only [abs_mul]
    rw [foldAngle_preserves (I.abs_transform_periodic (fun i => (α i : ℝ)))
        (I.transform_pi_sub (fun i => (α i : ℝ))) θ]
  · intro α _
    exact input_pack (coefficientInput_shape (d, List.ofFn α))
  · intro α _
    exact second_cube (d, List.ofFn α)
  · intro α _
    exact second_threshold_nonnegative (d, List.ofFn α)
  · intro α _
    exact second_entropy (d, List.ofFn α)

theorem coefficient_contract {d : ℕ}
    (I : SeedKernelIntervals (seedN d) (intervalCount d))
    (hshape : d = 4 * seedN d + 4) :
    FlatSeedCoefficientHypothesis flatFrontend (analyticData d I) := by
  constructor
  intro y hy θ
  have he := assembled_evaluation (seedN d) y hy θ
  rw [← hshape] at he
  exact he

theorem dyadic_shape {d : ℕ} (hd : Dyadic d) (hlarge : 4 ≤ d) : d = 4 * seedN d + 4 := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 2 ≤ k := by
    by_contra h
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> norm_num at hlarge
  have hp : 2 ^ k = 4 * 2 ^ (k - 2) := by
    conv_lhs => rw [show k = 2 + (k - 2) by omega, pow_add]
    norm_num
  unfold seedN
  rw [hp]
  omega

theorem coefficient_contract_dyadic {d : ℕ}
    (I : SeedKernelIntervals (seedN d) (intervalCount d)) (hd : Dyadic d) (hlarge : 4 ≤ d) :
    FlatSeedCoefficientHypothesis flatFrontend (analyticData d I) :=
  coefficient_contract I (dyadic_shape hd hlarge)

/-- Still-open verification of the actual marked runs. Endpoints must be
the output of `scanCells`, rather than unrelated real intervals. The other
three fields are precisely the geometry still needed by the assembly. -/
structure GeometryCertificate (d : ℕ) where
  kernelIntervals : SeedKernelIntervals (seedN d) (intervalCount d)
  left_eq : ∀ i, kernelIntervals.left i = ((intervals (seedN d)).getD i (0, 0)).1
  right_eq : ∀ i, kernelIntervals.right i = ((intervals (seedN d)).getD i (0, 0)).2
  count : intervalCount d * 2 ^ 66 ≤ seedN d
  cosine_good : ∀ θ, ¬ kernelIntervals.contains (foldAngle θ) →
    seedCosineMargin * Real.sqrt (seedN d) ≤ |cosine d θ|
  even_bound : ∀ θ, |evenPart d θ| ≤ 6 * Real.sqrt (seedN d)

theorem geometry_contract {d : ℕ} (G : GeometryCertificate d) :
    FlatSeedGeometryHypothesis flatFrontend (analyticData d G.kernelIntervals) := by
  exact ⟨input_pack (intervalInput_shape d), first_cube d, first_threshold_nonnegative d,
    first_entropy d, G.count, foldAngle_mem, G.cosine_good, G.even_bound⟩

/-- Quantitative obligations left for the selected finite precisions.
These are actual entry/start enclosures and the first-coloring coefficient
bound; no derivative, discrepancy, or final seed bound is postulated. -/
structure EnclosureHypothesis {d : ℕ}
    (I : SeedKernelIntervals (seedN d) (intervalCount d)) : Prop where
  fractional_bound : ∀ α, (analyticData d I).FirstSpec α → ∀ j,
    |fractional I α j| ≤ 3 / 4
  fractional_error : ∀ α, (analyticData d I).FirstSpec α → ∀ j : Fin (seedN d),
    |(fractionalCoefficient (seedN d) (intervals (seedN d)) (List.ofFn α) j : ℝ) -
      fractional I α j| ≤ (seedRoundingError (seedN d) : ℝ)
  derivative_error : ∀ k : Fin (16 * seedN d), ∀ ell ≤ seedN d, ∀ j : Fin (seedN d),
    |derivativeRow (seedN d) k ell j - (derivativeEntry (seedN d) k ell j : ℝ)| ≤
      (seedRoundingError (seedN d) : ℝ)

theorem derivative_contract {d : ℕ}
    (I : SeedKernelIntervals (seedN d) (intervalCount d)) (hN : 0 < seedN d)
    (hE : EnclosureHypothesis I) :
    FlatSeedDerivativeRoundingHypothesis (analyticData d I) := by
  constructor
  · intro α y _ _
    change HasTrigDegree (2 * seedN d) (fun θ => oddPart y θ - (analyticData d I).target α θ)
    rw [oddPart_eq, target_eq_oddSineSum I α, oddSineSum_sub]
    exact oddSineSum_degree _
  · intro α y hα hy θ
    change |oddPart y θ - (analyticData d I).target α θ| ≤ _
    rw [oddPart_eq, target_eq_oddSineSum I α]
    have he := congrFun (oddSineSum_sub (fun j => (y j : ℝ)) (fractional I α)) θ
    rw [he]
    have hb : ∀ j, |(y j : ℝ) - fractional I α j| ≤ 2 := by
      intro j
      have hyj : |(y j : ℝ)| = 1 := by rcases hy.1 j with h | h <;> simp [h]
      have hh := abs_sub (y j : ℝ) (fractional I α j)
      linarith [hE.fractional_bound α hα j]
    simpa [mul_comm] using oddSineSum_bound hb θ
  · intro α y _ _ θ
    change |oddPart y θ - (analyticData d I).target α θ| =
      |oddPart y (foldAngle θ) - (analyticData d I).target α (foldAngle θ)|
    rw [oddPart_eq, target_eq_oddSineSum I α]
    simp_rw [congrFun (oddSineSum_sub (fun j => (y j : ℝ)) (fractional I α))]
    exact oddSineSum_fold _ θ
  · intro α hα j
    change |(inputStart (coefficientInput (d, List.ofFn α)) j : ℝ) - fractional I α j| ≤ _
    rw [second_start]
    apply clamp_error ?_ (hE.fractional_error α hα j)
    have hh := hE.fractional_bound α hα j
    rcases abs_le.mp hh with ⟨hl, hu⟩
    norm_num
    constructor <;> linarith
  · intro α _ k ell hell
    let n := seedN d
    let i : Fin (seedDerivativeRows d) := ⟨k.val + 16 * n * ell, by
      have hmul := Nat.mul_le_mul_left (16 * n) hell
      have hk := k.isLt
      change k.val + 16 * n * ell < 16 * n * (n + 1)
      dsimp [n] at *
      nlinarith⟩
    have hp : 0 < 16 * n := by dsimp [n]; omega
    have hid : i.val / (16 * n) = ell := by
      change (k.val + 16 * n * ell) / (16 * n) = ell
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt k.isLt, zero_add]
    have him : i.val % (16 * n) = k.val := by
      change (k.val + 16 * n * ell) % (16 * n) = k.val
      have hk : k.val < 16 * n := k.isLt
      simp [Nat.add_mod, Nat.mod_eq_of_lt hk]
    refine ⟨i, derivativeRow n k ell, ?_, derivativeRow_bound hN k ell, ?_, ?_⟩
    · change inputThreshold (coefficientInput (d, List.ofFn α)) i = _
      rw [second_threshold, hid]
    · intro j
      change |derivativeRow n k ell j -
        (inputMatrix (coefficientInput (d, List.ofFn α)) i j : ℝ)| ≤ _
      rw [second_matrix, hid, him]
      exact hE.derivative_error k ell hell j
    · intro y _
      change (deriv^[ell] (fun θ => oddPart y θ - (analyticData d I).target α θ))
        (seedDerivativeAngle n k) = _
      rw [oddPart_eq, target_eq_oddSineSum I α]
      exact derivativeRow_identity hN (fun j => (y j : ℝ)) (fractional I α) k ell

/-- Explicit residual boundary for this implementation. No inhabitant of
this structure, and no unconditional preparation theorem, is claimed. -/
structure PreparationHypothesis : Prop where
  certificates : ∀ d, Dyadic d → 2 ^ 512 ≤ d →
    ∃ G : GeometryCertificate d, EnclosureHypothesis G.kernelIntervals

theorem preparation_of (h : PreparationHypothesis) :
    FlatSeedPreparationHypothesis flatFrontend := by
  constructor
  intro d hd hlarge
  obtain ⟨G, hE⟩ := h.certificates d hd hlarge
  have hN : 0 < seedN d := by have := (seed_degree_bounds hlarge).1; omega
  have hfour : 4 ≤ d := by have := (seed_degree_bounds hlarge).1; unfold seedN at this; omega
  exact ⟨analyticData d G.kernelIntervals, geometry_contract G,
    interval_contract G.kernelIntervals, derivative_contract G.kernelIntervals hN hE,
    coefficient_contract_dyadic G.kernelIntervals hd hfour⟩

end
end FlatFrontend
end Power2ModuleSVP
