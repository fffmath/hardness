import IdealCVP.ModuleSIVP

/-! # Rational targets, thresholds, and clearing denominators

The lattice remains integral; targets and squared thresholds may be rational.
Scaling changes the lattice as well as the target and squared threshold.
-/
noncomputable section
namespace IdealCVP

/-- Rational coefficient vectors of dimension `d`. -/
abbrev RatCoeff (d : ℕ) := Fin d → ℚ

/-- The squared Euclidean norm of a rational vector. -/
def ratSqNorm {ι : Type*} [Fintype ι] (v : ι → ℚ) : ℚ := ∑ i, v i ^ 2

/-- Embed an integral coefficient vector into the rational coefficient space. -/
def castCoeff {ι : Type*} (v : ι → ℤ) : ι → ℚ := fun i => v i

@[simp] theorem ratSqNorm_cast {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    ratSqNorm (castCoeff v) = (sqNorm v : ℚ) := by
  simp only [ratSqNorm, castCoeff, sqNorm, Int.cast_sum, Int.cast_pow]

theorem ratSqNorm_smul {ι : Type*} [Fintype ι] (a : ℚ) (v : ι → ℚ) :
    ratSqNorm (a • v) = a ^ 2 * ratSqNorm v := by
  simp only [ratSqNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- Exact decision CVP with rational target and rational squared threshold. -/
def RationalCVPYes {d : ℕ} (L : AddSubgroup (Coeff d)) (t : RatCoeff d) (Δ : ℚ) : Prop :=
  ∃ v ∈ L, ratSqNorm (castCoeff v - t) ≤ Δ

/-- Multiplication by a natural number, as an additive homomorphism. -/
def scaleCoeff (d N : ℕ) : Coeff d →+ Coeff d where
  toFun v := (N : ℤ) • v
  map_zero' := smul_zero _
  map_add' := smul_add _

/-- The lattice `N L`, with no implicit saturation. -/
def scaleLattice {d : ℕ} (N : ℕ) (L : AddSubgroup (Coeff d)) : AddSubgroup (Coeff d) :=
  L.map (scaleCoeff d N)

theorem castCoeff_scale {d : ℕ} (N : ℕ) (v : Coeff d) :
    castCoeff ((N : ℤ) • v) = (N : ℚ) • castCoeff v := by
  funext i
  simp only [castCoeff, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]

/-- Clearing denominators preserves the answer when all three data are scaled. -/
theorem rationalCVP_scale {d : ℕ} (L : AddSubgroup (Coeff d)) (t : RatCoeff d)
    (Δ : ℚ) (N : ℕ) (hN : 0 < N) :
    RationalCVPYes L t Δ ↔
      RationalCVPYes (scaleLattice N L) ((N : ℚ) • t) ((N : ℚ) ^ 2 * Δ) := by
  have hp : (0 : ℚ) < (N : ℚ) ^ 2 := by positivity
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨(N : ℤ) • v, ⟨v, hv, rfl⟩, ?_⟩
    rw [castCoeff_scale, ← smul_sub, ratSqNorm_smul]
    exact (mul_le_mul_iff_right₀ hp).mpr h
  · rintro ⟨w, ⟨v, hv, rfl⟩, h⟩
    refine ⟨v, hv, ?_⟩
    change ratSqNorm (castCoeff ((N : ℤ) • v) - (N : ℚ) • t) ≤ _ at h
    rw [castCoeff_scale, ← smul_sub, ratSqNorm_smul] at h
    exact (mul_le_mul_iff_right₀ hp).mp h

/-- The floor step is valid even for negative rational thresholds. -/
theorem sqNorm_le_floor {ι : Type*} [Fintype ι] (v : ι → ℤ) (x : ℚ) :
    (sqNorm v : ℚ) ≤ x ↔ sqNorm v ≤ ⌊x⌋ := Int.le_floor.symm

/-- For integral targets, a rational squared threshold is equivalent to its integer floor. -/
theorem rationalCVP_integral_target {d : ℕ} (L : AddSubgroup (Coeff d))
    (t : Coeff d) (Δ : ℚ) :
    RationalCVPYes L (castCoeff t) Δ ↔ CVPYes L t ⌊Δ⌋ := by
  have hc (v : Coeff d) : castCoeff v - castCoeff t = castCoeff (v - t) := by
    funext i
    simp only [castCoeff, Pi.sub_apply, Int.cast_sub]
  simp only [RationalCVPYes, CVPYes, hc, ratSqNorm_cast, Int.le_floor]

/-- An integral instance embeds into rational CVP without changing its answer. -/
theorem cvp_iff_rationalCVP {d : ℕ} (L : AddSubgroup (Coeff d)) (t : Coeff d) (Δ : ℤ) :
    CVPYes L t Δ ↔ RationalCVPYes L (castCoeff t) (Δ : ℚ) := by
  rw [rationalCVP_integral_target, Int.floor_intCast]

/-- A supplied common denominator gives an integral instance, using a floor. -/
theorem rationalCVP_clear_denominators {d : ℕ} (L : AddSubgroup (Coeff d))
    (t : RatCoeff d) (Δ : ℚ) (N : ℕ) (hN : 0 < N) (u : Coeff d)
    (hu : (N : ℚ) • t = castCoeff u) :
    RationalCVPYes L t Δ ↔ CVPYes (scaleLattice N L) u ⌊(N : ℚ) ^ 2 * Δ⌋ := by
  rw [rationalCVP_scale L t Δ N hN, hu, rationalCVP_integral_target]

/-- Every finite family of rational coefficients has a positive common denominator. -/
theorem exists_common_denominator {ι : Type*} [Finite ι] (t : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ u : ι → ℤ, (N : ℚ) • t = castCoeff u := by
  classical
  let := Fintype.ofFinite ι
  let N := ∏ i, (t i).den
  have hN : 0 < N := Finset.prod_pos fun i _ => (t i).den_pos
  have hd (i : ι) : (t i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  choose k hk using hd
  refine ⟨N, hN, (fun i => (k i : ℤ) * (t i).num), ?_⟩
  funext i
  change (N : ℚ) * t i = ((k i : ℤ) * (t i).num : ℤ)
  rw [hk i, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  have hden : ((t i).den : ℚ) * t i = (t i).num := by
    calc
      ((t i).den : ℚ) * t i = ((t i).den : ℚ) * ((t i).num / (t i).den) :=
        congrArg (fun x : ℚ => ((t i).den : ℚ) * x) (t i).num_div_den.symm
      _ = _ := by field_simp
  calc
    ((t i).den : ℚ) * (k i : ℚ) * t i = (k i : ℚ) * (((t i).den : ℚ) * t i) := by ring
    _ = _ := by rw [hden]

/-- The existing hardness reduction is also a rational-data reduction. -/
theorem x3c_correct_rational (I : X3CInstance) :
    I.HasExactCover ↔ RationalCVPYes (Cyclotomic.principalIdealLattice (x3cToCVP I).g)
      (castCoeff (x3cToCVP I).T) ((x3cToCVP I).Δ : ℚ) :=
  (x3c_correct I).trans (cvp_iff_rationalCVP _ _ _)

/-- The scaled lattice of a principal ideal is again the expected principal ideal. -/
theorem scaleLattice_principal {d : ℕ} (N : ℕ) (g : Cyclotomic.R d) :
    scaleLattice N (Cyclotomic.principalIdealLattice g) =
      Cyclotomic.principalIdealLattice ((N : ℤ) • g) := by
  ext w
  constructor
  · rintro ⟨v, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, Cyclotomic.mul_smul_left g a (N : ℤ)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Cyclotomic.mul g a, ⟨a, rfl⟩, (Cyclotomic.mul_smul_left g a (N : ℤ)).symm⟩

theorem ratSqNorm_residual {d : ℕ} (v t : Coeff d) :
    ratSqNorm (castCoeff v - castCoeff t) = (sqNorm (v - t) : ℚ) := by
  have he : castCoeff v - castCoeff t = castCoeff (v - t) := by
    funext i
    exact (Int.cast_sub _ _).symm
  rw [he, ratSqNorm_cast]

/-- The exact X3C yes-instance minimum persists under rational coefficient embedding. -/
theorem x3c_yes_gap_rational (I : X3CInstance) (hy : I.HasExactCover) :
    (∃ v ∈ Cyclotomic.principalIdealLattice (x3cToCVP I).g,
      ratSqNorm (castCoeff v - castCoeff (x3cToCVP I).T) = ((x3cToCVP I).Δ : ℚ)) ∧
    ∀ v ∈ Cyclotomic.principalIdealLattice (x3cToCVP I).g,
      ((x3cToCVP I).Δ : ℚ) ≤ ratSqNorm (castCoeff v - castCoeff (x3cToCVP I).T) := by
  obtain ⟨⟨v, hv, he⟩, hl⟩ := x3c_yes_gap I hy
  refine ⟨⟨v, hv, ?_⟩, ?_⟩
  · rw [ratSqNorm_residual, he]
  · intro w hw
    rw [ratSqNorm_residual]
    exact_mod_cast hl w hw

/-- The squared-distance gap of four persists under rational coefficient embedding. -/
theorem x3c_no_gap_rational (I : X3CInstance) (hn : ¬ I.HasExactCover) :
    ∀ v ∈ Cyclotomic.principalIdealLattice (x3cToCVP I).g,
      ((x3cToCVP I).Δ : ℚ) + 4 ≤ ratSqNorm (castCoeff v - castCoeff (x3cToCVP I).T) := by
  intro v hv
  rw [ratSqNorm_residual]
  exact_mod_cast x3c_no_gap I hn v hv

namespace ModuleSIVP
variable {d : ℕ} [Fact (∃ k, d = 2 ^ k)]

/-- Rational targets in the genuine field, represented in its monomial basis. -/
def RationalPrincipalCVPYes (g : Cyclotomic.QuotRing d) (T : K d) (Δ : ℚ) : Prop :=
  ∃ a : Cyclotomic.QuotRing d,
    ratSqNorm (rationalBasis.equivFun (scalarMap (g * a) - T)) ≤ Δ

/-- The coefficient target interpretation of rational principal ideal CVP. -/
theorem rationalPrincipalCVP_iff (g : Cyclotomic.R d) (T : K d) (Δ : ℚ) :
    RationalPrincipalCVPYes (Cyclotomic.toQuot g) T Δ ↔
      RationalCVPYes (Cyclotomic.principalIdealLattice g) (rationalBasis.equivFun T) Δ := by
  have he (v : Cyclotomic.R d) :
      rationalBasis.equivFun (scalarMap (Cyclotomic.toQuot v) - T) =
        castCoeff v - rationalBasis.equivFun T := by
    rw [map_sub, scalarMap_toQuot, LinearEquiv.apply_symm_apply]
    rfl
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, rfl⟩ := (Cyclotomic.toQuot_bijective dimension_pos).surjective a
    rw [← Cyclotomic.toQuot_mul dimension_pos, he] at ha
    exact ⟨Cyclotomic.mul g b, ⟨b, rfl⟩, ha⟩
  · rintro ⟨v, ⟨b, rfl⟩, hv⟩
    refine ⟨Cyclotomic.toQuot b, ?_⟩
    rw [← Cyclotomic.toQuot_mul dimension_pos, he]
    exact hv

/-- Principal rational CVP clears denominators into an integral principal ideal. -/
theorem rationalPrincipalCVP_clear_denominators (g : Cyclotomic.R d) (T : K d)
    (Δ : ℚ) (N : ℕ) (hN : 0 < N) (u : Coeff d)
    (hu : rationalBasis.equivFun ((N : ℚ) • T) = castCoeff u) :
    RationalPrincipalCVPYes (Cyclotomic.toQuot g) T Δ ↔
      CVPYes (Cyclotomic.principalIdealLattice ((N : ℤ) • g)) u ⌊(N : ℚ) ^ 2 * Δ⌋ := by
  rw [rationalPrincipalCVP_iff]
  rw [map_smul] at hu
  rw [rationalCVP_clear_denominators _ _ _ N hN u hu, scaleLattice_principal]

/-- Rational squared threshold on an integral module. -/
def RationalSecondMinimumSq
    (M : Submodule (Cyclotomic.QuotRing d) (Cyclotomic.QuotRing d × Cyclotomic.QuotRing d))
    (Γ : ℚ) : Prop :=
  ∃ u ∈ M, ∃ v ∈ M, Independent u v ∧
    (vectorNormSq u : ℚ) ≤ Γ ∧ (vectorNormSq v : ℚ) ≤ Γ

/-- A rational squared module threshold is equivalent to its integer floor. -/
theorem rationalSecondMinimumSq_iff (M : Submodule (Cyclotomic.QuotRing d)
    (Cyclotomic.QuotRing d × Cyclotomic.QuotRing d)) (Γ : ℚ) :
    RationalSecondMinimumSq M Γ ↔ SecondMinimumSq M ⌊Γ⌋ := by
  simp only [RationalSecondMinimumSq, SecondMinimumSq, Int.le_floor]

/-- Coefficient squared norm on arbitrary rational field vectors. -/
def fieldNormSq (v : K d × K d) : ℚ :=
  ratSqNorm (rationalBasis.equivFun v.1) + ratSqNorm (rationalBasis.equivFun v.2)

theorem fieldNormSq_scale (a : ℚ) (v : K d × K d) :
    fieldNormSq (a • v) = a ^ 2 * fieldNormSq v := by
  simp only [fieldNormSq, Prod.smul_fst, Prod.smul_snd, map_smul, ratSqNorm_smul]
  ring

/-- The module generated by two rational vectors, with integral ring coefficients. -/
def InRationalModule (b₁ b₂ v : K d × K d) : Prop :=
  ∃ a b : Cyclotomic.QuotRing d, v = scalarMap a • b₁ + scalarMap b • b₂

/-- Decision module-SIVP for arbitrary rational basis vectors. -/
def RationalBasisSIVPYes (b₁ b₂ : K d × K d) (Γ : ℚ) : Prop :=
  ∃ u v, InRationalModule b₁ b₂ u ∧ InRationalModule b₁ b₂ v ∧
    LinearIndependent (K d) ![u, v] ∧ fieldNormSq u ≤ Γ ∧ fieldNormSq v ≤ Γ

/-- Scaling both rational basis vectors scales the entire module and its squared norms;
field-linear independence is preserved. -/
theorem rationalBasisSIVP_scale (b₁ b₂ : K d × K d) (Γ : ℚ)
    (N : ℕ) (hN : 0 < N) :
    RationalBasisSIVPYes b₁ b₂ Γ ↔
      RationalBasisSIVPYes ((N : ℚ) • b₁) ((N : ℚ) • b₂) ((N : ℚ) ^ 2 * Γ) := by
  have hn : (N : ℚ) ≠ 0 := by positivity
  have hp : (0 : ℚ) < (N : ℚ) ^ 2 := by positivity
  have hm (u : K d × K d) : InRationalModule b₁ b₂ u →
      InRationalModule ((N : ℚ) • b₁) ((N : ℚ) • b₂) ((N : ℚ) • u) := by
    rintro ⟨a, b, rfl⟩
    refine ⟨a, b, ?_⟩
    rw [smul_add, smul_comm (N : ℚ) (scalarMap a), smul_comm (N : ℚ) (scalarMap b)]
  have hback (w : K d × K d)
      (hw : InRationalModule ((N : ℚ) • b₁) ((N : ℚ) • b₂) w) :
      ∃ u, InRationalModule b₁ b₂ u ∧ w = (N : ℚ) • u := by
    obtain ⟨a, b, rfl⟩ := hw
    exact ⟨scalarMap a • b₁ + scalarMap b • b₂, ⟨a, b, rfl⟩,
      by rw [smul_add, smul_comm (N : ℚ) (scalarMap a), smul_comm (N : ℚ) (scalarMap b)]⟩
  constructor
  · rintro ⟨u, v, hu, hv, hi, h₁, h₂⟩
    exact ⟨(N : ℚ) • u, (N : ℚ) • v, hm u hu, hm v hv,
      (LinearIndependent.pair_smul_iff hn).mpr hi,
      (fieldNormSq_scale _ _).trans_le ((mul_le_mul_iff_right₀ hp).mpr h₁),
      (fieldNormSq_scale _ _).trans_le ((mul_le_mul_iff_right₀ hp).mpr h₂)⟩
  · rintro ⟨w, z, hw, hz, hi, h₁, h₂⟩
    obtain ⟨u, hu, rfl⟩ := hback w hw
    obtain ⟨v, hv, rfl⟩ := hback z hz
    rw [fieldNormSq_scale] at h₁ h₂
    exact ⟨u, v, hu, hv, (LinearIndependent.pair_smul_iff hn).mp hi,
      (mul_le_mul_iff_right₀ hp).mp h₁, (mul_le_mul_iff_right₀ hp).mp h₂⟩

/-- Every pair of rational module generators can simultaneously be made integral. -/
theorem exists_integral_scaled_basis (b₁ b₂ : K d × K d) :
    ∃ N : ℕ, 0 < N ∧ ∃ a₁ a₂ : Cyclotomic.QuotRing d × Cyclotomic.QuotRing d,
      (N : ℚ) • b₁ = fieldVector a₁ ∧ (N : ℚ) • b₂ = fieldVector a₂ := by
  let coeff : (Fin d ⊕ Fin d) ⊕ (Fin d ⊕ Fin d) → ℚ :=
    Sum.elim (Sum.elim (rationalBasis.equivFun b₁.1) (rationalBasis.equivFun b₁.2))
      (Sum.elim (rationalBasis.equivFun b₂.1) (rationalBasis.equivFun b₂.2))
  obtain ⟨N, hN, u, hu⟩ := exists_common_denominator coeff
  have hc (j) := congrFun hu j
  let a₁ := (Cyclotomic.toQuot (fun i => u (.inl (.inl i))),
    Cyclotomic.toQuot (fun i => u (.inl (.inr i))))
  let a₂ := (Cyclotomic.toQuot (fun i => u (.inr (.inl i))),
    Cyclotomic.toQuot (fun i => u (.inr (.inr i))))
  refine ⟨N, hN, a₁, a₂, ?_, ?_⟩ <;> apply Prod.ext <;>
    apply rationalBasis.equivFun.injective <;>
    simp only [Prod.smul_fst, Prod.smul_snd, fieldVector, a₁, a₂,
      scalarMap_toQuot, LinearEquiv.apply_symm_apply, map_smul] <;> funext i
  · exact hc (.inl (.inl i))
  · exact hc (.inl (.inr i))
  · exact hc (.inr (.inl i))
  · exact hc (.inr (.inr i))

/-- Rational coefficient norms restrict to the existing integral module norms. -/
theorem fieldNormSq_fieldVector (u : Cyclotomic.QuotRing d × Cyclotomic.QuotRing d) :
    fieldNormSq (fieldVector u) = (vectorNormSq u : ℚ) := by
  obtain ⟨a, ha⟩ := (Cyclotomic.toQuot_bijective dimension_pos).surjective u.1
  obtain ⟨b, hb⟩ := (Cyclotomic.toQuot_bijective dimension_pos).surjective u.2
  rcases u with ⟨u₁, u₂⟩
  dsimp only at ha hb
  subst u₁ u₂
  simp only [fieldNormSq, fieldVector, scalarMap_toQuot, LinearEquiv.apply_symm_apply,
    vectorNormSq, normSq_toQuot, ratSqNorm, sqNorm, Int.cast_add, Int.cast_sum, Int.cast_pow]

theorem fieldVector_combination (a b : Cyclotomic.QuotRing d)
    (u v : Cyclotomic.QuotRing d × Cyclotomic.QuotRing d) :
    fieldVector (a • u + b • v) = scalarMap a • fieldVector u + scalarMap b • fieldVector v := by
  ext <;> simp [fieldVector, smul_eq_mul]

/-- The module generated by embedded integral vectors is exactly the embedded integral span. -/
theorem inRationalModule_integral_iff (b₁ b₂ : Cyclotomic.QuotRing d × Cyclotomic.QuotRing d)
    (w : K d × K d) :
    InRationalModule (fieldVector b₁) (fieldVector b₂) w ↔
      ∃ u ∈ Submodule.span (Cyclotomic.QuotRing d) ({b₁, b₂} : Set _), fieldVector u = w := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a • b₁ + b • b₂, Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩,
      fieldVector_combination a b b₁ b₂⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
    exact ⟨a, b, fieldVector_combination a b b₁ b₂⟩

/-- Integral generators give precisely integral module-SIVP, with the floor threshold. -/
theorem rationalBasisSIVP_integral_iff (b₁ b₂ : Cyclotomic.QuotRing d × Cyclotomic.QuotRing d)
    (Γ : ℚ) :
    RationalBasisSIVPYes (fieldVector b₁) (fieldVector b₂) Γ ↔
      SecondMinimumSq (Submodule.span (Cyclotomic.QuotRing d) ({b₁, b₂} : Set _)) ⌊Γ⌋ := by
  constructor
  · rintro ⟨w, z, hw, hz, hi, h₁, h₂⟩
    obtain ⟨u, hu, rfl⟩ := (inRationalModule_integral_iff _ _ _).mp hw
    obtain ⟨v, hv, rfl⟩ := (inRationalModule_integral_iff _ _ _).mp hz
    rw [fieldNormSq_fieldVector] at h₁ h₂
    exact ⟨u, hu, v, hv, hi, Int.le_floor.mpr h₁, Int.le_floor.mpr h₂⟩
  · rintro ⟨u, hu, v, hv, hi, h₁, h₂⟩
    refine ⟨fieldVector u, fieldVector v,
      (inRationalModule_integral_iff _ _ _).mpr ⟨u, hu, rfl⟩,
      (inRationalModule_integral_iff _ _ _).mpr ⟨v, hv, rfl⟩, hi, ?_, ?_⟩ <;>
      rw [fieldNormSq_fieldVector]
    · exact Int.le_floor.mp h₁
    · exact Int.le_floor.mp h₂

/-- Arbitrary rational rank-two generators reduce to an integral module with
squared threshold `floor (N² Γ)`. Their field-linear independence is preserved. -/
theorem rationalBasisSIVP_clear_denominators (b₁ b₂ : K d × K d) (Γ : ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ a₁ a₂ : Cyclotomic.QuotRing d × Cyclotomic.QuotRing d,
      (N : ℚ) • b₁ = fieldVector a₁ ∧ (N : ℚ) • b₂ = fieldVector a₂ ∧
      (Independent a₁ a₂ ↔ LinearIndependent (K d) ![b₁, b₂]) ∧
      (RationalBasisSIVPYes b₁ b₂ Γ ↔
        SecondMinimumSq (Submodule.span (Cyclotomic.QuotRing d) ({a₁, a₂} : Set _))
          ⌊(N : ℚ) ^ 2 * Γ⌋) := by
  obtain ⟨N, hN, a₁, a₂, h₁, h₂⟩ := exists_integral_scaled_basis b₁ b₂
  refine ⟨N, hN, a₁, a₂, h₁, h₂, ?_, ?_⟩
  · change LinearIndependent (K d) ![fieldVector a₁, fieldVector a₂] ↔ _
    rw [← h₁, ← h₂]
    exact LinearIndependent.pair_smul_iff (by positivity : (N : ℚ) ≠ 0)
  · rw [rationalBasisSIVP_scale b₁ b₂ Γ N hN, h₁, h₂, rationalBasisSIVP_integral_iff]

end ModuleSIVP
/-- The rational target may equivalently be an element of the genuine quotient field. -/
theorem x3c_correct_rational_principal (I : X3CInstance) :
    let C := x3cToCVP I
    letI : Fact (∃ k, C.d = 2 ^ k) := ⟨C.power_two⟩
    I.HasExactCover ↔ ModuleSIVP.RationalPrincipalCVPYes (Cyclotomic.toQuot C.g)
      (ModuleSIVP.scalarMap (Cyclotomic.toQuot C.T)) (C.Δ : ℚ) := by
  let : Fact (∃ k, (x3cToCVP I).d = 2 ^ k) := ⟨(x3cToCVP I).power_two⟩
  change I.HasExactCover ↔ ModuleSIVP.RationalPrincipalCVPYes _ _ _
  rw [ModuleSIVP.rationalPrincipalCVP_iff, ModuleSIVP.scalarMap_toQuot,
    LinearEquiv.apply_symm_apply]
  exact x3c_correct_rational I

/-- The module reduction also accepts a rational squared threshold. -/
theorem x3c_module_sivp_correct_rational (I : X3CInstance) :
    let J := x3cToModuleSIVP I
    letI : Fact (∃ k, J.d = 2 ^ k) := ⟨J.power_two⟩
    I.HasExactCover ↔ ModuleSIVP.RationalSecondMinimumSq J.module (J.Γ : ℚ) := by
  let : Fact (∃ k, (x3cToModuleSIVP I).d = 2 ^ k) := ⟨(x3cToModuleSIVP I).power_two⟩
  change I.HasExactCover ↔ ModuleSIVP.RationalSecondMinimumSq (x3cToModuleSIVP I).module _
  rw [ModuleSIVP.rationalSecondMinimumSq_iff, Int.floor_intCast]
  exact x3c_module_sivp_correct I

end IdealCVP
