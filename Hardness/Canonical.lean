import Hardness.Rational
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Data.Int.Lemmas

/-! # Canonical embeddings of the negacyclic quotient

Fourier orthogonality proves the factor `d` between squared canonical and
coefficient norms. The embeddings are ring homomorphisms on the actual quotients.
-/
noncomputable section
namespace Hardness.Canonical
open scoped ComplexConjugate
open Hardness

/-- The specified primitive `2d`-th root of unity. -/
def zeta (d : ℕ) : ℂ := Complex.exp (Real.pi * Complex.I / (d : ℂ))

theorem zeta_primitive {d : ℕ} (hd : 0 < d) : IsPrimitiveRoot (zeta d) (2 * d) := by
  have hn : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : zeta d = Complex.exp (2 * Real.pi * Complex.I / (2 * d : ℕ)) := by
    unfold zeta
    congr 1
    push_cast
    field_simp
  rw [he]
  exact Complex.isPrimitiveRoot_exp _ (by omega)

theorem zeta_sq_primitive {d : ℕ} (hd : 0 < d) : IsPrimitiveRoot (zeta d ^ 2) d := by
  have h := (zeta_primitive hd).pow_of_dvd (by decide : 2 ≠ 0) (dvd_mul_right 2 d)
  simpa using h

theorem zeta_ne_zero {d : ℕ} (hd : 0 < d) : zeta d ≠ 0 :=
  (zeta_primitive hd).ne_zero (by omega)

theorem zeta_norm {d : ℕ} (hd : 0 < d) : ‖zeta d‖ = 1 :=
  (zeta_primitive hd).norm'_eq_one (by omega)

/-- Signed-exponent Fourier orthogonality, including both signs of `r-s`. -/
theorem odd_orthogonality {d : ℕ} (hd : 0 < d) (r s : Fin d) :
    (∑ k : Fin d, zeta d ^ (((2 * k.val + 1 : ℕ) : ℤ) * (r.val - (s.val : ℤ)))) =
      if r = s then (d : ℂ) else 0 := by
  classical
  by_cases hrs : r = s
  · subst s
    simp only [sub_self, mul_zero, zpow_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ite_true]
  · rw [if_neg hrs]
    let a : ℤ := (r.val : ℤ) - s.val
    let q : ℂ := (zeta d ^ 2) ^ a
    have hz := zeta_ne_zero hd
    have hq : q ≠ 1 := by
      intro h
      have hdiv := ((zeta_sq_primitive hd).zpow_eq_one_iff_dvd a).mp h
      have ha : a = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv (by
        rw [Int.natAbs_lt_iff_sq_lt]
        have hlo : -(d : ℤ) < a := by dsimp [a]; omega
        have hhi : a < (d : ℤ) := by dsimp [a]; omega
        nlinarith)
      apply hrs
      apply Fin.ext
      dsimp [a] at ha
      omega
    have hqd : q ^ d = 1 := by
      dsimp [q]
      rw [← zpow_natCast, ← zpow_mul]
      rw [mul_comm a, zpow_mul, zpow_natCast, (zeta_sq_primitive hd).pow_eq_one, one_zpow]
    have hsum : (∑ k : Fin d, q ^ k.val) = 0 := by
      rw [Fin.sum_univ_eq_sum_range]
      have hh := geom_sum_mul q d
      rw [hqd, sub_self] at hh
      exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hq)
    have he (k : Fin d) :
        zeta d ^ (((2 * k.val + 1 : ℕ) : ℤ) * a) = zeta d ^ a * q ^ k.val := by
      dsimp [q]
      rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast (zeta d) 2, ← zpow_mul,
        ← zpow_add₀ hz]
      congr 1
      push_cast
      ring
    change (∑ k : Fin d, zeta d ^ (((2 * k.val + 1 : ℕ) : ℤ) * a)) = 0
    simp_rw [he]
    rw [← Finset.mul_sum, hsum, mul_zero]

/-- Evaluation of the degree-<d coefficient representative at the kth odd root. -/
def sigma {d : ℕ} (c : Fin d → ℝ) (k : Fin d) : ℂ :=
  ∑ r, (c r : ℂ) * zeta d ^ ((2 * k.val + 1) * r.val)

/-- Character-product form of orthogonality. -/
theorem character_orthogonality {d : ℕ} (hd : 0 < d) (r s : Fin d) :
    (∑ k : Fin d, zeta d ^ ((2 * k.val + 1) * r.val) *
      conj (zeta d ^ ((2 * k.val + 1) * s.val))) =
      if r = s then (d : ℂ) else 0 := by
  have he (k : Fin d) :
      zeta d ^ ((2 * k.val + 1) * r.val) * conj (zeta d ^ ((2 * k.val + 1) * s.val)) =
        zeta d ^ (((2 * k.val + 1 : ℕ) : ℤ) * (r.val - (s.val : ℤ))) := by
    rw [map_pow, ← Complex.inv_eq_conj (zeta_norm hd), inv_pow,
      ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (zeta_ne_zero hd)]
    congr 1
    push_cast
    ring
  simp_rw [he]
  exact odd_orthogonality hd r s

/-- Paper `lem:canonical`, for arbitrary real coefficients (hence also ℚ and ℤ). -/
theorem norm_identity {d : ℕ} (hd : 0 < d) (c : Fin d → ℝ) :
    (∑ k, ‖sigma c k‖ ^ 2) = (d : ℝ) * ∑ r, c r ^ 2 := by
  classical
  have hexpand (k : Fin d) : sigma c k * conj (sigma c k) =
      ∑ r, ∑ s, (c r : ℂ) * (c s : ℂ) *
        (zeta d ^ ((2*k.val+1)*r.val) * conj (zeta d ^ ((2*k.val+1)*s.val))) := by
    simp only [sigma, map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  have h : (∑ k, sigma c k * conj (sigma c k)) =
      (d : ℂ) * ∑ r, (c r : ℂ)^2 := by
    calc
      _ = ∑ r, ∑ s, (c r : ℂ) * (c s : ℂ) *
          (∑ k : Fin d, zeta d ^ ((2*k.val+1)*r.val) *
            conj (zeta d ^ ((2*k.val+1)*s.val))) := by
        simp_rw [hexpand]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
      _ = _ := by
        simp_rw [character_orthogonality hd]
        simp [mul_ite, Finset.mul_sum, pow_two, mul_assoc, mul_comm]
  simp_rw [Complex.mul_conj'] at h
  exact_mod_cast h

/-- Each odd power is a root of the defining polynomial. -/
theorem zeta_pow_dimension {d : ℕ} (hd : 0 < d) : zeta d ^ d = -1 := by
  have hs : (zeta d ^ d)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm d 2]
    exact (zeta_primitive hd).pow_eq_one
  exact (sq_eq_one_iff.mp hs).resolve_left
    ((zeta_primitive hd).pow_ne_one_of_pos_of_lt hd.ne' (by omega))

theorem odd_root {d : ℕ} (hd : 0 < d) (k : Fin d) :
    (zeta d ^ (2 * k.val + 1)) ^ d = -1 := by
  rw [← pow_mul, Nat.mul_comm _ d, pow_mul, zeta_pow_dimension hd]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]

/-- Canonical evaluation on the genuine integral quotient. -/
def integralEmbedding {d : ℕ} (hd : 0 < d) (k : Fin d) :
    Cyclotomic.QuotRing d →+* ℂ :=
  AdjoinRoot.lift (Int.castRingHom ℂ) (zeta d ^ (2 * k.val + 1))
    (by simp only [Cyclotomic.modulus, Polynomial.eval₂_add, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_one, odd_root hd k, neg_add_cancel])

/-- Canonical evaluation on the genuine rational quotient. -/
def rationalEmbedding {d : ℕ} (hd : 0 < d) (k : Fin d) :
    ModuleSIVP.K d →+* ℂ :=
  AdjoinRoot.lift (Rat.castHom ℂ) (zeta d ^ (2 * k.val + 1))
    (by simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_one, odd_root hd k, neg_add_cancel])

/-- The representative-based sum agrees with evaluation modulo `X^d+1`. -/
theorem integralEmbedding_toQuot {d : ℕ} (hd : 0 < d) (k : Fin d) (c : Coeff d) :
    integralEmbedding hd k (Cyclotomic.toQuot c) = sigma (fun i => (c i : ℝ)) k := by
  simp [Cyclotomic.toQuot, integralEmbedding, sigma, ← pow_mul]

/-- Evaluation on a polynomial class is `Polynomial.aeval`, so it descends modulo the modulus. -/
theorem integralEmbedding_mk {d : ℕ} (hd : 0 < d) (k : Fin d) (p : Polynomial ℤ) :
    integralEmbedding hd k (AdjoinRoot.mk (Cyclotomic.modulus d) p) =
      Polynomial.aeval (zeta d ^ (2*k.val+1)) p := by
  rfl

theorem rationalEmbedding_mk {d : ℕ} (hd : 0 < d) (k : Fin d) (p : Polynomial ℚ) :
    rationalEmbedding hd k (AdjoinRoot.mk ((Polynomial.X : Polynomial ℚ)^d+1) p) =
      Polynomial.aeval (zeta d ^ (2*k.val+1)) p := by
  rfl

/-- In particular the embedding is multiplicative on coefficient representatives. -/
theorem sigma_mul {d : ℕ} (hd : 0 < d) (c b : Coeff d) (k : Fin d) :
    sigma (fun i => (Cyclotomic.mul c b i : ℝ)) k =
      sigma (fun i => (c i : ℝ)) k * sigma (fun i => (b i : ℝ)) k := by
  rw [← integralEmbedding_toQuot hd, Cyclotomic.toQuot_mul hd, map_mul,
    integralEmbedding_toQuot, integralEmbedding_toQuot]

/-- The rational quotient evaluation agrees with its unique monomial representative. -/
theorem rationalEmbedding_eq_sigma {d : ℕ} [Fact (∃ k, d = 2 ^ k)]
    (hd : 0 < d) (k : Fin d) (f : ModuleSIVP.K d) :
    rationalEmbedding hd k f =
      sigma (fun i => (ModuleSIVP.rationalBasis.equivFun f i : ℝ)) k := by
  have he (c : RatCoeff d) :
      rationalEmbedding hd k (ModuleSIVP.rationalBasis.equivFun.symm c) =
        sigma (fun i => (c i : ℝ)) k := by
    simp [Module.Basis.equivFun_symm_apply, ModuleSIVP.rationalBasis_apply,
      rationalEmbedding, sigma, Algebra.smul_def, ← pow_mul]
  simpa only [LinearEquiv.symm_apply_apply] using he (ModuleSIVP.rationalBasis.equivFun f)

/-- `lem:canonical` on the actual rational quotient field. -/
theorem field_norm_identity {d : ℕ} [Fact (∃ k, d = 2 ^ k)] (f : ModuleSIVP.K d) :
    (∑ k, ‖rationalEmbedding ModuleSIVP.dimension_pos k f‖^2) =
      (d : ℝ) * ∑ i, (ModuleSIVP.rationalBasis.equivFun f i : ℝ)^2 := by
  simp_rw [rationalEmbedding_eq_sigma]
  exact norm_identity ModuleSIVP.dimension_pos _

/-- These quotient evaluation maps are field embeddings for power-of-two dimensions. -/
theorem rationalEmbedding_injective {d : ℕ} [Fact (∃ k, d = 2 ^ k)] (k : Fin d) :
    Function.Injective (rationalEmbedding ModuleSIVP.dimension_pos k) :=
  RingHom.injective _

/-- Rational coefficient version of the field norm identity. -/
theorem rational_field_norm_identity {d : ℕ} [Fact (∃ k, d = 2 ^ k)] (f : ModuleSIVP.K d) :
    (∑ k, ‖rationalEmbedding ModuleSIVP.dimension_pos k f‖^2) =
      (d : ℝ) * (ratSqNorm (ModuleSIVP.rationalBasis.equivFun f) : ℝ) := by
  rw [field_norm_identity]
  simp only [ratSqNorm, Rat.cast_sum, Rat.cast_pow]

/-- Principal-ideal CVP in the actual canonical field embeddings, with arbitrary `T ∈ K_d`. -/
def PrincipalCVPYes {d : ℕ} [Fact (∃ k, d = 2 ^ k)]
    (g : Cyclotomic.QuotRing d) (T : ModuleSIVP.K d) (Δ : ℝ) : Prop :=
  ∃ a : Cyclotomic.QuotRing d,
    (∑ k, ‖rationalEmbedding ModuleSIVP.dimension_pos k (ModuleSIVP.scalarMap (g*a) - T)‖^2) ≤ Δ

/-- For every principal ideal and rational field target, squared thresholds scale by `d`. -/
theorem principalCVP_iff_rational {d : ℕ} [Fact (∃ k, d = 2 ^ k)]
    (g : Cyclotomic.QuotRing d) (T : ModuleSIVP.K d) (Δ : ℚ) :
    PrincipalCVPYes g T ((d : ℝ) * (Δ : ℝ)) ↔ ModuleSIVP.RationalPrincipalCVPYes g T Δ := by
  have hp : (0 : ℝ) < d := by exact_mod_cast (ModuleSIVP.dimension_pos (d := d))
  simp only [PrincipalCVPYes, ModuleSIVP.RationalPrincipalCVPYes, rational_field_norm_identity,
    mul_le_mul_iff_right₀ hp, Rat.cast_le]

/-- Componentwise `lem:canonical` for arbitrary rational field pairs. -/
theorem field_vector_norm_identity {d : ℕ} [Fact (∃ k, d = 2 ^ k)]
    (v : ModuleSIVP.K d × ModuleSIVP.K d) :
    (∑ k, ‖rationalEmbedding ModuleSIVP.dimension_pos k v.1‖^2) +
      (∑ k, ‖rationalEmbedding ModuleSIVP.dimension_pos k v.2‖^2) =
        (d : ℝ) * (ModuleSIVP.fieldNormSq v : ℝ) := by
  rw [field_norm_identity, field_norm_identity, ModuleSIVP.fieldNormSq]
  simp only [ratSqNorm, Rat.cast_add, Rat.cast_sum, Rat.cast_pow, mul_add]

/-- Squared canonical distance, with rational target coefficients. -/
def distanceSq {d : ℕ} (v : Coeff d) (t : RatCoeff d) : ℝ :=
  ∑ k, ‖sigma (fun i => ((v i : ℚ) - t i : ℚ)) k‖^2

/-- The distance identity applies to every lattice point and every rational target. -/
theorem distanceSq_eq {d : ℕ} (hd : 0 < d) (v : Coeff d) (t : RatCoeff d) :
    distanceSq v t = (d : ℝ) * (ratSqNorm (castCoeff v - t) : ℝ) := by
  rw [distanceSq, norm_identity hd]
  simp only [ratSqNorm, castCoeff, Pi.sub_apply, Rat.cast_sum, Rat.cast_pow]

theorem distanceSq_integral {d : ℕ} (hd : 0 < d) (v t : Coeff d) :
    distanceSq v (castCoeff t) = (d : ℝ) * (sqNorm (v - t) : ℝ) := by
  rw [distanceSq_eq hd, ratSqNorm_residual]
  norm_cast

/-- The coefficient distance is the distance in the actual rational field embeddings. -/
theorem distanceSq_eq_field {d : ℕ} [Fact (∃ k, d = 2 ^ k)]
    (v : Coeff d) (T : ModuleSIVP.K d) :
    distanceSq v (ModuleSIVP.rationalBasis.equivFun T) =
      ∑ k, ‖rationalEmbedding ModuleSIVP.dimension_pos k
        (ModuleSIVP.scalarMap (Cyclotomic.toQuot v) - T)‖^2 := by
  simp only [rationalEmbedding_eq_sigma, map_sub, ModuleSIVP.scalarMap_toQuot,
    LinearEquiv.apply_symm_apply, distanceSq]
  simp [sigma, sub_mul, Finset.sum_sub_distrib]

/-- Canonical decision CVP with a real squared threshold. -/
def CVPYes {d : ℕ} (L : AddSubgroup (Coeff d)) (t : RatCoeff d) (Δ : ℝ) : Prop :=
  ∃ v ∈ L, distanceSq v t ≤ Δ

/-- Multiplication of squared thresholds by `d` transfers rational-data CVP. -/
theorem cvp_iff_rational {d : ℕ} (hd : 0 < d) (L : AddSubgroup (Coeff d))
    (t : RatCoeff d) (Δ : ℚ) :
    CVPYes L t ((d : ℝ) * (Δ : ℝ)) ↔ RationalCVPYes L t Δ := by
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [CVPYes, RationalCVPYes, distanceSq_eq hd, mul_le_mul_iff_right₀ hp,
    Rat.cast_le]

/-- Canonical norm of an integral quotient element, using its actual evaluations. -/
def ringNormSq {d : ℕ} (hd : 0 < d) (x : Cyclotomic.QuotRing d) : ℝ :=
  ∑ k, ‖integralEmbedding hd k x‖^2

theorem ringNormSq_identity {d : ℕ} [Fact (∃ k, d = 2 ^ k)]
    (x : Cyclotomic.QuotRing d) :
    ringNormSq ModuleSIVP.dimension_pos x = (d : ℝ) * (ModuleSIVP.normSq x : ℝ) := by
  obtain ⟨c, rfl⟩ := (Cyclotomic.toQuot_bijective ModuleSIVP.dimension_pos).surjective x
  simp only [ringNormSq, integralEmbedding_toQuot, ModuleSIVP.normSq_toQuot]
  rw [norm_identity ModuleSIVP.dimension_pos]
  simp only [sqNorm, Int.cast_sum, Int.cast_pow]

/-- The componentwise squared canonical norm of a pair. -/
def vectorNormSq {d : ℕ} (hd : 0 < d)
    (v : Cyclotomic.QuotRing d × Cyclotomic.QuotRing d) : ℝ :=
  ringNormSq hd v.1 + ringNormSq hd v.2

theorem vectorNormSq_identity {d : ℕ} [Fact (∃ k, d = 2 ^ k)]
    (v : Cyclotomic.QuotRing d × Cyclotomic.QuotRing d) :
    vectorNormSq ModuleSIVP.dimension_pos v = (d : ℝ) * (ModuleSIVP.vectorNormSq v : ℝ) := by
  rw [vectorNormSq, ringNormSq_identity, ringNormSq_identity, ModuleSIVP.vectorNormSq,
    Int.cast_add, mul_add]

/-- Maximum of the two componentwise squared norms scales by the same factor. -/
theorem pairMax_identity {d : ℕ} [Fact (∃ k, d = 2 ^ k)]
    (u v : Cyclotomic.QuotRing d × Cyclotomic.QuotRing d) :
    max (vectorNormSq ModuleSIVP.dimension_pos u) (vectorNormSq ModuleSIVP.dimension_pos v) =
      (d : ℝ) * (max (ModuleSIVP.vectorNormSq u) (ModuleSIVP.vectorNormSq v) : ℤ) := by
  rw [vectorNormSq_identity, vectorNormSq_identity, Int.cast_max,
    mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ d)]

end Hardness.Canonical
namespace Hardness

/-- The X3C reduction in the canonical embedding. -/
theorem x3c_correct_canonical (I : X3CInstance) :
    I.HasExactCover ↔ Canonical.CVPYes (Cyclotomic.principalIdealLattice (x3cToCVP I).g)
      (castCoeff (x3cToCVP I).T) ((x3cToCVP I).d * ((x3cToCVP I).Δ : ℝ)) := by
  apply (x3c_correct_rational I).trans
  simpa only [Rat.cast_intCast] using
    (Canonical.cvp_iff_rational (Cyclotomic.power_two_pos (x3cToCVP I).power_two)
      _ _ ((x3cToCVP I).Δ : ℚ)).symm

/-- YES instances attain the canonical squared threshold `d Δ`. -/
theorem x3c_yes_gap_canonical (I : X3CInstance) (hy : I.HasExactCover) :
    (∃ v ∈ Cyclotomic.principalIdealLattice (x3cToCVP I).g,
      Canonical.distanceSq v (castCoeff (x3cToCVP I).T) =
        (x3cToCVP I).d * ((x3cToCVP I).Δ : ℝ)) ∧
    ∀ v ∈ Cyclotomic.principalIdealLattice (x3cToCVP I).g,
      (x3cToCVP I).d * ((x3cToCVP I).Δ : ℝ) ≤
        Canonical.distanceSq v (castCoeff (x3cToCVP I).T) := by
  obtain ⟨⟨v, hv, he⟩, hl⟩ := x3c_yes_gap I hy
  have hd := Cyclotomic.power_two_pos (x3cToCVP I).power_two
  refine ⟨⟨v, hv, ?_⟩, ?_⟩
  · rw [Canonical.distanceSq_integral hd, he]
  · intro w hw
    rw [Canonical.distanceSq_integral hd]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hl w hw) (by positivity)

/-- NO instances have canonical squared distance at least `d (Δ+4)`. -/
theorem x3c_no_gap_canonical (I : X3CInstance) (hn : ¬ I.HasExactCover) :
    ∀ v ∈ Cyclotomic.principalIdealLattice (x3cToCVP I).g,
      (x3cToCVP I).d * (((x3cToCVP I).Δ : ℝ) + 4) ≤
        Canonical.distanceSq v (castCoeff (x3cToCVP I).T) := by
  intro v hv
  rw [Canonical.distanceSq_integral (Cyclotomic.power_two_pos (x3cToCVP I).power_two)]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast x3c_no_gap I hn v hv) (by positivity)

/-- Componentwise canonical module-SIVP YES: attainment and the universal bound. -/
theorem x3c_module_sivp_yes_canonical (I : X3CInstance) (hy : I.HasExactCover) :
    let J := x3cToModuleSIVP I
    letI : Fact (∃ k, J.d = 2 ^ k) := ⟨J.power_two⟩
    (∃ u ∈ J.module, ∃ v ∈ J.module, ModuleSIVP.Independent u v ∧
      max (Canonical.vectorNormSq ModuleSIVP.dimension_pos u)
        (Canonical.vectorNormSq ModuleSIVP.dimension_pos v) = (J.d : ℝ) * J.Γ) ∧
    ∀ u ∈ J.module, ∀ v ∈ J.module, ModuleSIVP.Independent u v →
      (J.d : ℝ) * J.Γ ≤ max (Canonical.vectorNormSq ModuleSIVP.dimension_pos u)
        (Canonical.vectorNormSq ModuleSIVP.dimension_pos v) := by
  let J := x3cToModuleSIVP I
  letI : Fact (∃ k, J.d = 2 ^ k) := ⟨J.power_two⟩
  obtain ⟨⟨u, hu, v, hv, hi, he⟩, hl⟩ := x3c_module_sivp_yes I hy
  refine ⟨⟨u, hu, v, hv, hi, ?_⟩, ?_⟩
  · rw [Canonical.pairMax_identity, he]
  · intro u hu v hv hi
    rw [Canonical.pairMax_identity]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hl u hu v hv hi) (by positivity)

/-- Componentwise canonical module-SIVP NO: squared gap `d (Γ+4)`. -/
theorem x3c_module_sivp_no_canonical (I : X3CInstance) (hn : ¬ I.HasExactCover) :
    let J := x3cToModuleSIVP I
    letI : Fact (∃ k, J.d = 2 ^ k) := ⟨J.power_two⟩
    ∀ u ∈ J.module, ∀ v ∈ J.module, ModuleSIVP.Independent u v →
      (J.d : ℝ) * ((J.Γ : ℝ) + 4) ≤ max (Canonical.vectorNormSq ModuleSIVP.dimension_pos u)
        (Canonical.vectorNormSq ModuleSIVP.dimension_pos v) := by
  let J := x3cToModuleSIVP I
  letI : Fact (∃ k, J.d = 2 ^ k) := ⟨J.power_two⟩
  dsimp only
  intro u hu v hv hi
  rw [Canonical.pairMax_identity]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast x3c_module_sivp_no I hn u hu v hv hi)
    (by positivity)

end Hardness
