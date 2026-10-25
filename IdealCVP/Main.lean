import IdealCVP.Reduction

/-! # Compiler correctness and X3C specialization

These are mathematical reductions and squared-distance gap statements. Neither
NP membership nor polynomial-time Turing machine statements are claimed here.
-/
namespace IdealCVP
open IdealCVP.Cyclotomic
namespace ReductionData
variable {M n : ℕ} (D : ReductionData M n)

/-- No multiplier beats the threshold, in either a YES or a NO instance. -/
theorem universal_lower_bound (q : R D.d) :
    D.Δ ≤ sqNorm (mul D.g q - D.T) := by
  classical
  by_cases hq : ∃ ξ, D.system.Allowed ξ ∧ q = D.encode ξ
  · obtain ⟨ξ, hξ, rfl⟩ := hq
    rw [D.admissible_allowed ξ hξ]
    have := sqNorm_nonneg (D.system.residual ξ)
    omega
  · have := D.admissible_forbidden q hq
    omega

/-- The compiler's exact characterization, retaining the multiplier witness. -/
theorem within_threshold_iff (q : R D.d) :
    sqNorm (mul D.g q - D.T) ≤ D.Δ ↔
      ∃ ξ, D.system.Feasible ξ ∧ q = D.encode ξ := by
  classical
  constructor
  · intro hd
    by_cases hq : ∃ ξ, D.system.Allowed ξ ∧ q = D.encode ξ
    · obtain ⟨ξ, hξ, rfl⟩ := hq
      rw [D.admissible_allowed ξ hξ] at hd
      have hn := sqNorm_nonneg (D.system.residual ξ)
      have hz : sqNorm (D.system.residual ξ) = 0 := by omega
      exact ⟨ξ, ⟨hξ, (sqNorm_eq_zero_iff _).mp hz⟩, rfl⟩
    · have := D.admissible_forbidden q hq
      omega
  · rintro ⟨ξ, ⟨hξ, he⟩, rfl⟩
    rw [D.admissible_allowed ξ hξ, he, sqNorm_zero]
    omega

/-- Theorem `thm:compiler`: correctness for exact decision CVP. -/
theorem compiler_correct :
    D.system.HasSolution ↔ CVPYes D.lattice D.T D.Δ := by
  constructor
  · rintro ⟨ξ, hξ⟩
    refine ⟨mul D.g (D.encode ξ), ⟨D.encode ξ, rfl⟩, ?_⟩
    exact (D.within_threshold_iff _).mpr ⟨ξ, hξ, rfl⟩
  · rintro ⟨v, ⟨q, rfl⟩, hv⟩
    obtain ⟨ξ, hξ, _⟩ := (D.within_threshold_iff q).mp hv
    exact ⟨ξ, hξ⟩

/-- YES instances attain Δ, and every lattice vector has distance at least Δ. -/
theorem compiler_yes (hy : D.system.HasSolution) :
    MinimumSquaredDistance D.lattice D.T D.Δ := by
  obtain ⟨ξ, hξ⟩ := hy
  constructor
  · refine ⟨mul D.g (D.encode ξ), ⟨D.encode ξ, rfl⟩, ?_⟩
    rw [D.admissible_allowed ξ hξ.1, hξ.2, sqNorm_zero]
    ring
  · rintro v ⟨q, rfl⟩
    exact D.universal_lower_bound q

/-- NO instances have the promised additive squared-distance gap of four. -/
theorem compiler_no (hn : ¬ D.system.HasSolution) :
    ∀ v ∈ D.lattice, D.Δ + 4 ≤ sqNorm (v - D.T) := by
  classical
  rintro v ⟨q, rfl⟩
  change D.Δ + 4 ≤ sqNorm (mul D.g q - D.T)
  by_cases hq : ∃ ξ, D.system.Allowed ξ ∧ q = D.encode ξ
  · obtain ⟨ξ, hξ, rfl⟩ := hq
    have he : D.system.residual ξ ≠ 0 := fun hz => hn ⟨ξ, hξ, hz⟩
    have := sqNorm_pos he
    rw [D.admissible_allowed ξ hξ]
    omega
  · have := D.admissible_forbidden q hq
    omega

/-- Distinct Boolean assignments give distinct ideal elements. Only the odd
block is needed, so no domain assumption on the coefficient model is hidden. -/
theorem encoded_product_injective : Function.Injective (fun ξ => mul D.g (D.encode ξ)) := by
  intro ξ η he
  have he' : mul D.g (interleave (D.a ξ) 0) - D.T =
      mul D.g (interleave (D.a η) 0) - D.T := congrArg (fun v => v - D.T) he
  rw [D.block_product, D.block_product] at he'
  have ho := (interleave_injective he').2
  have hp : (D.P : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt D.P_pos)
  apply D.encode_injective
  unfold encode
  congr 1
  funext r
  have hr := congrFun ho r
  simp only [mul_zero, smul_zero, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, zero_add] at hr
  have hm : (2 * (D.P : ℤ)) * D.a ξ r = (2 * (D.P : ℤ)) * D.a η r := by linarith
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hp) hm

/-- Bijection between feasible vectors and lattice points at exactly Δ. -/
noncomputable def feasibleEquivClosest :
    {ξ // D.system.Feasible ξ} ≃
      {v : R D.d // v ∈ D.lattice ∧ sqNorm (v - D.T) = D.Δ} := by
  let f : {ξ // D.system.Feasible ξ} →
      {v : R D.d // v ∈ D.lattice ∧ sqNorm (v - D.T) = D.Δ} := fun ξ =>
    ⟨mul D.g (D.encode ξ.val), ⟨D.encode ξ.val, rfl⟩, by
      rw [D.admissible_allowed ξ.val ξ.property.1, ξ.property.2, sqNorm_zero]
      ring⟩
  apply Equiv.ofBijective f
  constructor
  · intro ξ η h
    apply Subtype.ext
    exact D.encoded_product_injective (congrArg Subtype.val h)
  · rintro ⟨v, ⟨q, rfl⟩, hv⟩
    obtain ⟨ξ, hξ, hq⟩ := (D.within_threshold_iff q).mp (le_of_eq hv)
    refine ⟨⟨ξ, hξ⟩, ?_⟩
    apply Subtype.ext
    dsimp [f]
    rw [hq]
    rfl

end ReductionData

/-- A principal power-of-two cyclotomic CVP instance, including the required
nonzero generator and nonnegative squared threshold. -/
structure PrincipalCVPInstance where
  d : ℕ
  power_two : ∃ k : ℕ, d = 2 ^ k
  g : R d
  g_ne_zero : g ≠ 0
  T : R d
  Δ : ℤ
  Δ_nonneg : 0 ≤ Δ

namespace X3CInstance

/-- The canonical masked incidence data and Sidon positions for an indexed X3C instance. -/
def reductionData (I : X3CInstance) : ReductionData (3 * I.q) I.n where
  system := I.system
  positions := SidonPositions.erdosTuran I.n
  M_pos := by have := I.q_pos; omega
  n_pos := I.n_pos

end X3CInstance

/-- The explicit X3C → principal cyclotomic CVP map. -/
def x3cToCVP (I : X3CInstance) : PrincipalCVPInstance where
  d := I.reductionData.d
  power_two := I.reductionData.d_power_two
  g := I.reductionData.g
  g_ne_zero := I.reductionData.g_ne_zero
  T := I.reductionData.T
  Δ := I.reductionData.Δ
  Δ_nonneg := by unfold ReductionData.Δ; positivity

/-- The mathematical reduction in Theorem `thm:cyclotomic-cvp`. -/
theorem x3c_correct (I : X3CInstance) :
    I.HasExactCover ↔ CVPYes (principalIdealLattice (x3cToCVP I).g)
      (x3cToCVP I).T (x3cToCVP I).Δ :=
  I.hasExactCover_iff_hasSolution.trans I.reductionData.compiler_correct

/-- An exact cover attains the reduction threshold as its minimum squared distance. -/
theorem x3c_yes_gap (I : X3CInstance) (hy : I.HasExactCover) :
    MinimumSquaredDistance (principalIdealLattice (x3cToCVP I).g)
      (x3cToCVP I).T (x3cToCVP I).Δ :=
  I.reductionData.compiler_yes (I.hasExactCover_iff_hasSolution.mp hy)

/-- Without an exact cover, every lattice vector has squared distance at least the threshold
plus four. -/
theorem x3c_no_gap (I : X3CInstance) (hn : ¬ I.HasExactCover) :
    ∀ v ∈ principalIdealLattice (x3cToCVP I).g,
      (x3cToCVP I).Δ + 4 ≤ sqNorm (v - (x3cToCVP I).T) :=
  I.reductionData.compiler_no (hn ∘ I.hasExactCover_iff_hasSolution.mpr)

/-- Exact covers correspond to g a_ξ(y²) at squared distance exactly Δ. -/
noncomputable def exactCoverEquivClosest (I : X3CInstance) :
    {s // I.IsExactCover s} ≃
      {v : R (x3cToCVP I).d // v ∈ principalIdealLattice (x3cToCVP I).g ∧
        sqNorm (v - (x3cToCVP I).T) = (x3cToCVP I).Δ} :=
  I.exactCoverEquivFeasible.trans I.reductionData.feasibleEquivClosest

@[simp] theorem exactCoverEquivClosest_apply (I : X3CInstance)
    (s : {s // I.IsExactCover s}) :
    (exactCoverEquivClosest I s).val =
      mul (x3cToCVP I).g (I.reductionData.encode (I.selectionEquiv s.val)) := rfl

end IdealCVP
