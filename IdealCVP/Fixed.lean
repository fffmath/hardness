import IdealCVP.GeneralFullRank

/-! # A fixed ideal family for masked collections of triples

All triples of an `m`-element universe are enumerated once. The incidence
matrix, generator, ideal and multiplication basis are fixed by `m`; only
the mask, target and threshold depend on the collection. No preprocessing
or complexity-class assertion is made here.
-/
noncomputable section
namespace IdealCVP.Fixed
open IdealCVP.Cyclotomic

/-- All three-element subsets, including their cardinality certificate. -/
abbrev Triple (m : ℕ) := ↥((Finset.univ : Finset (Fin m)).powersetCard 3)

/-- The number of distinct three-element subsets is the binomial coefficient. -/
theorem triple_card (m : ℕ) : Fintype.card (Triple m) = m.choose 3 := by
  simp [Triple]

/-- Any fixed enumeration suffices; no property of lexicographic order is used. -/
def enumeration (m : ℕ) : Fin (m.choose 3) ≃ Triple m :=
  (Fintype.equivFinOfCardEq (triple_card m)).symm

/-- Ordinary exact covers by a subcollection of the input set of triples. -/
def HasExactCover {m : ℕ} (C : Finset (Triple m)) : Prop :=
  ∃ s : Finset (Triple m), s ⊆ C ∧
    ∀ i : Fin m, (s.filter fun t => i ∈ t.val).card = 1

/-- The universal incidence matrix `U_m`, with target all ones. -/
def system (m : ℕ) (C : Finset (Triple m)) : MaskedSystem m (m.choose 3) where
  A i j := decide (i ∈ (enumeration m j).val)
  b _ := true
  μ j := decide (enumeration m j ∈ C)

/-- Selection sets and Boolean coefficient vectors have a fixed bijection. -/
def selectionEquiv (m : ℕ) : Finset (Triple m) ≃ (Fin (m.choose 3) → Bool) where
  toFun s j := decide (enumeration m j ∈ s)
  invFun ξ := (Finset.univ.filter fun j => ξ j = true).map (enumeration m).toEmbedding
  left_inv s := by ext t; simp
  right_inv ξ := by funext j; cases h : ξ j <;> simp [h]

/-- Subcollection exact covers correspond to feasible masked incidence systems. -/
theorem cover_iff_feasible {m : ℕ} (C s : Finset (Triple m)) :
    (s ⊆ C ∧ ∀ i : Fin m, (s.filter fun t => i ∈ t.val).card = 1) ↔
      (system m C).Feasible (selectionEquiv m s) := by
  have hsum (i : Fin m) :
      (∑ j, bit ((system m C).A i j) * bit (selectionEquiv m s j)) =
        ((s.filter fun t => i ∈ t.val).card : ℤ) := by
    change (∑ j, bit (decide (i ∈ (enumeration m j).val)) *
      bit (decide (enumeration m j ∈ s))) = _
    rw [(enumeration m).sum_comp (fun t : Triple m =>
      bit (decide (i ∈ t.val)) * bit (decide (t ∈ s)))]
    simp only [bit, decide_eq_true_eq]
    simp only [mul_ite, _root_.mul_one, MulZeroClass.mul_zero]
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun t : Triple m => t ∈ s) = s := by ext t; simp
    rw [hf, ← Finset.sum_filter]
    simp
  have hallowed : (system m C).Allowed (selectionEquiv m s) ↔ s ⊆ C := by
    change (∀ j, decide (enumeration m j ∈ s) = true →
      decide (enumeration m j ∈ C) = true) ↔ _
    simp only [decide_eq_true_eq]
    constructor
    · intro h t ht
      obtain ⟨j, rfl⟩ := (enumeration m).surjective t
      exact h j ht
    · intro h j hj; exact h hj
  rw [MaskedSystem.Feasible, hallowed]
  apply and_congr_right
  intro _
  change (∀ i : Fin m, (s.filter fun t => i ∈ t.val).card = 1) ↔
    (fun i => (∑ j, bit ((system m C).A i j) * bit (selectionEquiv m s j)) - 1) = 0
  simp only [funext_iff, Pi.zero_apply, sub_eq_zero, hsum, Nat.cast_eq_one]

/-- The combinatorial equivalence in `thm:fixed-family`, for every universe
size (also when it is not divisible by three). -/
theorem hasExactCover_iff_hasSolution {m : ℕ} (C : Finset (Triple m)) :
    HasExactCover C ↔ (system m C).HasSolution := by
  constructor
  · rintro ⟨s, hs⟩; exact ⟨selectionEquiv m s, (cover_iff_feasible C s).mp hs⟩
  · rintro ⟨ξ, hξ⟩
    refine ⟨(selectionEquiv m).symm ξ, ?_⟩
    exact (cover_iff_feasible C _).mpr (by simpa using hξ)

/-- The compiler data for the fixed system, before choosing its mask. -/
def baseData (m : ℕ) (hm : 3 ≤ m) : ReductionData m (m.choose 3) where
  system := system m Finset.univ
  positions := SidonPositions.erdosTuran (m.choose 3)
  M_pos := by omega
  n_pos := Nat.choose_pos hm

/-- Only the mask is changed for a particular input collection. -/
def data (m : ℕ) (hm : 3 ≤ m) (C : Finset (Triple m)) : ReductionData m (m.choose 3) :=
  (baseData m hm).withMask (system m C).μ

@[simp] theorem data_system (m : ℕ) (hm : 3 ≤ m) (C : Finset (Triple m)) :
    (data m hm C).system = system m C := rfl

/-- The generator is shared by all collections on this universe. -/
def generator (m : ℕ) (hm : 3 ≤ m) : R (baseData m hm).d := (baseData m hm).g

/-- The principal ideal lattice fixed by the universe size. -/
def lattice (m : ℕ) (hm : 3 ≤ m) : AddSubgroup (R (baseData m hm).d) :=
  principalIdealLattice (generator m hm)

/-- The entire multiplication basis is fixed by `m`. -/
def basis (m : ℕ) (hm : 3 ≤ m) : Module.Basis (Fin (baseData m hm).d) ℤ (lattice m hm) :=
  principalMultiplicationBasis (baseData m hm).d_power_two _ (baseData m hm).g_ne_zero

/-- The collection-dependent target in the fixed principal ideal. -/
def target (m : ℕ) (hm : 3 ≤ m) (C : Finset (Triple m)) : R (baseData m hm).d :=
  (data m hm C).T

/-- The collection-dependent squared-distance threshold. -/
def threshold (m : ℕ) (hm : 3 ≤ m) (C : Finset (Triple m)) : ℤ := (data m hm C).Δ

/-- Changing the input collection preserves the generator for a fixed universe. -/
theorem generator_independent (m : ℕ) (hm : 3 ≤ m) (C : Finset (Triple m)) :
    (data m hm C).g = generator m hm :=
  (baseData m hm).generator_mask_independent _

/-- Changing the input collection preserves the principal ideal lattice. -/
theorem lattice_independent (m : ℕ) (hm : 3 ≤ m) (C : Finset (Triple m)) :
    (data m hm C).lattice = lattice m hm := by
  change principalIdealLattice (data m hm C).g = _
  rw [generator_independent]
  rfl

/-- Every multiplication column is independent of the input collection.
`principalMultiplicationBasis_apply` identifies these with the basis vectors. -/
theorem basis_columns_independent (m : ℕ) (hm : 3 ≤ m) (C : Finset (Triple m))
    (j : Fin (baseData m hm).d) :
    @mul (baseData m hm).d (data m hm C).g (monomial j 1) =
      @mul (baseData m hm).d (generator m hm) (monomial j 1) := by
  exact congrArg (fun g : R (baseData m hm).d =>
    @mul (baseData m hm).d g (monomial j 1)) (generator_independent m hm C)

/-- Paper `thm:fixed-family`, mathematical correctness for the fixed ideal. -/
theorem fixed_family_correct (m : ℕ) (hm : 3 ≤ m) (C : Finset (Triple m)) :
    HasExactCover C ↔ CVPYes (lattice m hm) (target m hm C) (threshold m hm C) := by
  rw [hasExactCover_iff_hasSolution]
  have h := (data m hm C).compiler_correct
  rw [data_system, lattice_independent] at h
  exact h

/-- YES instances attain the collection-dependent threshold in the fixed ideal. -/
theorem fixed_family_yes (m : ℕ) (hm : 3 ≤ m) (C : Finset (Triple m))
    (hy : HasExactCover C) :
    MinimumSquaredDistance (lattice m hm) (target m hm C) (threshold m hm C) := by
  have h := (data m hm C).compiler_yes ((hasExactCover_iff_hasSolution C).mp hy)
  rw [lattice_independent] at h
  exact h

/-- NO instances retain the four-unit squared gap in the very same ideal. -/
theorem fixed_family_no (m : ℕ) (hm : 3 ≤ m) (C : Finset (Triple m))
    (hn : ¬ HasExactCover C) :
    ∀ v ∈ lattice m hm, threshold m hm C + 4 ≤ sqNorm (v - target m hm C) := by
  have h := (data m hm C).compiler_no (hn ∘ (hasExactCover_iff_hasSolution C).mpr)
  rw [lattice_independent] at h
  exact h

end IdealCVP.Fixed
