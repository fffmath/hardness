import Power2IdealSVP.Algebra.SpinBasic

/-!
# Sparse spins and their finite local-field objective

Paper: `paper/power2-ideal-svp.txt`, Section 1.2; expanded audit, Section 6.

`OddAlternating` includes both choices of initial sign. Alternation is expressed by the
number of support coordinates strictly preceding a coordinate, hence agrees with alternation
on the increasing support list. `Theta` is an integer finite maximum of finite minima.
Its value at degree zero is defined to be zero; all mathematical uses assume positive degree.
-/

namespace Power2IdealSVP.Spin

open Power2ModuleSVP (Coeff)
open IdealCVP.Cyclotomic (mul)

/-- The shared antiperiodic extension, using the signed Euclidean quotient at every wrap. -/
abbrev antiperiodicExtension {n : ℕ} (σ : Coeff n) : ℤ → ℤ := lift σ

/-- The shared extension reverses sign on translation by the degree. -/
theorem antiperiodicExtension_antiperiodic {n : ℕ} (σ : Coeff n) :
    Function.Antiperiodic (antiperiodicExtension σ) (n : ℤ) := lift_antiperiodic σ

/-- The nonzero coefficient positions of a vector. -/
def support {n : ℕ} (σ : Coeff n) : Finset (Fin n) :=
  Finset.univ.filter fun i => σ i ≠ 0

/-- Membership in the support means the coefficient is nonzero. -/
@[simp] theorem mem_support {n : ℕ} (σ : Coeff n) (i : Fin n) :
    i ∈ support σ ↔ σ i ≠ 0 := by simp [support]

/-- Every coefficient is one of the three allowed spin values. -/
def Ternary {n : ℕ} (σ : Coeff n) : Prop :=
  ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1

/-- The ordinal position of a support coordinate, starting at zero. -/
def supportRank {n : ℕ} (σ : Coeff n) (i : Fin n) : ℕ :=
  ((support σ).filter fun j => j < i).card

/-- A ternary vector of odd support size whose nonzero coefficients alternate in order. -/
def OddAlternating {n : ℕ} (σ : Coeff n) : Prop :=
  Ternary σ ∧ Odd (support σ).card ∧
    ∃ η : ℤ, (η = -1 ∨ η = 1) ∧
      ∀ i ∈ support σ, σ i = η * (-1) ^ supportRank σ i

/-- The signed local field at a coordinate, using negacyclic multiplication. -/
def fieldAt {n : ℕ} (G σ : Coeff n) (i : Fin n) : ℤ :=
  σ i * (mul G σ) i

/-- All ternary coefficient arrays, enumerated by functions with values in `Fin 3`. -/
def ternaryCoeffs (n : ℕ) : Finset (Coeff n) :=
  Finset.univ.image fun f : Fin n → Fin 3 => fun i => (f i).val - (1 : ℤ)

/-- The finite set of sparse spins, including both initial signs. -/
noncomputable def spinSet (n : ℕ) : Finset (Coeff n) := by
  classical
  exact (ternaryCoeffs n).filter OddAlternating

/-- The minimum active local field, with a harmless total value at the empty support. -/
noncomputable def spinValue {n : ℕ} (G σ : Coeff n) : ℤ :=
  if hs : (support σ).Nonempty then (support σ).inf' hs (fieldAt G σ) else 0

/-- The maximum active-field minimum over all odd alternating supports.

Precisely, for positive `n`, this is `sup' (spinSet n)` of
`inf' (support σ) (fun i => σ i * (mul G σ) i)`. Both finite indexing sets are nonempty.
The definition has no promise concerning `G` or a decision threshold.
-/
noncomputable def Theta {n : ℕ} (G : Coeff n) : ℤ :=
  if hs : (spinSet n).Nonempty then (spinSet n).sup' hs (spinValue G) else 0

/-- The finite ternary enumeration contains exactly the ternary arrays. -/
theorem mem_ternaryCoeffs {n : ℕ} (σ : Coeff n) :
    σ ∈ ternaryCoeffs n ↔ Ternary σ := by
  classical
  constructor
  · intro h i
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp h
    have hi := (f i).isLt
    change (f i).val - (1 : ℤ) = -1 ∨
      (f i).val - (1 : ℤ) = 0 ∨ (f i).val - (1 : ℤ) = 1
    omega
  · intro h
    let f : Fin n → Fin 3 := fun i =>
      if σ i = -1 then 0 else if σ i = 0 then 1 else 2
    apply Finset.mem_image.mpr
    refine ⟨f, Finset.mem_univ _, ?_⟩
    funext i
    rcases h i with hi | hi | hi <;> simp [f, hi]

/-- The finite spin enumeration contains exactly the odd alternating arrays. -/
@[simp] theorem mem_spinSet {n : ℕ} (σ : Coeff n) :
    σ ∈ spinSet n ↔ OddAlternating σ := by
  classical
  simp only [spinSet, Finset.mem_filter, mem_ternaryCoeffs]
  exact ⟨And.right, fun h => ⟨h.1, h⟩⟩

/-- Odd support cardinality ensures that the active minimum is defined. -/
theorem OddAlternating.support_nonempty {n : ℕ} {σ : Coeff n}
    (hσ : OddAlternating σ) : (support σ).Nonempty := by
  by_contra hs
  have he := Finset.not_nonempty_iff_eq_empty.mp hs
  simpa [he] using hσ.2.1

/-- A positive unit monomial is a valid singleton sparse spin. -/
theorem oddAlternating_singleton {n : ℕ} (i : Fin n) :
    OddAlternating (IdealCVP.Cyclotomic.monomial i 1) := by
  classical
  have hs : support (IdealCVP.Cyclotomic.monomial i 1) = {i} := by
    ext j
    simp [IdealCVP.Cyclotomic.monomial, eq_comm]
  refine ⟨?_, ?_, 1, Or.inr rfl, ?_⟩
  · intro j
    by_cases hj : j = i <;> simp [IdealCVP.Cyclotomic.monomial, hj]
  · simp [hs]
  · intro j hj
    have hj' : j = i := by simpa [hs] using hj
    subst j
    have hf : ({i} : Finset (Fin n)).filter (fun j => j < i) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨rfl, hj⟩
      exact (lt_irrefl _) hj
    simp [supportRank, hs, hf]

/-- Sparse spins exist in every positive degree. -/
theorem spinSet_nonempty {n : ℕ} (hn : 0 < n) : (spinSet n).Nonempty :=
  ⟨_, (mem_spinSet _).mpr (oddAlternating_singleton ⟨0, hn⟩)⟩

/-- Thresholding a spin minimum means thresholding every active field. -/
theorem le_spinValue_iff {n : ℕ} {G σ : Coeff n} (hσ : OddAlternating σ) (t : ℤ) :
    t ≤ spinValue G σ ↔ ∀ i ∈ support σ, t ≤ fieldAt G σ i := by
  rw [spinValue, dite_eq_left hσ.support_nonempty, Finset.le_inf'_iff]

/-- The finite maximum has exactly the intended existential threshold semantics. -/
theorem le_Theta_iff {n : ℕ} (hn : 0 < n) (G : Coeff n) (t : ℤ) :
    t ≤ Theta G ↔ ∃ σ : Coeff n, OddAlternating σ ∧
      ∀ i ∈ support σ, t ≤ fieldAt G σ i := by
  classical
  rw [Theta, dite_eq_left (spinSet_nonempty hn), Finset.le_sup'_iff]
  constructor
  · rintro ⟨σ, hσ, ht⟩
    exact ⟨σ, (mem_spinSet σ).mp hσ,
      (le_spinValue_iff ((mem_spinSet σ).mp hσ) t).mp ht⟩
  · rintro ⟨σ, hσ, ht⟩
    exact ⟨σ, (mem_spinSet σ).mpr hσ, (le_spinValue_iff hσ t).mpr ht⟩

/-- Every ternary array is in the coefficient unit cube. -/
theorem Ternary.cube {n : ℕ} {σ : Coeff n} (hσ : Ternary σ) :
    Power2ModuleSVP.Cube σ := by
  intro i
  rcases hσ i with hi | hi | hi <;> simp [hi]

/-- Global sign reversal preserves the support. -/
@[simp] theorem support_neg {n : ℕ} (σ : Coeff n) : support (-σ) = support σ := by
  ext i
  simp

/-- Global sign reversal preserves the support rank. -/
@[simp] theorem supportRank_neg {n : ℕ} (σ : Coeff n) (i : Fin n) :
    supportRank (-σ) i = supportRank σ i := by simp [supportRank]

/-- Reversing the initial sign preserves the class of sparse spins. -/
theorem OddAlternating.neg {n : ℕ} {σ : Coeff n} (hσ : OddAlternating σ) :
    OddAlternating (-σ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases hσ.1 i with hi | hi | hi <;> simp [hi]
  · simpa using hσ.2.1
  · obtain ⟨η, hη, he⟩ := hσ.2.2
    refine ⟨-η, ?_, ?_⟩
    · rcases hη with rfl | rfl <;> simp
    · intro i hi
      have hi' : i ∈ support σ := by simpa using hi
      simp [he i hi']

/-- Initial sign reversal leaves all local fields unchanged, for any multiplier. -/
@[simp] theorem fieldAt_neg {n : ℕ} (G σ : Coeff n) (i : Fin n) :
    fieldAt G (-σ) i = fieldAt G σ i := by
  simp [fieldAt, IdealCVP.Cyclotomic.mul_neg]

/-- Put alternating signs, with prescribed initial sign, on a finite support. -/
def alternatingOn {n : ℕ} (W : Finset (Fin n)) (η : ℤ) : Coeff n := fun i =>
  if i ∈ W then η * (-1) ^ (W.filter fun j => j < i).card else 0

/-- The support of the alternating construction is exactly the prescribed set. -/
@[simp] theorem support_alternatingOn {n : ℕ} (W : Finset (Fin n)) {η : ℤ}
    (hη : η = -1 ∨ η = 1) : support (alternatingOn W η) = W := by
  ext i
  simp only [mem_support, alternatingOn]
  split_ifs with hi
  · rcases hη with rfl | rfl <;> simp [hi]
  · simp [hi]

/-- Every odd finite support supplies an actual sparse spin. -/
theorem oddAlternating_alternatingOn {n : ℕ} (W : Finset (Fin n))
    (hW : Odd W.card) {η : ℤ} (hη : η = -1 ∨ η = 1) :
    OddAlternating (alternatingOn W η) := by
  refine ⟨?_, by simpa only [support_alternatingOn W hη] using hW, η, hη, ?_⟩
  · intro i
    by_cases hi : i ∈ W
    · rcases neg_one_pow_eq_or ℤ (W.filter fun j => j < i).card with he | he <;>
        rcases hη with rfl | rfl <;> simp [alternatingOn, hi, he]
    · simp [alternatingOn, hi]
  · intro i hi
    have hi' : i ∈ W := by simpa only [support_alternatingOn W hη] using hi
    simp [alternatingOn, hi', supportRank, support_alternatingOn W hη]

/-- An odd alternating array is determined by its support and its initial sign. -/
theorem OddAlternating.eq_alternatingOn {n : ℕ} {σ : Coeff n}
    (hσ : OddAlternating σ) :
    ∃ η : ℤ, (η = -1 ∨ η = 1) ∧ σ = alternatingOn (support σ) η := by
  obtain ⟨η, hη, he⟩ := hσ.2.2
  refine ⟨η, hη, ?_⟩
  funext i
  by_cases hi : i ∈ support σ
  · simpa [alternatingOn, hi, supportRank] using he i hi
  · simpa [alternatingOn, hi] using not_not.mp ((not_congr (mem_support σ i)).mp hi)

/-- Sparse spins with the same support differ by at most their global sign. -/
theorem OddAlternating.eq_or_eq_neg_of_support_eq {n : ℕ} {σ ρ : Coeff n}
    (hσ : OddAlternating σ) (hρ : OddAlternating ρ) (hs : support σ = support ρ) :
    σ = ρ ∨ σ = -ρ := by
  obtain ⟨η, hη, he⟩ := hσ.eq_alternatingOn
  obtain ⟨ν, hν, hf⟩ := hρ.eq_alternatingOn
  rw [he, hf, hs]
  rcases hη with rfl | rfl <;> rcases hν with rfl | rfl
  · exact Or.inl rfl
  · right; funext i; simp only [alternatingOn, Pi.neg_apply]; split_ifs <;> ring
  · right; funext i; simp only [alternatingOn, Pi.neg_apply]; split_ifs <;> ring
  · exact Or.inl rfl

/-- On a fixed odd support, the local fields do not depend on the initial sign. -/
theorem OddAlternating.fieldAt_eq_of_support_eq {n : ℕ} {σ ρ : Coeff n}
    (hσ : OddAlternating σ) (hρ : OddAlternating ρ) (hs : support σ = support ρ)
    (G : Coeff n) (i : Fin n) : fieldAt G σ i = fieldAt G ρ i := by
  rcases hσ.eq_or_eq_neg_of_support_eq hρ hs with he | he
  · rw [he]
  · rw [he, fieldAt_neg]

end Power2IdealSVP.Spin
