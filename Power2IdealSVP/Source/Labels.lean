import Power2IdealSVP.Source.ThreeTerm
import Power2IdealSVP.Source.Extraction

/-!
# Polynomial source labels

The base expansion and three-term uniqueness of the source labels, with multiplicities.

Paper: `Power2IdealSVP/paper/power2-ideal-svp.txt`, Section 1.1.
-/

namespace Power2IdealSVP.Source

/-- The no-carry base used by the cubic source labels. -/
def base (v : ℕ) : ℕ := 3 * v ^ 3 + 1

/-- Vertices of `Fin v` carry the one-based integer indices `1,…,v`. -/
def index {v : ℕ} (i : Fin v) : ℤ := (i.val : ℤ) + 1

/-- The cubic source label `i + b₀ i² + b₀² i³`. -/
def label {v : ℕ} (i : Fin v) : ℤ :=
  index i + (base v : ℤ) * index i ^ 2 + (base v : ℤ) ^ 2 * index i ^ 3

/-- The label base is positive, including for an empty vertex set. -/
@[simp] theorem base_pos (v : ℕ) : 0 < base v := by unfold base; omega

/-- The one-based vertex index is positive. -/
@[simp] theorem index_pos {v : ℕ} (i : Fin v) : 0 < index i := by
  unfold index
  omega

/-- Every one-based vertex index is at most the vertex count. -/
theorem index_le {v : ℕ} (i : Fin v) : index i ≤ v := by
  unfold index
  exact_mod_cast Nat.succ_le_of_lt i.isLt

/-- One-based indexing preserves distinct vertices. -/
theorem index_injective {v : ℕ} : Function.Injective (@index v) := by
  intro i j h
  apply Fin.ext
  dsimp [index] at h
  omega

/-- The source label is positive for every vertex. -/
theorem label_pos {v : ℕ} (i : Fin v) : 0 < label i := by
  unfold label
  have := index_pos i
  have := base_pos v
  positivity

/-- Source labels increase strictly with their vertex indices. -/
theorem label_strictMono {v : ℕ} : StrictMono (@label v) := by
  intro i j hij
  have hi : 0 ≤ index i := le_of_lt (index_pos i)
  have hj : index i < index j := by
    have hij' : i.val < j.val := hij
    dsimp [index]
    omega
  dsimp [label]
  have hb : 0 ≤ (base v : ℤ) := by positivity
  have h₂ : index i ^ 2 ≤ index j ^ 2 := by gcongr
  have h₃ : index i ^ 3 ≤ index j ^ 3 := by gcongr
  exact add_lt_add_of_lt_of_le
    (add_lt_add_of_lt_of_le hj (mul_le_mul_of_nonneg_left h₂ hb))
    (mul_le_mul_of_nonneg_left h₃ (sq_nonneg _))

/-- Different source vertices have different labels. -/
theorem label_injective {v : ℕ} : Function.Injective (@label v) :=
  label_strictMono.injective

private theorem index_powers_le {v : ℕ} (i : Fin v) :
    index i ≤ (v : ℤ) ^ 3 ∧ index i ^ 2 ≤ (v : ℤ) ^ 3 ∧
      index i ^ 3 ≤ (v : ℤ) ^ 3 := by
  have hi := index_le i
  have hi0 : 0 ≤ index i := le_of_lt (index_pos i)
  have hv : 1 ≤ (v : ℤ) := by have := index_pos i; omega
  have hv2 : (v : ℤ) ≤ (v : ℤ) ^ 2 := by nlinarith
  have hv3 : (v : ℤ) ^ 2 ≤ (v : ℤ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (v : ℤ)) (show 0 ≤ (v : ℤ) - 1 by omega)]
  refine ⟨le_trans hi (le_trans hv2 hv3), le_trans ?_ hv3, ?_⟩ <;> gcongr

private theorem digit_bounds {v : ℕ} (i j k : Fin v) :
    (0 ≤ index i + index j + index k ∧
      index i + index j + index k < (base v : ℤ)) ∧
    (0 ≤ index i ^ 2 + index j ^ 2 + index k ^ 2 ∧
      index i ^ 2 + index j ^ 2 + index k ^ 2 < (base v : ℤ)) ∧
    (0 ≤ index i ^ 3 + index j ^ 3 + index k ^ 3 ∧
      index i ^ 3 + index j ^ 3 + index k ^ 3 < (base v : ℤ)) := by
  have hi := index_powers_le i
  have hj := index_powers_le j
  have hk := index_powers_le k
  have hi0 := index_pos i
  have hj0 := index_pos j
  have hk0 := index_pos k
  have hb : (base v : ℤ) = 3 * (v : ℤ) ^ 3 + 1 := by simp [base]
  rw [hb]
  refine ⟨⟨by positivity, by omega⟩, ⟨by positivity, by omega⟩,
    ⟨by positivity, by omega⟩⟩

/-- Equality of three source labels determines the multiset of vertices, with repetitions. -/
theorem three_term_unique {v : ℕ} {i j k p q r : Fin v}
    (h : label i + label j + label k = label p + label q + label r) :
    ({i, j, k} : Multiset (Fin v)) = {p, q, r} := by
  have hi := digit_bounds i j k
  have hp := digit_bounds p q r
  have he : (index i + index j + index k) +
      (base v : ℤ) * (index i ^ 2 + index j ^ 2 + index k ^ 2) +
      (base v : ℤ) ^ 2 * (index i ^ 3 + index j ^ 3 + index k ^ 3) =
      (index p + index q + index r) +
      (base v : ℤ) * (index p ^ 2 + index q ^ 2 + index r ^ 2) +
      (base v : ℤ) ^ 2 * (index p ^ 3 + index q ^ 3 + index r ^ 3) := by
    dsimp [label] at h
    linear_combination h
  obtain ⟨h₁, h₂, h₃⟩ := three_digits_unique (by exact_mod_cast base_pos v)
    hi.1 hi.2.1 hi.2.2 hp.1 hp.2.1 hp.2.2 he
  have hm := multiset_triple_eq_of_moments h₁ h₂ h₃
  have hm' : Multiset.map index ({i, j, k} : Multiset (Fin v)) =
      Multiset.map index {p, q, r} := by simpa using hm
  exact Multiset.map_injective index_injective hm'

/-- Equality of two label sums determines the vertex multiset, with repetitions. -/
theorem two_term_unique {v : ℕ} {i j k l : Fin v}
    (h : label i + label j = label k + label l) :
    ({i, j} : Multiset (Fin v)) = {k, l} := by
  have hm := three_term_unique (i := i) (j := j) (k := i)
    (p := k) (q := l) (r := i) (by omega)
  exact add_right_cancel
    (show ({i, j} : Multiset (Fin v)) + {i} = {k, l} + {i} from hm)

/-- A nonzero ordered difference of labels uniquely determines its ordered vertex pair. -/
theorem ordered_difference_unique {v : ℕ} {i j k l : Fin v} (hne : i ≠ j)
    (h : label i - label j = label k - label l) : i = k ∧ j = l := by
  have hm := three_term_unique (i := i) (j := l) (k := i)
    (p := k) (q := j) (r := i) (by linarith)
  have hp : ({i, l} : Multiset (Fin v)) = {k, j} := by
    exact add_right_cancel (show ({i, l} : Multiset (Fin v)) + {i} = {k, j} + {i} from hm)
  have hi : i = k ∨ i = j := by
    have : i ∈ ({k, j} : Multiset (Fin v)) := hp ▸ (by simp)
    simpa using this
  have hik : i = k := hi.resolve_right hne
  subst k
  have hjl : l = j := by
    have hp' : ({i} : Multiset (Fin v)) + {l} = {i} + {j} := hp
    have : ({l} : Multiset (Fin v)) = {j} := add_left_cancel hp'
    simpa using this
  exact ⟨rfl, hjl.symm⟩

/-- The maximum source-label formula, also defined at an empty graph. -/
def labelBound (v : ℕ) : ℤ :=
  (v : ℤ) + (base v : ℤ) * (v : ℤ) ^ 2 + (base v : ℤ) ^ 2 * (v : ℤ) ^ 3

/-- For a nonempty source, `A₀` is the label at the last vertex. -/
theorem labelBound_eq_last {v : ℕ} (hv : 0 < v) :
    labelBound v = label (⟨v - 1, by omega⟩ : Fin v) := by
  have hi : index (⟨v - 1, by omega⟩ : Fin v) = (v : ℤ) := by
    dsimp [index]
    omega
  simp only [labelBound, label, hi]

/-- Every label is bounded by the value of the label polynomial at `v`. -/
theorem label_le_bound {v : ℕ} (i : Fin v) : label i ≤ labelBound v := by
  have hi := index_le i
  have hi0 : 0 ≤ index i := le_of_lt (index_pos i)
  have hb : 0 ≤ (base v : ℤ) := by positivity
  dsimp [label, labelBound]
  gcongr

/-- The no-carry base is polynomially bounded. -/
theorem base_le {v : ℕ} (hv : 1 ≤ v) : base v ≤ 4 * v ^ 3 := by
  have hv3 : 1 ≤ v ^ 3 := one_le_pow₀ hv
  unfold base
  omega

/-- The source labels have the explicit ninth-degree bound from the audit. -/
theorem labelBound_le {v : ℕ} (hv : 1 ≤ v) : labelBound v ≤ 21 * (v : ℤ) ^ 9 := by
  have hv' : 1 ≤ (v : ℤ) := by exact_mod_cast hv
  have hb : (base v : ℤ) ≤ 4 * (v : ℤ) ^ 3 := by exact_mod_cast base_le hv
  have hb0 : 0 ≤ (base v : ℤ) := by positivity
  have hpoly : labelBound v ≤ (v : ℤ) + 4 * (v : ℤ) ^ 5 + 16 * (v : ℤ) ^ 9 := by
    calc
      _ ≤ (v : ℤ) + (4 * (v : ℤ) ^ 3) * (v : ℤ) ^ 2 +
          (4 * (v : ℤ) ^ 3) ^ 2 * (v : ℤ) ^ 3 := by
        dsimp [labelBound]
        gcongr
      _ = _ := by ring
  have h₁ : (v : ℤ) ≤ (v : ℤ) ^ 9 := by
    simpa using pow_le_pow_right₀ hv' (show 1 ≤ 9 by omega)
  have h₅ : (v : ℤ) ^ 5 ≤ (v : ℤ) ^ 9 := pow_le_pow_right₀ hv' (by omega)
  linarith

/-- The graph's positive edge differences. -/
noncomputable def edgeDifferences {v : ℕ} (Γ : SimpleGraph (Fin v)) : Finset ℤ :=
  edgeDifferencesOf label Γ

/-- A direct polynomial cardinal bound for the allowed difference set. -/
theorem edgeDifferences_card_le {v : ℕ} (Γ : SimpleGraph (Fin v)) :
    (edgeDifferences Γ).card ≤ v * v := by
  classical
  unfold edgeDifferences edgeDifferencesOf
  exact le_trans Finset.card_image_le (le_trans (Finset.card_filter_le _ _)
    (by simp))

/-- Every allowed edge difference is strictly positive and bounded by `labelBound v`. -/
theorem edgeDifference_bounds {v : ℕ} (Γ : SimpleGraph (Fin v)) {d : ℤ}
    (hd : d ∈ edgeDifferences Γ) : 0 < d ∧ d ≤ labelBound v := by
  obtain ⟨i, j, hij, rfl⟩ := (mem_edgeDifferencesOf label Γ d).mp hd
  have hne : label i ≠ label j := fun h => hij.ne (label_injective h)
  have hi := label_pos i
  have hj := label_pos j
  have hi' := label_le_bound i
  have hj' := label_le_bound j
  constructor
  · exact abs_pos.mpr (sub_ne_zero.mpr hne)
  · exact (abs_le).mpr ⟨by omega, by omega⟩

/-- Lemma 1, with the explicit cubic labels and no unproved uniqueness assumptions.
The stronger lower bound two includes the two-point edge case. -/
theorem difference_clique_extraction {v : ℕ} (Γ : SimpleGraph (Fin v))
    {P : Finset ℤ} (hcard : 2 ≤ P.card)
    (hP : PositiveDifferences P (edgeDifferences Γ)) :
    ∃ C : Finset (Fin v), ∃ t ε : ℤ, (ε = -1 ∨ ε = 1) ∧
      Γ.IsClique (C : Set (Fin v)) ∧
      P = C.image (fun i => t + ε * label i) ∧ P.card = C.card ∧ C.card ≤ v := by
  simpa only [Fintype.card_fin] using difference_clique_extraction_of_unique label Γ
    label_injective (fun _ _ _ _ _ _ h => three_term_unique h)
    (fun _ _ _ _ hne h => ordered_difference_unique hne h) hcard hP

/-- A source clique yields equally many allowed positions anchored at zero. -/
theorem clique_positions {v : ℕ} (Γ : SimpleGraph (Fin v))
    {C : Finset (Fin v)} (hC : Γ.IsClique (C : Set (Fin v)))
    {b : Fin v} (hb : b ∈ C) :
    ∃ P : Finset ℤ, 0 ∈ P ∧ P.card = C.card ∧
      PositiveDifferences P (edgeDifferences Γ) ∧
      ∀ p ∈ P, |p| ≤ labelBound v := by
  classical
  let P := C.image (fun i => -label b + label i)
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨b, hb, by ring⟩
  · apply Finset.card_image_of_injective
    simpa only [one_mul] using affine_label_injective label_injective
      (-label b) 1 (Or.inr rfl)
  · simpa only [P, edgeDifferences, one_mul] using positiveDifferences_of_clique label Γ hC
      (-label b) 1 (Or.inr rfl)
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    have hi := label_pos i
    have hb' := label_pos b
    have hi' := label_le_bound i
    have hb'' := label_le_bound b
    exact abs_le.mpr ⟨by omega, by omega⟩

/-- A nonempty clique has an anchored realization in the interval `[0,A₀]`.
Choosing its least vertex removes the translation ambiguity in the converse construction. -/
theorem clique_positions_nonneg {v : ℕ} (Γ : SimpleGraph (Fin v))
    {C : Finset (Fin v)} (hC : Γ.IsClique (C : Set (Fin v))) (hne : C.Nonempty) :
    ∃ P : Finset ℤ, 0 ∈ P ∧ P.card = C.card ∧
      PositiveDifferences P (edgeDifferences Γ) ∧
      ∀ p ∈ P, 0 ≤ p ∧ p ≤ labelBound v := by
  classical
  let b := C.min' hne
  have hb : b ∈ C := Finset.min'_mem C hne
  let P := C.image (fun i => -label b + label i)
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨b, hb, by ring⟩
  · apply Finset.card_image_of_injective
    simpa only [one_mul] using affine_label_injective label_injective
      (-label b) 1 (Or.inr rfl)
  · simpa only [P, edgeDifferences, one_mul] using positiveDifferences_of_clique label Γ hC
      (-label b) 1 (Or.inr rfl)
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    have hbi : b ≤ i := Finset.min'_le C i hi
    have hlabel := label_strictMono.monotone hbi
    have hbpos := label_pos b
    have hibound := label_le_bound i
    constructor <;> omega

/-- Empty positions extract to the empty clique, including an empty graph. -/
theorem empty_positions {v : ℕ} (Γ : SimpleGraph (Fin v)) :
    Γ.IsClique (∅ : Set (Fin v)) ∧
      (∅ : Finset ℤ) = (∅ : Finset (Fin v)).image (fun i => label i) := by
  exact ⟨Γ.isClique_empty, by simp⟩

/-- A singleton position is a translate of one label when the source graph is nonempty. -/
theorem singleton_positions {v : ℕ} (Γ : SimpleGraph (Fin v))
    (hv : 0 < v) (p : ℤ) :
    ∃ C : Finset (Fin v), ∃ t : ℤ, Γ.IsClique (C : Set (Fin v)) ∧
      ({p} : Finset ℤ) = C.image (fun i => t + label i) ∧ C.card = 1 := by
  classical
  let b : Fin v := ⟨0, hv⟩
  refine ⟨{b}, p - label b, ?_, ?_, by simp⟩
  · intro i hi j hj hij
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hi hj
    exact False.elim (hij (hi.trans hj.symm))
  · simp

/-- The exact difference-set interface used to combine Lemma 1 with the spin gadget. -/
theorem clique_iff_positions {v h : ℕ} (Γ : SimpleGraph (Fin v)) (hh : 2 ≤ h) :
    (∃ C : Finset (Fin v), h ≤ C.card ∧ Γ.IsClique (C : Set (Fin v))) ↔
      ∃ P : Finset ℤ, h ≤ P.card ∧
        PositiveDifferences P (edgeDifferences Γ) ∧ 0 ∈ P := by
  constructor
  · rintro ⟨C, hc, hC⟩
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
    obtain ⟨P, hp, hpc, hd, _⟩ := clique_positions Γ hC hb
    exact ⟨P, by omega, hd, hp⟩
  · rintro ⟨P, hc, hP, _⟩
    obtain ⟨C, _, _, _, hC, _, hpc, _⟩ :=
      difference_clique_extraction Γ (by omega) hP
    exact ⟨C, by omega, hC⟩

end Power2IdealSVP.Source
