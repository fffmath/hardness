import Power2IdealSVP.Source.RowColumn
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Difference-clique extraction for labels with unique triple sums

The graph argument is separated from the arithmetic choice of labels. The hypotheses below
are ordinary properties of a label function; `Labels.lean` supplies their proofs
for the paper's explicit base-polynomial labels.
Paper: `paper/power2-ideal-svp.pdf`, Section 1.1, Lemma 1.
-/

namespace Power2IdealSVP.Source

/-- Every positive difference between two members of `P` belongs to `D`. -/
def PositiveDifferences (P D : Finset ℤ) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, x < y → y - x ∈ D

/-- The positive edge differences of an integer-labelled finite simple graph. -/
noncomputable def edgeDifferencesOf {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → ℤ) (Γ : SimpleGraph V) : Finset ℤ := by
  classical
  exact ((Finset.univ.product Finset.univ).filter fun p => Γ.Adj p.1 p.2).image
    (fun p => |a p.1 - a p.2|)

/-- Membership in the difference set records an actual graph edge. -/
theorem mem_edgeDifferencesOf {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → ℤ) (Γ : SimpleGraph V) (d : ℤ) :
    d ∈ edgeDifferencesOf a Γ ↔ ∃ i j, Γ.Adj i j ∧ d = |a i - a j| := by
  classical
  constructor
  · intro hd
    obtain ⟨⟨i, j⟩, hij, he⟩ := Finset.mem_image.mp hd
    exact ⟨i, j, (Finset.mem_filter.mp hij).2, he.symm⟩
  · rintro ⟨i, j, hij, hd⟩
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨by simp, hij⟩, hd.symm⟩

/-- Distinct points with allowed differences have an oriented edge representation. -/
theorem exists_edge_difference {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → ℤ) (Γ : SimpleGraph V) {P : Finset ℤ}
    (hP : PositiveDifferences P (edgeDifferencesOf a Γ))
    {x y : ℤ} (hx : x ∈ P) (hy : y ∈ P) (hne : x ≠ y) :
    ∃ i j, Γ.Adj i j ∧ x - y = a i - a j := by
  have habs : |x - y| ∈ edgeDifferencesOf a Γ := by
    rcases lt_or_gt_of_ne hne with h | h
    · simpa [abs_of_neg (sub_neg.mpr h)] using hP x hx y hy h
    · simpa [abs_of_pos (sub_pos.mpr h)] using hP y hy x hx h
  obtain ⟨i, j, hij, hd⟩ := (mem_edgeDifferencesOf a Γ _).mp habs
  rcases abs_eq_abs.mp hd with h | h
  · exact ⟨i, j, hij, h⟩
  · refine ⟨j, i, hij.symm, ?_⟩
    omega

/-- The multiset cancellation step in the label argument, including repeated indices. -/
theorem share_coordinate_of_triple_unique {V : Type*}
    (a : V → ℤ)
    (hu : ∀ i j k p q r, a i + a j + a k = a p + a q + a r →
      ({i, j, k} : Multiset V) = {p, q, r})
    {i j k l p q : V} (hij : i ≠ j) (hkl : k ≠ l)
    (hd : (a i - a j) - (a k - a l) = a p - a q) :
    i = k ∨ j = l := by
  classical
  by_cases hik : i = k
  · exact Or.inl hik
  · have hs := hu i l q j k p (by omega)
    have hi : i ∈ ({j, k, p} : Multiset V) := by
      rw [← hs]
      simp
    have hip : i = p := by
      simpa [hij, hik] using hi
    subst p
    have hc := congrArg (fun s : Multiset V => s.erase i) hs
    have hc' : ({l, q} : Multiset V) = {j, k} := by
      simpa [Ne.symm hij, Ne.symm hik] using hc
    have hl : l ∈ ({j, k} : Multiset V) := by
      rw [← hc']
      simp
    exact Or.inr (by simpa [Ne.symm hkl] using hl : l = j).symm

/-- A row or column representation of the anchored differences gives a translate or
reflection of a subset of source labels. The statement covers two-point sets as well. -/
theorem translate_reflect_of_differences {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → ℤ) (Γ : SimpleGraph V)
    (hu : ∀ i j k p q r, a i + a j + a k = a p + a q + a r →
      ({i, j, k} : Multiset V) = {p, q, r})
    {P : Finset ℤ} (hcard : 2 ≤ P.card)
    (hP : PositiveDifferences P (edgeDifferencesOf a Γ)) :
    ∃ C : Finset V, ∃ t ε : ℤ, (ε = -1 ∨ ε = 1) ∧
      P = C.image (fun i => t + ε * a i) := by
  classical
  obtain ⟨p₀, hp₀⟩ := Finset.card_pos.mp (by omega : 0 < P.card)
  let Q := P.erase p₀
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    dsimp [Q]
    rw [Finset.card_erase_of_mem hp₀]
    omega
  let : Nonempty Q := hQ.to_subtype
  have hrep (x : Q) : ∃ i j, Γ.Adj i j ∧ (x : ℤ) - p₀ = a i - a j := by
    have hx := Finset.mem_erase.mp x.property
    exact exists_edge_difference a Γ hP hx.2 hp₀ hx.1
  choose r s hrs heq using hrep
  have hcompat (x y : Q) : r x = r y ∨ s x = s y := by
    by_cases hxy : x = y
    · simp [hxy]
    · have hval : (x : ℤ) ≠ y := fun h => hxy (Subtype.ext h)
      obtain ⟨i, j, _, hij⟩ := exists_edge_difference a Γ hP
        (Finset.mem_of_mem_erase x.property) (Finset.mem_of_mem_erase y.property) hval
      exact share_coordinate_of_triple_unique a hu (hrs x).ne (hrs y).ne
        (by rw [← heq x, ← heq y]; omega :
          (a (r x) - a (s x)) - (a (r y) - a (s y)) = a i - a j)
  have image_eq (b : V) (f : Q → V) (t ε : ℤ)
      (hb : p₀ = t + ε * a b)
      (hf : ∀ x : Q, (x : ℤ) = t + ε * a (f x)) :
      P = (insert b (Finset.univ.image f)).image (fun i => t + ε * a i) := by
    ext x
    constructor
    · intro hx
      apply Finset.mem_image.mpr
      by_cases hxp : x = p₀
      · exact ⟨b, Finset.mem_insert_self _ _, hxp.trans hb |>.symm⟩
      · let q : Q := ⟨x, Finset.mem_erase.mpr ⟨hxp, hx⟩⟩
        exact ⟨f q, Finset.mem_insert_of_mem (Finset.mem_image_of_mem f
          (Finset.mem_univ q)), (hf q).symm⟩
    · rintro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rwa [← hb]
      · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hi
        rw [← hf q]
        exact Finset.mem_of_mem_erase q.property
  rcases exists_row_or_column (fun x => (r x, s x)) hcompat with ⟨b, hb⟩ | ⟨b, hb⟩
  · refine ⟨insert b (Finset.univ.image s), p₀ + a b, -1, Or.inl rfl, ?_⟩
    apply image_eq
    · ring
    · intro x
      have hx := heq x
      have hbx : r x = b := hb x
      rw [hbx] at hx
      omega
  · refine ⟨insert b (Finset.univ.image r), p₀ - a b, 1, Or.inr rfl, ?_⟩
    apply image_eq
    · ring
    · intro x
      have hx := heq x
      have hbx : s x = b := hb x
      rw [hbx] at hx
      omega

/-- Translation and multiplication by either sign preserve injectivity of the labels. -/
theorem affine_label_injective {V : Type*} {a : V → ℤ} (ha : Function.Injective a)
    (t ε : ℤ) (hε : ε = -1 ∨ ε = 1) : Function.Injective (fun i => t + ε * a i) := by
  intro i j hij
  apply ha
  rcases hε with rfl | rfl <;> simp only [neg_one_mul, one_mul] at hij <;> omega

/-- Ordered-difference uniqueness recovers adjacency from an allowed label difference. -/
theorem edge_of_allowed_difference {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → ℤ) (Γ : SimpleGraph V)
    (hu : ∀ i j k l, i ≠ j → a i - a j = a k - a l → i = k ∧ j = l)
    {i j : V} (hij : i ≠ j) (hd : |a i - a j| ∈ edgeDifferencesOf a Γ) :
    Γ.Adj i j := by
  obtain ⟨k, l, hkl, he⟩ := (mem_edgeDifferencesOf a Γ _).mp hd
  rcases abs_eq_abs.mp he with he | he
  · obtain ⟨rfl, rfl⟩ := hu i j k l hij he
    exact hkl
  · obtain ⟨rfl, rfl⟩ := hu i j l k hij (by omega)
    exact hkl.symm

/-- A translate or reflection with allowed differences is the image of a source clique. -/
theorem clique_of_affine_positions {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → ℤ) (Γ : SimpleGraph V) (ha : Function.Injective a)
    (hu : ∀ i j k l, i ≠ j → a i - a j = a k - a l → i = k ∧ j = l)
    {C : Finset V} {t ε : ℤ} (hε : ε = -1 ∨ ε = 1)
    (hP : PositiveDifferences (C.image (fun i => t + ε * a i))
      (edgeDifferencesOf a Γ)) : Γ.IsClique (C : Set V) := by
  intro i hi j hj hij
  have hf := affine_label_injective ha t ε hε
  have hne : t + ε * a i ≠ t + ε * a j := fun h => hij (hf h)
  obtain ⟨k, l, hkl, he⟩ := exists_edge_difference a Γ hP
    (Finset.mem_image_of_mem _ hi) (Finset.mem_image_of_mem _ hj) hne
  rcases hε with rfl | rfl
  · have he' : a j - a i = a k - a l := by omega
    obtain ⟨rfl, rfl⟩ := hu j i k l (Ne.symm hij) he'
    exact hkl.symm
  · have he' : a i - a j = a k - a l := by omega
    obtain ⟨rfl, rfl⟩ := hu i j k l hij he'
    exact hkl

/-- Every translate and reflection of clique labels has allowed positive differences. -/
theorem positiveDifferences_of_clique {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → ℤ) (Γ : SimpleGraph V) {C : Finset V}
    (hC : Γ.IsClique (C : Set V)) (t ε : ℤ) (hε : ε = -1 ∨ ε = 1) :
    PositiveDifferences (C.image (fun i => t + ε * a i)) (edgeDifferencesOf a Γ) := by
  classical
  intro x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  have hij : i ≠ j := by intro he; subst j; omega
  apply (mem_edgeDifferencesOf a Γ _).mpr
  refine ⟨i, j, hC hi hj hij, ?_⟩
  rcases hε with rfl | rfl
  · simp only [neg_one_mul] at *
    rw [abs_of_nonneg (by omega : 0 ≤ a i - a j)]
    omega
  · simp only [one_mul] at *
    rw [abs_of_nonpos (by omega : a i - a j ≤ 0)]
    omega

/-- The full extraction statement for any finite label system with unique triple sums
and ordered differences. The explicit paper labels instantiate both hypotheses. -/
theorem difference_clique_extraction_of_unique {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → ℤ) (Γ : SimpleGraph V) (ha : Function.Injective a)
    (h₃ : ∀ i j k p q r, a i + a j + a k = a p + a q + a r →
      ({i, j, k} : Multiset V) = {p, q, r})
    (h₂ : ∀ i j k l, i ≠ j → a i - a j = a k - a l → i = k ∧ j = l)
    {P : Finset ℤ} (hcard : 2 ≤ P.card)
    (hP : PositiveDifferences P (edgeDifferencesOf a Γ)) :
    ∃ C : Finset V, ∃ t ε : ℤ, (ε = -1 ∨ ε = 1) ∧ Γ.IsClique (C : Set V) ∧
      P = C.image (fun i => t + ε * a i) ∧ P.card = C.card ∧ C.card ≤ Fintype.card V := by
  classical
  obtain ⟨C, t, ε, hε, he⟩ := translate_reflect_of_differences a Γ h₃ hcard hP
  refine ⟨C, t, ε, hε, ?_, he, ?_, Finset.card_le_univ C⟩
  · apply clique_of_affine_positions a Γ ha h₂ hε
    rwa [← he]
  · rw [he]
    exact Finset.card_image_of_injective _ (affine_label_injective ha t ε hε)

end Power2IdealSVP.Source
