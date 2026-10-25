import Power2ModuleSVP.Source.Sidon.Encoding

/-!
# Correctness of the sparse affine source (`prop:sidon-source`)

All finite row-isolation claims are proved from the reused quadratic Sidon
uniqueness theorems. The main theorem `affine_correct` has no unproved
hypotheses. The explicit row interface is also exposed for reuse.

Paper: `paper/power2svp.pdf`, Section 4 (Proposition 2 and Lemmas 5–6).
-/
namespace Power2ModuleSVP
namespace SparseEncoding
noncomputable section
open Polynomial
open scoped BigOperators
set_option maxHeartbeats 800000

/-- Which input variables contribute to an ordinary product coefficient. -/
def rowIndices {v r : ℕ} (C : Clauses v r) (ell z : ℕ) : Finset (Fin v) :=
  Finset.univ.filter fun i => Sidon.position ell i ≤ z ∧
    z - Sidon.position ell i ∈ support C ell

/-- A cluster is strictly above every input position and below the midpoint. -/
theorem cluster_bounds {ell v r : ℕ} (j : Fin (2*r)) :
    B ell v < cluster ell v j.val ∧ cluster ell v j.val ≤ 2*r*delta ell v := by
  have hd : delta ell v = 4*B ell v+1 := rfl
  have h1 := Nat.mul_le_mul_right (delta ell v) (show 1 ≤ j.val+1 by omega)
  have h2 := Nat.mul_le_mul_right (delta ell v) (show j.val+1 ≤ 2*r by omega)
  dsimp [cluster]
  constructor <;> omega

/-- Distinct clusters are separated by more than the total input range. -/
theorem cluster_isolation {ell v r : ℕ} {j k : Fin (2*r)} {a b : ℕ}
    (ha : a ≤ B ell v) (hb : b ≤ B ell v)
    (he : cluster ell v j.val + a = cluster ell v k.val + b) : j = k := by
  have hd : delta ell v = 4*B ell v+1 := rfl
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm := Nat.mul_le_mul_right (delta ell v) (show j.val+2 ≤ k.val+1 by omega)
    dsimp [cluster] at he
    nlinarith
  · have hm := Nat.mul_le_mul_right (delta ell v) (show k.val+2 ≤ j.val+1 by omega)
    dsimp [cluster] at he
    nlinarith

/-- The central coefficient reads exactly the variables of the clause.
This part of row isolation needs only monotonicity, not the Sidon property. -/
theorem center_row {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell)
    (j : Fin (2*r)) : rowIndices C ell (cluster ell v j.val) = C (originalRow j) := by
  ext k
  have hak := Sidon.position_le_bound hell k
  have hcb := cluster_bounds (ell := ell) (v := v) j
  have hlow : Sidon.position ell k ≤ cluster ell v j.val := by
    dsimp [B] at *
    omega
  simp only [rowIndices, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right hlow]
  constructor
  · intro h
    simp only [support, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image] at h
    rcases h with ((hz | ht) | hl) | ⟨a,ha,he⟩
    · dsimp [B] at *
      omega
    · have hlarge : 2*r*delta ell v < T ell v r := by
        unfold T
        have hd : 0 < delta ell v := by unfold delta; positivity
        exact Nat.mul_lt_mul_of_pos_right (by omega) hd
      omega
    · obtain ⟨jj,_,hl⟩ := Finset.mem_biUnion.mp hl
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hl
      have hai := Sidon.position_le_bound hell i
      have hcbi := cluster_bounds (ell := ell) (v := v) jj
      have hei : cluster ell v j.val + Sidon.position ell i =
          cluster ell v jj.val + Sidon.position ell k := by
        dsimp [B] at *
        omega
      have hjj := cluster_isolation hai hak hei
      subst jj
      have hki : k = i := (Sidon.strictMono hell).injective (by omega)
      simpa [hki] using hi
    · have hb := (lower_bounds C hell ha).2
      have hlarge : 2*r*delta ell v + 2*r*delta ell v < T ell v r := by
        unfold T
        have hd : 0 < delta ell v := by unfold delta; positivity
        nlinarith
      omega
  · intro hk
    unfold support
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨k,hk,rfl⟩⟩

/-- An individual contribution records its support family and source clause. -/
inductive RowOrigin {v r : ℕ} (C : Clauses v r) (ell z : ℕ) (i : Fin v) : Prop
  | low (h : z = Sidon.position ell i)
  | high (h : z = T ell v r + Sidon.position ell i)
  | lower (j : Fin (2*r)) (a : Fin v) (ha : a ∈ C (originalRow j))
      (h : z = cluster ell v j.val - Sidon.position ell a + Sidon.position ell i)
  | upper (j : Fin (2*r)) (a : Fin v) (ha : a ∈ C (originalRow j))
      (h : z = T ell v r - cluster ell v j.val + Sidon.position ell a + Sidon.position ell i)

theorem row_origin {v r : ℕ} (C : Clauses v r) {ell z : ℕ} (hell : 0 < ell)
    {i : Fin v} (hi : i ∈ rowIndices C ell z) : RowOrigin C ell z i := by
  obtain ⟨_,hiz,hs⟩ := Finset.mem_filter.mp hi
  simp only [support, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image] at hs
  rcases hs with ((hs | hs) | hs) | ⟨a,ha,he⟩
  · exact .low (by omega)
  · exact .high (by omega)
  · obtain ⟨j,_,hs⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hs
    exact .lower j a ha (by omega)
  · obtain ⟨j,_,himg⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨aa,hclause,hexponent⟩ := Finset.mem_image.mp himg
    have hcb := cluster_bounds (ell := ell) (v := v) j
    have haa := Sidon.position_le_bound hell aa
    have hT : 2*r*delta ell v < T ell v r := by
      unfold T
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by unfold delta; positivity)
    exact .upper j aa hclause (by dsimp [B] at *; omega)

/-- A row's families occupy disjoint ranges. This formulation also identifies
which duplicate clause can occur in each non-guard family. -/
theorem origin_ranges {v r : ℕ} (C : Clauses v r) {ell z : ℕ} (hell : 0 < ell)
    {i : Fin v} (hi : RowOrigin C ell z i) :
    (z ≤ B ell v ∧ z = Sidon.position ell i) ∨
    (T ell v r < z ∧ z = T ell v r + Sidon.position ell i) ∨
    (∃ j a, a ∈ C (originalRow j) ∧
      z = cluster ell v j.val - Sidon.position ell a + Sidon.position ell i ∧
      cluster ell v j.val - B ell v ≤ z ∧ z ≤ cluster ell v j.val + B ell v ∧
      B ell v < z ∧ z ≤ 2*r*delta ell v+B ell v) ∨
    (∃ j a, a ∈ C (originalRow j) ∧
      z = T ell v r - cluster ell v j.val + Sidon.position ell a + Sidon.position ell i ∧
      T ell v r - cluster ell v j.val ≤ z ∧
      z ≤ T ell v r - cluster ell v j.val + 2*B ell v ∧
      2*r*delta ell v+B ell v < z ∧ z < T ell v r) := by
  have hii := Sidon.position_le_bound hell i
  have hi0 := Sidon.position_pos hell i
  have hd : delta ell v = 4*B ell v+1 := rfl
  have hT : T ell v r = (4*r+1)*delta ell v := rfl
  rcases hi with h | h | ⟨j,a,ha,h⟩ | ⟨j,a,ha,h⟩
  · exact Or.inl ⟨h ▸ hii,h⟩
  · exact Or.inr (Or.inl ⟨by dsimp [B] at *; omega,h⟩)
  · have haa := Sidon.position_le_bound hell a
    have hcb := cluster_bounds (ell := ell) (v := v) j
    have hcl : delta ell v ≤ cluster ell v j.val := by
      unfold cluster
      exact Nat.le_mul_of_pos_left _ (by omega)
    apply Or.inr (Or.inr (Or.inl ?_))
    refine ⟨j,a,ha,h,?_,?_,?_,?_⟩ <;> dsimp [B] at * <;> omega
  · have haa := Sidon.position_le_bound hell a
    have ha0 := Sidon.position_pos hell a
    have hcb := cluster_bounds (ell := ell) (v := v) j
    have hcl : delta ell v ≤ cluster ell v j.val := by
      unfold cluster
      exact Nat.le_mul_of_pos_left _ (by omega)
    have hmid : 2*r*delta ell v + (2*r*delta ell v+B ell v) < T ell v r := by nlinarith
    apply Or.inr (Or.inr (Or.inr ?_))
    refine ⟨j,a,ha,h,?_,?_,?_,?_⟩ <;> dsimp [B] at * <;> omega


/-- Cluster centers within `2B` of each other are equal. -/
theorem nearby_clusters_eq {ell v r : ℕ} {j k : Fin (2*r)}
    (h1 : cluster ell v j.val ≤ cluster ell v k.val + 2*B ell v)
    (h2 : cluster ell v k.val ≤ cluster ell v j.val + 2*B ell v) : j = k := by
  have hd : delta ell v = 4*B ell v+1 := rfl
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm := Nat.mul_le_mul_right (delta ell v) (show j.val+2 ≤ k.val+1 by omega)
    dsimp [cluster] at h1 h2
    nlinarith
  · have hm := Nat.mul_le_mul_right (delta ell v) (show k.val+2 ≤ j.val+1 by omega)
    dsimp [cluster] at h1 h2
    nlinarith

/-- Every contributor to an unreflected row uses the same clause copy. -/
theorem lower_row_contributors {v r : ℕ} (C : Clauses v r) {ell z : ℕ}
    (hell : 0 < ell) (j : Fin (2*r))
    (hz1 : cluster ell v j.val - B ell v ≤ z)
    (hz2 : z ≤ cluster ell v j.val + B ell v)
    (hz3 : B ell v < z) (hz4 : z ≤ 2*r*delta ell v+B ell v)
    {k : Fin v} (hk : k ∈ rowIndices C ell z) :
    ∃ a ∈ C (originalRow j),
      z = cluster ell v j.val - Sidon.position ell a + Sidon.position ell k := by
  have hT : 2*r*delta ell v+B ell v < T ell v r := by
    unfold T delta
    nlinarith
  rcases origin_ranges C hell (row_origin C hell hk) with hl | hh | hl | hh
  · omega
  · omega
  · obtain ⟨jj,a,ha,he,h1,h2,h3,h4⟩ := hl
    have hj := cluster_bounds (ell := ell) (v := v) j
    have hjj := cluster_bounds (ell := ell) (v := v) jj
    have heq : j = jj := nearby_clusters_eq (ell := ell) (v := v) (by omega) (by omega)
    subst jj
    exact ⟨a,ha,he⟩
  · obtain ⟨jj,a,ha,he,h1,h2,h3,h4⟩ := hh
    omega

/-- Every contributor to a reflected row uses the same clause copy. -/
theorem upper_row_contributors {v r : ℕ} (C : Clauses v r) {ell z : ℕ}
    (hell : 0 < ell) (j : Fin (2*r))
    (hz1 : T ell v r - cluster ell v j.val ≤ z)
    (hz2 : z ≤ T ell v r - cluster ell v j.val + 2*B ell v)
    (hz3 : 2*r*delta ell v+B ell v < z) (hz4 : z < T ell v r)
    {k : Fin v} (hk : k ∈ rowIndices C ell z) :
    ∃ a ∈ C (originalRow j),
      z = T ell v r - cluster ell v j.val + Sidon.position ell a + Sidon.position ell k := by
  have hT : 2*r*delta ell v < T ell v r := by
    unfold T
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by unfold delta; positivity)
  rcases origin_ranges C hell (row_origin C hell hk) with hl | hh | hl | hh
  · omega
  · omega
  · obtain ⟨jj,a,ha,he,h1,h2,h3,h4⟩ := hl
    omega
  · obtain ⟨jj,a,ha,he,h1,h2,h3,h4⟩ := hh
    have hj := cluster_bounds (ell := ell) (v := v) j
    have hjj := cluster_bounds (ell := ell) (v := v) jj
    have heq : j = jj := nearby_clusters_eq (ell := ell) (v := v) (by omega) (by omega)
    subst jj
    exact ⟨a,ha,he⟩

/-- The finite row interface, proved by `rowIsolation`. Clause containment is
slightly weaker than the singleton/pair description and suffices for bit bounds. -/
structure RowIsolation {v r : ℕ} (C : Clauses v r) (ell : ℕ) : Prop where
  centers : ∀ j : Fin (2*r), rowIndices C ell (cluster ell v j.val) = C (originalRow j)
  rows : ∀ z, (rowIndices C ell z).card ≤ 1 ∨
    ∃ j, rowIndices C ell z ⊆ C j

/-- Construct the row interface from clause containment and the proved center identity. -/
theorem rowIsolation_of_classification {v r : ℕ} (C : Clauses v r) {ell : ℕ}
    (hell : 0 < ell)
    (h : ∀ z, (rowIndices C ell z).card ≤ 1 ∨ ∃ j, rowIndices C ell z ⊆ C j) :
    RowIsolation C ell := ⟨center_row C hell,h⟩

/-- Row classification from Sidon uniqueness; no row-isolation assumption is needed. -/
theorem rowIsolation {v r : ℕ} (C : Clauses v r) {ell : ℕ}
    (hp : ell.Prime) (ho : 2 < ell) (hv : v < ell) : RowIsolation C ell := by
  refine rowIsolation_of_classification C hp.pos (fun z => ?_)
  by_cases hempty : (rowIndices C ell z).Nonempty
  swap
  · exact Or.inl (by rw [Finset.not_nonempty_iff_eq_empty.mp hempty]; simp)
  obtain ⟨i,hi⟩ := hempty
  have horigin := origin_ranges C hp.pos (row_origin C hp.pos hi)
  rcases horigin with hlow | hhigh | hlower | hupper
  · apply Or.inl
    have hsub : rowIndices C ell z ⊆ {i} := by
      intro k hk
      rcases origin_ranges C hp.pos (row_origin C hp.pos hk) with h | h | h | h
      · have he : Sidon.position ell k = Sidon.position ell i := by omega
        simpa using (Sidon.strictMono hp.pos).injective he
      · have hBT : B ell v < T ell v r := by unfold T delta; nlinarith
        omega
      · obtain ⟨j,a,ha,he,h1,h2,h3,h4⟩ := h
        omega
      · obtain ⟨j,a,ha,he,h1,h2,h3,h4⟩ := h
        have hmid : B ell v ≤ 2*r*delta ell v+B ell v := by omega
        omega
    exact (Finset.card_le_card hsub).trans (by simp)
  · apply Or.inl
    have hsub : rowIndices C ell z ⊆ {i} := by
      intro k hk
      rcases origin_ranges C hp.pos (row_origin C hp.pos hk) with h | h | h | h
      · have hBT : B ell v < T ell v r := by unfold T delta; nlinarith
        omega
      · have he : Sidon.position ell k = Sidon.position ell i := by omega
        simpa using (Sidon.strictMono hp.pos).injective he
      · obtain ⟨j,a,ha,he,h1,h2,h3,h4⟩ := h
        have hmid : 2*r*delta ell v+B ell v < T ell v r := by unfold T delta; nlinarith
        omega
      · obtain ⟨j,a,ha,he,h1,h2,h3,h4⟩ := h
        omega
    exact (Finset.card_le_card hsub).trans (by simp)
  · obtain ⟨j,a,ha,hei,h1,h2,h3,h4⟩ := hlower
    by_cases hzcenter : z = cluster ell v j.val
    · exact Or.inr ⟨originalRow j, by rw [hzcenter,center_row C hp.pos j]⟩
    · apply Or.inl
      have hai : a ≠ i := by
        intro he
        subst a
        have hcb := cluster_bounds (ell := ell) (v := v) j
        have hip := Sidon.position_le_bound hp.pos i
        dsimp [B] at *
        omega
      have hsub : rowIndices C ell z ⊆ {i} := by
        intro k hk
        obtain ⟨b,hb,hek⟩ := lower_row_contributors C hp.pos j h1 h2 h3 h4 hk
        have hbk : b ≠ k := by
          intro he
          subst b
          have hcb := cluster_bounds (ell := ell) (v := v) j
          have hkp := Sidon.position_le_bound hp.pos k
          dsimp [B] at *
          omega
        have haB := Sidon.position_le_bound hp.pos a
        have hbB := Sidon.position_le_bound hp.pos b
        have hcb := cluster_bounds (ell := ell) (v := v) j
        have hdiff : (Sidon.position ell i : ℤ)-Sidon.position ell a =
            (Sidon.position ell k : ℤ)-Sidon.position ell b := by
          dsimp [B] at *
          omega
        have he := Sidon.differences hp ho hv a i b k hai hbk hdiff
        simpa using he.2.symm
      exact (Finset.card_le_card hsub).trans (by simp)
  · obtain ⟨j,a,ha,hei,h1,h2,h3,h4⟩ := hupper
    by_cases hiC : i ∈ C (originalRow j)
    · apply Or.inr
      refine ⟨originalRow j,fun k hk => ?_⟩
      obtain ⟨b,hb,hek⟩ := upper_row_contributors C hp.pos j h1 h2 h3 h4 hk
      have hs : Sidon.position ell a+Sidon.position ell i =
          Sidon.position ell b+Sidon.position ell k := by omega
      rcases Sidon.pair_sums hp ho hv a i b k hs with ⟨_,hik⟩ | ⟨hak,_⟩
      · exact hik ▸ hiC
      · exact hak ▸ ha
    · apply Or.inl
      have hsub : rowIndices C ell z ⊆ {i} := by
        intro k hk
        obtain ⟨b,hb,hek⟩ := upper_row_contributors C hp.pos j h1 h2 h3 h4 hk
        have hs : Sidon.position ell a+Sidon.position ell i =
            Sidon.position ell b+Sidon.position ell k := by omega
        rcases Sidon.pair_sums hp ho hv a i b k hs with ⟨_,hik⟩ | ⟨_,hib⟩
        · simpa using hik.symm
        · exact (hiC (hib.symm ▸ hb)).elim
      exact (Finset.card_le_card hsub).trans (by simp)

/-- Place arbitrary integer coefficients at the Sidon positions. -/
def placed {v : ℕ} (ell : ℕ) (b : Fin v → ℤ) : ℤ[X] :=
  ∑ i : Fin v, monomial (Sidon.position ell i) (b i)

theorem placed_coeff_at {ell v : ℕ} (hell : 0 < ell) (b : Fin v → ℤ) (i : Fin v) :
    (placed ell b).coeff (Sidon.position ell i) = b i := by
  classical
  rw [placed, finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : Sidon.position ell j ≠ Sidon.position ell i :=
      (Sidon.strictMono hell).injective.ne hji
    simp [coeff_monomial, hne]
  · simp

theorem placed_coeff_outside {ell v z : ℕ} (b : Fin v → ℤ)
    (hz : z ∉ positions ell v) : (placed ell b).coeff z = 0 := by
  classical
  rw [placed, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  have hne : Sidon.position ell i ≠ z := by
    intro he
    exact hz (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩)
  simp [coeff_monomial, hne]

theorem placed_degree {ell v : ℕ} (hell : 0 < ell) (b : Fin v → ℤ) :
    (placed ell b).natDegree ≤ B ell v := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro z hz
  apply placed_coeff_outside
  rintro hm
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hm
  have := Sidon.position_le_bound hell i
  exact (not_le.mpr hz) this

/-- Sparse coefficient multiplication is exactly a sum over `rowIndices`. -/
theorem product_placed_coeff {v r : ℕ} (C : Clauses v r) (ell z : ℕ) (b : Fin v → ℤ) :
    (P C ell * placed ell b).coeff z = ∑ i ∈ rowIndices C ell z, b i := by
  classical
  rw [placed, Finset.mul_sum, finsetSum_coeff]
  simp only [rowIndices, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow']
  simp only [coeff_mul_C, coeff_P]
  by_cases hi : Sidon.position ell i ≤ z <;>
    by_cases hs : z - Sidon.position ell i ∈ support C ell <;> simp [hi, hs]

/-- Every supported polynomial is recovered by sampling its Sidon coefficients. -/
theorem eq_placed_of_supported {ell v : ℕ} (hell : 0 < ell) (x : ℤ[X])
    (hx : ∀ z, z ∉ positions ell v → x.coeff z = 0) :
    x = placed ell (fun i : Fin v => x.coeff (Sidon.position ell i)) := by
  ext z
  by_cases hz : z ∈ positions ell v
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    rw [placed_coeff_at hell]
  · rw [hx z hz, placed_coeff_outside _ hz]

/-- Reconstruct a canonical representative from a finite coefficient function. -/
def vectorPolynomial (len : ℕ) (a : ℕ → ℤ) : ℤ[X] :=
  ∑ z ∈ Finset.range len, monomial z (a z)

theorem vectorPolynomial_coeff (len z : ℕ) (a : ℕ → ℤ) :
    (vectorPolynomial len a).coeff z = if z < len then a z else 0 := by
  classical
  simp [vectorPolynomial, coeff_monomial]

theorem vectorPolynomial_bit {len : ℕ} {a : ℕ → ℤ}
    (ha : ∀ z < len, a z = 0 ∨ a z = 1) : BitPolynomial len (vectorPolynomial len a) := by
  constructor
  · apply (degree_lt_iff_coeff_zero _ _).mpr
    intro z hz
    simp [vectorPolynomial_coeff, not_lt.mpr hz]
  · intro z
    rw [vectorPolynomial_coeff]
    split_ifs with h
    · exact ha z h
    · exact Or.inl rfl

theorem odd_center_offset {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell)
    (hC : WellFormed C) (hrows : RowIsolation C ell) (j : Fin r) :
    translation C ell (cluster ell v (2*j.val)) = 0 := by
  have hd : 0 < delta ell v := by unfold delta; positivity
  have hn : cluster ell v (2*j.val) ∉ negativeRows ell v r := by
    intro hn
    obtain ⟨k,_,he⟩ := Finset.mem_image.mp hn
    dsimp [cluster] at he
    have he' := Nat.eq_of_mul_eq_mul_right hd he
    omega
  have hne : (C j).Nonempty := Finset.card_pos.mp (by rw [hC j]; omega)
  obtain ⟨i,hi⟩ := hne
  let jj : Fin (2*r) := ⟨2*j.val, by omega⟩
  have hjj : originalRow jj = j := by apply Fin.ext; simp [originalRow,jj]
  have hri : i ∈ rowIndices C ell (cluster ell v (2*j.val)) := by
    simpa [hrows.centers jj, hjj, jj] using hi
  have ht : cluster ell v (2*j.val) ∈ touched C ell := by
    have hr := Finset.mem_filter.mp hri
    exact Finset.mem_biUnion.mpr ⟨Sidon.position ell i,
      Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
      Finset.mem_image.mpr ⟨_,hr.2.2, Nat.add_sub_of_le hr.2.1⟩⟩
  simp [translation, hn, ht]

theorem even_center_offset {v r : ℕ} (C : Clauses v r) (ell : ℕ) (j : Fin r) :
    translation C ell (cluster ell v (2*j.val+1)) = -1 := by
  have hn : cluster ell v (2*j.val+1) ∈ negativeRows ell v r :=
    Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  simp [translation, hn]

/-- Under row isolation, soundness of the complete quotient equation. -/
theorem affine_sound_of_rows {v r : ℕ} (C : Clauses v r) {ell : ℕ}
    (hell : 0 < ell) (hC : WellFormed C) (hrows : RowIsolation C ell)
    (h : ∃ x y, AffineSolution C ell x y) : Satisfiable C := by
  obtain ⟨x,y,hx,hy,he⟩ := h
  have hpad := encoding_padding C hell ⟨hx,hy,he⟩
  have hplaced := eq_placed_of_supported hell x hpad.1
  let b : Fin v → Bool := fun i => decide (x.coeff (Sidon.position ell i) = 1)
  have hb (i : Fin v) : (if b i then (1 : ℤ) else 0) =
      x.coeff (Sidon.position ell i) := by
    rcases hx.2 (Sidon.position ell i) with h | h <;> simp [b,h]
  refine ⟨b, fun j => ?_⟩
  let jo : Fin (2*r) := ⟨2*j.val, by omega⟩
  let je : Fin (2*r) := ⟨2*j.val+1, by omega⟩
  have hjo : originalRow jo = j := by apply Fin.ext; simp [originalRow,jo]
  have hje : originalRow je = j := by apply Fin.ext; simp [originalRow,je]; omega
  have hcenter (k : Fin (2*r)) : (P C ell*x).coeff (cluster ell v k.val) =
      ∑ i ∈ C (originalRow k), x.coeff (Sidon.position ell i) := by
    conv_lhs => rw [hplaced]
    rw [product_placed_coeff, hrows.centers]
  have hoddL : cluster ell v (2*j.val) < L ell v r := by
    have hmul := Nat.mul_le_mul_right (delta ell v) (show 2*j.val+1 ≤ 2*r by omega)
    have hl := (L_spec ell v r).1
    dsimp [cluster, T] at *
    nlinarith [show 0 < delta ell v by unfold delta; positivity]
  have hevenL : cluster ell v (2*j.val+1) < L ell v r := by
    have hn := negative_bounds (show cluster ell v (2*j.val+1) ∈ negativeRows ell v r from
      Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
    have hl := (L_spec ell v r).1
    omega
  have ho := he _ hoddL
  have hv := he _ hevenL
  rw [hpad.2, odd_center_offset C hell hC hrows j, add_zero] at ho
  rw [hpad.2, even_center_offset C ell j] at hv
  have hco := hcenter jo
  have hce := hcenter je
  simp only [jo, je, hjo, hje] at hco hce
  have yo := hy.2 (cluster ell v (2*j.val))
  have ye := hy.2 (cluster ell v (2*j.val+1))
  simp only [hb]
  rcases yo with yo | yo <;> rcases ye with ye | ye <;> omega

/-- Any represented row is contained in the explicitly computed touched set. -/
theorem touched_of_row_mem {v r : ℕ} (C : Clauses v r) (ell z : ℕ) {i : Fin v}
    (hi : i ∈ rowIndices C ell z) : z ∈ touched C ell := by
  have hr := (Finset.mem_filter.mp hi).2
  exact Finset.mem_biUnion.mpr ⟨Sidon.position ell i,
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
    Finset.mem_image.mpr ⟨_,hr.2,Nat.add_sub_of_le hr.1⟩⟩

/-- Under row isolation, completeness of the bit-vector quotient equation. -/
theorem affine_complete_of_rows {v r : ℕ} (C : Clauses v r) {ell : ℕ}
    (hell : 0 < ell) (hrows : RowIsolation C ell)
    (h : Satisfiable C) : ∃ x y, AffineSolution C ell x y := by
  classical
  obtain ⟨b,hb⟩ := h
  let bits : Fin v → ℤ := fun i => if b i then 1 else 0
  let x := placed ell bits
  have hbits (i : Fin v) : bits i = 0 ∨ bits i = 1 := by
    dsimp [bits]; split_ifs <;> simp
  have hbits0 (i : Fin v) : 0 ≤ bits i := by rcases hbits i with h | h <;> omega
  have hbits1 (i : Fin v) : bits i ≤ 1 := by rcases hbits i with h | h <;> omega
  have hsum : ∀ z, 0 ≤ (P C ell*x).coeff z ∧ (P C ell*x).coeff z ≤ 1 := by
    intro z
    change 0 ≤ (P C ell*placed ell bits).coeff z ∧ _
    rw [product_placed_coeff]
    constructor
    · exact Finset.sum_nonneg fun i _ => hbits0 i
    · rcases hrows.rows z with hs | ⟨j,hj⟩
      · calc
          _ ≤ ∑ _i ∈ rowIndices C ell z, (1 : ℤ) := Finset.sum_le_sum fun i _ => hbits1 i
          _ = ((rowIndices C ell z).card : ℤ) := by simp
          _ ≤ 1 := by exact_mod_cast hs
      · calc
          _ ≤ ∑ i ∈ C j, bits i := Finset.sum_le_sum_of_subset_of_nonneg hj (fun i _ _ => hbits0 i)
          _ = 1 := hb j
  have houtput : ∀ z, (P C ell*x).coeff z + translation C ell z = 0 ∨
      (P C ell*x).coeff z + translation C ell z = 1 := by
    intro z
    by_cases hn : z ∈ negativeRows ell v r
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hn
      have ht := even_center_offset C ell j
      let jj : Fin (2*r) := ⟨2*j.val+1,by omega⟩
      have hjj : originalRow jj = j := by apply Fin.ext; simp [originalRow,jj]; omega
      have he : (P C ell*x).coeff (cluster ell v (2*j.val+1)) = 1 := by
        change (P C ell*placed ell bits).coeff _ = _
        rw [product_placed_coeff]
        have hh := hrows.centers jj
        change rowIndices C ell (cluster ell v (2*j.val+1)) = _ at hh
        rw [hh,hjj]
        exact hb j
      exact Or.inl (by rw [he,ht]; norm_num)
    · by_cases ht : z ∈ touched C ell
      · have hc : translation C ell z = 0 := by simp [translation, hn, ht]
        have hh := hsum z
        rcases (show (P C ell*x).coeff z = 0 ∨ (P C ell*x).coeff z = 1 by omega) with h | h
        · exact Or.inl (by rw [h,hc]; norm_num)
        · exact Or.inr (by rw [h,hc]; norm_num)
      · have hr : rowIndices C ell z = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi
          exact ht (touched_of_row_mem C ell z hi)
        have he : (P C ell*x).coeff z = 0 := by
          change (P C ell*placed ell bits).coeff z = _
          rw [product_placed_coeff,hr,Finset.sum_empty]
        exact Or.inr (by simp [translation,hn,ht,he])
  have hBL : B ell v < L ell v r := by
    have hl := (L_spec ell v r).1
    have hT : B ell v < T ell v r := by unfold T delta; nlinarith
    omega
  have hx : BitPolynomial (L ell v r) x := by
    constructor
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast (placed_degree hell bits).trans_lt hBL)
    · intro z
      by_cases hz : z ∈ positions ell v
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
        change (placed ell bits).coeff _ = 0 ∨ (placed ell bits).coeff _ = 1
        rw [placed_coeff_at hell]
        exact hbits i
      · exact Or.inl (placed_coeff_outside bits hz)
  have hdeg : (P C ell*x).natDegree < L ell v r := by
    have hp := (degree_P C hell).le
    have hx := placed_degree hell bits
    have hm := natDegree_mul_le (p := P C ell) (q := x)
    have hl := (L_spec ell v r).1
    have hT : B ell v < T ell v r := by unfold T delta; nlinarith
    change x.natDegree ≤ B ell v at hx
    omega
  have hmonic : (X^(L ell v r)+P C ell).Monic := monic_X_pow_add
    (degree_le_natDegree.trans_lt (by exact_mod_cast (degree_P C hell).trans_lt (by
      have := (L_spec ell v r).1; omega)))
  have hwdeg : (X^(L ell v r)+P C ell).natDegree = L ell v r :=
    by
      rw [natDegree_add_eq_left_of_natDegree_lt (by
        simpa [degree_P C hell] using (show T ell v r < L ell v r by
          have := (L_spec ell v r).1; omega))]
      simp
  have hrem : (P C ell*x) %ₘ (X^(L ell v r)+P C ell) = P C ell*x := by
    apply (modByMonic_eq_self_iff hmonic).mpr
    apply degree_le_natDegree.trans_lt
    rw [degree_eq_natDegree hmonic.ne_zero,hwdeg]
    exact_mod_cast hdeg
  let out := fun z => (P C ell*x).coeff z + translation C ell z
  refine ⟨x,vectorPolynomial (L ell v r) out,hx,
    vectorPolynomial_bit (fun z _ => houtput z),fun z hz => ?_⟩
  rw [vectorPolynomial_coeff,ite_eq_left hz,hrem]

/-- Correctness factored through the proved row interface. -/
theorem affine_correct_of_rows {v r : ℕ} (C : Clauses v r) {ell : ℕ}
    (hell : 0 < ell) (hC : WellFormed C) (hrows : RowIsolation C ell) :
    Satisfiable C ↔ ∃ x y, AffineSolution C ell x y :=
  ⟨affine_complete_of_rows C hell hrows, affine_sound_of_rows C hell hC hrows⟩

/-- Unconditional semantic correctness of the explicit Sidon affine source. -/
theorem affine_correct {v r : ℕ} (C : Clauses v r) {ell : ℕ}
    (hp : ell.Prime) (ho : 2 < ell) (hv : v < ell) (hC : WellFormed C) :
    Satisfiable C ↔ ∃ x y, AffineSolution C ell x y :=
  affine_correct_of_rows C hp.pos hC (rowIsolation C hp ho hv)

/-- Exact support size, including injectivity and separation of all exponent families. -/
theorem weight_eq {v r : ℕ} (C : Clauses v r) {ell : ℕ} (hell : 0 < ell)
    (hC : WellFormed C) : (support C ell).card = 2+12*r := by
  classical
  let E : Fin (2*r) → Finset ℕ := fun j => (C (originalRow j)).image
    (fun i => cluster ell v j.val-Sidon.position ell i)
  have hdis : (↑(Finset.univ : Finset (Fin (2*r))) : Set (Fin (2*r))).PairwiseDisjoint E := by
    intro j _ k _ hjk
    apply Finset.disjoint_left.mpr
    intro z hzj hzk
    obtain ⟨a,ha,haz⟩ := Finset.mem_image.mp hzj
    obtain ⟨b,hb,hbz⟩ := Finset.mem_image.mp hzk
    have haB := Sidon.position_le_bound hell a
    have hbB := Sidon.position_le_bound hell b
    have hj := cluster_bounds (ell := ell) (v := v) j
    have hk := cluster_bounds (ell := ell) (v := v) k
    have he : cluster ell v j.val + Sidon.position ell b =
        cluster ell v k.val + Sidon.position ell a := by dsimp [B] at *; omega
    exact hjk (cluster_isolation hbB haB he)
  have hcard : ∀ j, (E j).card = 3 := by
    intro j
    dsimp only [E]
    rw [Finset.card_image_of_injOn, hC]
    intro a _ b _ he
    have haB := Sidon.position_le_bound hell a
    have hbB := Sidon.position_le_bound hell b
    have hj := cluster_bounds (ell := ell) (v := v) j
    apply (Sidon.strictMono hell).injective
    dsimp [B] at *
    omega
  have hlower : (lowerSupport C ell).card = 6*r := by
    change (Finset.univ.biUnion E).card = _
    rw [Finset.card_biUnion hdis]
    simp [hcard]
    ring
  have hreflect : ((lowerSupport C ell).image (T ell v r-·)).card = 6*r := by
    rw [Finset.card_image_of_injOn,hlower]
    intro a ha b hb he
    change T ell v r-a = T ell v r-b at he
    have haT := support_bounds C hell (show a ∈ support C ell from
      Finset.mem_union_left _ (Finset.mem_union_right _ ha))
    have hbT := support_bounds C hell (show b ∈ support C ell from
      Finset.mem_union_left _ (Finset.mem_union_right _ hb))
    omega
  have hguards : Disjoint ({0,T ell v r} : Finset ℕ) (lowerSupport C ell) := by
    apply Finset.disjoint_left.mpr
    intro z hz hl
    have hb := lower_bounds C hell hl
    have hT : 2*r*delta ell v < T ell v r := by
      unfold T
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by unfold delta; positivity)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with hz | hz <;> omega
  have hall : Disjoint ({0,T ell v r} ∪ lowerSupport C ell)
      ((lowerSupport C ell).image (T ell v r-·)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hr
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hr
    have hb := lower_bounds C hell ha
    have hT : 2*r*delta ell v+2*r*delta ell v < T ell v r := by
      unfold T
      nlinarith [show 0 < delta ell v by unfold delta; positivity]
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with (hz | hz) | hz
    · omega
    · omega
    · have hh := lower_bounds C hell hz
      omega
  rw [support,Finset.card_union_of_disjoint hall,Finset.card_union_of_disjoint hguards,
    hlower,hreflect,Finset.card_pair (show (0 : ℕ) ≠ T ell v r by have := T_pos ell v r; omega)]
  ring

end
end SparseEncoding
end Power2ModuleSVP
