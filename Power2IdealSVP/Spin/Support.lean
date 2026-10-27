import Power2IdealSVP.Spin.Defs
import Power2IdealSVP.Spin.Geometry

/-!
# Alternating signs on integer supports

Integer configurations are embedded into the coefficient interval only after taking a cut.
The definitions here make the relation between ordinary ranks and coefficient ranks explicit.

Paper: `paper/power2-ideal-svp.txt`, Sections 1.2–1.4; audit Sections 7–9.
-/

namespace Power2IdealSVP.Spin

open Power2ModuleSVP (Coeff)

/-- The ordinary integer representatives of the support in the coefficient interval. -/
def integerSupport {n : ℕ} (σ : Coeff n) : Finset ℤ :=
  (support σ).image fun i => (i.val : ℤ)

/-- Coefficient indices belonging to a prescribed integer support. -/
def indexSet (n : ℕ) (W : Finset ℤ) : Finset (Fin n) :=
  Finset.univ.filter fun i => (i.val : ℤ) ∈ W

/-- Embed an integer support by alternating signs in its increasing order. -/
def embedSupport (n : ℕ) (W : Finset ℤ) (η : ℤ) : Coeff n :=
  alternatingOn (indexSet n W) η

/-- The alternating sign at an integer position, zero off the support. -/
def integerAlternating (W : Finset ℤ) (x : ℤ) : ℤ :=
  if x ∈ W then (-1) ^ (W.filter fun y => y < x).card else 0

/-- Taking integer representatives loses no support positions. -/
theorem card_integerSupport {n : ℕ} (σ : Coeff n) :
    (integerSupport σ).card = (support σ).card := by
  unfold integerSupport
  apply Finset.card_image_of_injective
  intro i j h
  change (i.val : ℤ) = (j.val : ℤ) at h
  exact Fin.ext (by exact_mod_cast h)

/-- Every ordinary support position lies in the coefficient interval. -/
theorem integerSupport_bounds {n : ℕ} {σ : Coeff n} {x : ℤ}
    (hx : x ∈ integerSupport σ) : 0 ≤ x ∧ x < n := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨by omega, by exact_mod_cast i.isLt⟩

/-- Membership at a coefficient index is preserved by the integer representation. -/
@[simp] theorem coe_mem_integerSupport {n : ℕ} (σ : Coeff n) (i : Fin n) :
    (i.val : ℤ) ∈ integerSupport σ ↔ i ∈ support σ := by
  simp only [integerSupport, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, he⟩
    have : j = i := Fin.ext (by exact_mod_cast he)
    simpa only [this] using hj
  · exact fun hi => ⟨i, hi, rfl⟩

/-- Integer supports inside the coefficient interval are recovered by `indexSet`. -/
theorem image_indexSet {n : ℕ} {W : Finset ℤ}
    (hW : ∀ x ∈ W, 0 ≤ x ∧ x < n) :
    (indexSet n W).image (fun i => (i.val : ℤ)) = W := by
  ext x
  simp only [Finset.mem_image, indexSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    have hb := hW x hx
    let i : Fin n := ⟨x.toNat, by omega⟩
    have hi : (i.val : ℤ) = x := Int.toNat_of_nonneg hb.1
    exact ⟨i, hi.symm ▸ hx, hi⟩

/-- The embedding preserves support cardinality when the cut is in the coefficient interval. -/
theorem card_indexSet {n : ℕ} {W : Finset ℤ}
    (hW : ∀ x ∈ W, 0 ≤ x ∧ x < n) : (indexSet n W).card = W.card := by
  calc
    _ = ((indexSet n W).image (fun i => (i.val : ℤ))).card := by
      symm
      apply Finset.card_image_of_injective
      intro i j h
      change (i.val : ℤ) = (j.val : ℤ) at h
      exact Fin.ext (by exact_mod_cast h)
    _ = W.card := congrArg Finset.card (image_indexSet hW)

/-- Coefficient rank and ordinary integer rank agree after embedding. -/
theorem rank_indexSet {n : ℕ} {W : Finset ℤ}
    (hW : ∀ x ∈ W, 0 ≤ x ∧ x < n) (i : Fin n) :
    ((indexSet n W).filter fun j => j < i).card =
      (W.filter fun y => y < (i.val : ℤ)).card := by
  have heq := congrArg (fun S : Finset ℤ => S.filter (fun y => y < (i.val : ℤ)))
    (image_indexSet hW)
  rw [Finset.filter_image] at heq
  have hf : (indexSet n W).filter (fun j => (j.val : ℤ) < (i.val : ℤ)) =
      (indexSet n W).filter (fun j => j < i) := by
    ext j
    simp only [Finset.mem_filter, Fin.lt_def, Nat.cast_lt]
  rw [hf] at heq
  calc
    _ = (((indexSet n W).filter fun j => j < i).image
        (fun j => (j.val : ℤ))).card := by
      symm
      apply Finset.card_image_of_injective
      intro j k h
      change (j.val : ℤ) = (k.val : ℤ) at h
      exact Fin.ext (by exact_mod_cast h)
    _ = _ := congrArg Finset.card heq

/-- The actual coefficient embedding has exactly the ordinary alternating values. -/
theorem embedSupport_apply {n : ℕ} {W : Finset ℤ}
    (hW : ∀ x ∈ W, 0 ≤ x ∧ x < n) (η : ℤ) (i : Fin n) :
    embedSupport n W η i = η * integerAlternating W (i.val : ℤ) := by
  have hm : i ∈ indexSet n W ↔ (i.val : ℤ) ∈ W := by simp [indexSet]
  simp only [embedSupport, alternatingOn, integerAlternating, hm]
  split_ifs
  · rw [rank_indexSet hW]
  · ring

/-- An odd integer support in range gives an actual odd alternating coefficient vector. -/
theorem oddAlternating_embedSupport {n : ℕ} {W : Finset ℤ}
    (hW : ∀ x ∈ W, 0 ≤ x ∧ x < n) (hodd : Odd W.card)
    {η : ℤ} (hη : η = -1 ∨ η = 1) : OddAlternating (embedSupport n W η) := by
  exact oddAlternating_alternatingOn _ (by simpa only [card_indexSet hW] using hodd) hη

/-- The integer support of an embedded odd support is exactly the original support. -/
theorem integerSupport_embedSupport {n : ℕ} {W : Finset ℤ}
    (hW : ∀ x ∈ W, 0 ≤ x ∧ x < n) {η : ℤ} (hη : η = -1 ∨ η = 1) :
    integerSupport (embedSupport n W η) = W := by
  rw [integerSupport, embedSupport, support_alternatingOn _ hη, image_indexSet hW]

/-- Equality of integer representatives is equality of the underlying coefficient supports. -/
theorem support_eq_of_integerSupport_eq {n : ℕ} {σ ρ : Coeff n}
    (he : integerSupport σ = integerSupport ρ) : support σ = support ρ := by
  ext i
  rw [← coe_mem_integerSupport σ i, ← coe_mem_integerSupport ρ i, he]

/-- A sparse spin agrees up to global sign with the embedding of its integer support. -/
theorem OddAlternating.eq_or_eq_neg_embedSupport {n : ℕ} {σ : Coeff n}
    (hσ : OddAlternating σ) :
    σ = embedSupport n (integerSupport σ) 1 ∨
      σ = -embedSupport n (integerSupport σ) 1 := by
  have hb : ∀ x ∈ integerSupport σ, 0 ≤ x ∧ x < n :=
    fun _ hx => integerSupport_bounds hx
  have hodd : Odd (integerSupport σ).card := by
    simpa only [card_integerSupport] using hσ.2.1
  apply hσ.eq_or_eq_neg_of_support_eq (oddAlternating_embedSupport hb hodd (Or.inr rfl))
  apply support_eq_of_integerSupport_eq
  exact (integerSupport_embedSupport hb (Or.inr rfl)).symm

/-- Before a point in a component lie precisely the earlier components and its own prefix. -/
theorem configuration_prefix {P : Finset ℤ} {q x : ℤ} (hq : q ∈ P)
    (hx : x ∈ component q) :
    (configuration P).filter (fun y => y < x) =
      (P.filter fun r => r < q).biUnion component ∪
        (component q).filter (fun y => y < x) := by
  ext y
  simp only [Finset.mem_filter, configuration, Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨⟨r, hr, hyr⟩, hyx⟩
    rcases lt_trichotomy r q with hrq | rfl | hqr
    · exact Or.inl ⟨r, ⟨hr, hrq⟩, hyr⟩
    · exact Or.inr ⟨hyr, hyx⟩
    · have := components_separated hqr hx hyr
      omega
  · rintro (⟨r, ⟨hr, hrq⟩, hyr⟩ | ⟨hyq, hyx⟩)
    · refine ⟨⟨r, hr, hyr⟩, ?_⟩
      have := components_separated hrq hyr hx
      omega
    · exact ⟨⟨q, hq, hyq⟩, hyx⟩

/-- The rank of a component point counts all preceding dimers and the possible trimer. -/
theorem configuration_rank {P : Finset ℤ} (h0 : 0 ∈ P) {q x : ℤ} (hq : q ∈ P)
    (hx : x ∈ component q) :
    ((configuration P).filter fun y => y < x).card =
      2 * (P.filter fun r => r < q).card + (if 0 < q then 1 else 0) +
        ((component q).filter fun y => y < x).card := by
  rw [configuration_prefix hq hx, Finset.card_union_of_disjoint]
  · rw [Finset.card_biUnion]
    · simp_rw [card_component]
      simp [Finset.sum_add_distrib, h0, Nat.mul_comm]
    · intro r hr s hs hrs
      exact components_disjoint hrs
  · apply Finset.disjoint_left.mpr
    intro y hy hyq
    obtain ⟨r, hr, hyr⟩ := Finset.mem_biUnion.mp hy
    have hrq := (Finset.mem_filter.mp hr).2
    have he := components_separated hrq hyr (Finset.mem_filter.mp hyq).1
    omega

/-- The ordinary alternating signs on canonical components have the paper's patterns. -/
theorem integerAlternating_configuration {P : Finset ℤ} (h0 : 0 ∈ P)
    {q x : ℤ} (hq : q ∈ P) (hx : x ∈ component q) :
    integerAlternating (configuration P) x =
      if q < 0 then if x = 16 * q then 1 else -1
      else if q = 0 then if x = 1 then -1 else 1
      else if x = 16 * q + 1 then -1 else 1 := by
  have hxW : x ∈ configuration P := Finset.mem_biUnion.mpr ⟨q, hq, hx⟩
  rw [integerAlternating, ite_eq_left hxW, configuration_rank h0 hq hx]
  have heven : (-1 : ℤ) ^ (2 * (P.filter fun r => r < q).card) = 1 := by
    rw [pow_mul]
    norm_num
  rw [pow_add, pow_add, heven, one_mul]
  unfold component at hx ⊢
  by_cases hqneg : q < 0
  · simp only [hqneg, ite_eq_left] at hx ⊢
    have hqpos : ¬0 < q := by omega
    simp only [hqpos]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · have hf : ({16 * q, 16 * q + 1} : Finset ℤ).filter
          (fun y => y < 16 * q) = ∅ := by ext y; simp; omega
      simp [hf]
    · have hx' := Finset.mem_singleton.mp hx
      subst x
      have hf : ({16 * q, 16 * q + 1} : Finset ℤ).filter
          (fun y => y < 16 * q + 1) = {16 * q} := by ext y; simp; omega
      rw [hf]
      simp [show 16 * q + 1 ≠ 16 * q by omega]
  · by_cases hqzero : q = 0
    · subst q
      simp only [lt_irrefl, ite_eq_left] at hx ⊢
      rcases Finset.mem_insert.mp hx with rfl | hx
      · norm_num [Finset.filter_insert, Finset.filter_singleton]
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · norm_num [Finset.filter_insert, Finset.filter_singleton]
        · have hx' := Finset.mem_singleton.mp hx
          subst x
          norm_num [Finset.filter_insert, Finset.filter_singleton]
    · have hqpos : 0 < q := by omega
      simp only [hqneg, hqzero, hqpos, ite_false, ite_true, pow_one] at hx ⊢
      rcases Finset.mem_insert.mp hx with rfl | hx
      · have hf : ({16 * q + 1, 16 * q + 2} : Finset ℤ).filter
            (fun y => y < 16 * q + 1) = ∅ := by ext y; simp; omega
        rw [hf]
        simp
      · have hx' := Finset.mem_singleton.mp hx
        subst x
        have hf : ({16 * q + 1, 16 * q + 2} : Finset ℤ).filter
            (fun y => y < 16 * q + 2) = {16 * q + 1} := by ext y; simp; omega
        rw [hf]
        simp [show 16 * q + 2 ≠ 16 * q + 1 by omega]

/-- Translating a finite support preserves its rank signs under the translated coordinates. -/
theorem integerAlternating_translate (W : Finset ℤ) (t x : ℤ) :
    integerAlternating (W.image fun y => y + t) (x + t) = integerAlternating W x := by
  classical
  have hinj : Function.Injective (fun y : ℤ => y + t) :=
    fun _ _ h => add_right_cancel h
  have hm : x + t ∈ W.image (fun y => y + t) ↔ x ∈ W := by
    rw [Finset.mem_image]
    exact ⟨fun ⟨y, hy, he⟩ => (add_right_cancel he) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  simp only [integerAlternating, hm]
  split_ifs
  · rw [Finset.filter_image, Finset.card_image_of_injective _ hinj]
    congr 2
    ext y
    simp
  · rfl

end Power2IdealSVP.Spin
