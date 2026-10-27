import Power2IdealSVP.Spin.Defs

/-!
# Signed shifts preserve local fields

Paper: `paper/power2-ideal-svp.txt`, Section 1.3; audit Section 7.

Multiplication by a monomial is a signed cyclic permutation. The signs cancel in the
product defining a local field. These statements hold for every multiplier and coefficient
array, without any support or symmetry hypothesis.
-/

namespace Power2IdealSVP.Spin

open Power2ModuleSVP (Coeff coeff_mul_assoc)
open IdealCVP.Cyclotomic

/-- The coefficient at a shifted position has precisely the negacyclic wrap sign. -/
theorem monomial_mul_at {n : ℕ} (e : Fin n) (σ : Coeff n) (j : Fin n) :
    mul (monomial e 1) σ (e + j) =
      (if e.val + j.val < n then 1 else -1) * σ j := by
  have hn : 0 < n := by have := e.isLt; omega
  let : NeZero n := ⟨by omega⟩
  have hinj : Function.Injective (fun j : Fin n => e + j) :=
    fun _ _ h => add_left_cancel h
  have heq : mul (monomial e 1) σ = sparse (fun j : Fin n => e + j)
      (fun j => (if e.val + j.val < n then 1 else -1) * σ j) := by
    funext r
    rw [mul_monomial_left, sparse_apply]
    apply Finset.sum_congr rfl
    intro k _
    have hc : (e.val + k.val) % n = r.val ↔ r = e + k := by
      simp only [Fin.ext_iff, Fin.val_add]
      omega
    simp only [hc, mul_one]
  rw [heq, sparse_at hinj]

/-- A signed cyclic shift commutes with every negacyclic multiplier. -/
theorem mul_monomial_commute {n : ℕ} (e : Fin n) (G σ : Coeff n) :
    mul G (mul (monomial e 1) σ) = mul (monomial e 1) (mul G σ) := by
  have hn : 0 < n := by have := e.isLt; omega
  rw [← coeff_mul_assoc hn, IdealCVP.Cyclotomic.mul_comm G, coeff_mul_assoc hn]

/-- The induced cyclic permutation preserves each signed local field. -/
theorem fieldAt_monomial_mul {n : ℕ} (e : Fin n) (G σ : Coeff n) (j : Fin n) :
    fieldAt G (mul (monomial e 1) σ) (e + j) = fieldAt G σ j := by
  simp only [fieldAt, mul_monomial_commute, monomial_mul_at]
  split_ifs <;> ring

/-- The support of a shifted array is the corresponding cyclic permutation of the support. -/
theorem support_monomial_mul {n : ℕ} (e : Fin n) (σ : Coeff n) :
    support (mul (monomial e 1) σ) = (support σ).image (fun j => e + j) := by
  classical
  have hn : 0 < n := by have := e.isLt; omega
  let : NeZero n := ⟨by omega⟩
  ext r
  obtain ⟨j, rfl⟩ := (Equiv.addLeft e).surjective r
  simp only [Equiv.coe_addLeft]
  simp only [mem_support, monomial_mul_at, Finset.mem_image]
  constructor
  · intro hj
    refine ⟨j, ?_, rfl⟩
    intro hz
    simp [hz] at hj
  · rintro ⟨k, hk, hkj⟩
    have hkj' : k = j := add_left_cancel hkj
    subst k
    have hj := hk
    split_ifs <;> simpa using hj

/-- Signed shifts preserve support cardinality, in particular its parity. -/
theorem card_support_monomial_mul {n : ℕ} (e : Fin n) (σ : Coeff n) :
    (support (mul (monomial e 1) σ)).card = (support σ).card := by
  rw [support_monomial_mul]
  apply Finset.card_image_of_injective
  have hn : 0 < n := by have := e.isLt; omega
  let : NeZero n := ⟨by omega⟩
  exact fun _ _ h => add_left_cancel h

/-- A signed cyclic shift preserves ternary coefficients. -/
theorem Ternary.monomial_mul {n : ℕ} {σ : Coeff n} (hσ : Ternary σ) (e : Fin n) :
    Ternary (mul (monomial e 1) σ) := by
  have hn : 0 < n := by have := e.isLt; omega
  let : NeZero n := ⟨by omega⟩
  intro r
  obtain ⟨j, rfl⟩ := (Equiv.addLeft e).surjective r
  simp only [Equiv.coe_addLeft]
  rw [monomial_mul_at]
  rcases hσ j with hj | hj | hj <;> split_ifs <;> simp [hj]

/-- A cyclic rotation counts all wrapped positions before any unwrapped position. -/
theorem supportRank_monomial_mul_of_no_wrap {n : ℕ} (e : Fin n) (σ : Coeff n)
    (j : Fin n) (hj : e.val + j.val < n) :
    supportRank (mul (monomial e 1) σ) (e + j) =
      ((support σ).filter fun k => n ≤ e.val + k.val).card + supportRank σ j := by
  classical
  have hn : 0 < n := by have := e.isLt; omega
  let : NeZero n := ⟨by omega⟩
  rw [supportRank, support_monomial_mul, Finset.filter_image,
    Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)]
  have heq : (support σ).filter (fun k => e + k < e + j) =
      ((support σ).filter fun k => n ≤ e.val + k.val) ∪
      ((support σ).filter fun k => k < j) := by
    ext k
    have he := e.isLt
    have hk := k.isLt
    have hj' := j.isLt
    by_cases hmem : k ∈ support σ
    · simp only [Finset.mem_filter, Finset.mem_union, hmem, true_and, Fin.lt_def,
        Fin.val_add_eq_ite]
      split_ifs <;> omega
    · simp [hmem]
  have hd : Disjoint ((support σ).filter fun k => n ≤ e.val + k.val)
      ((support σ).filter fun k => k < j) := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    have he := e.isLt
    have hk'' := k.isLt
    have hj' := j.isLt
    simp only [Finset.mem_filter, Fin.lt_def] at hk hk'
    omega
  rw [heq, Finset.card_union_of_disjoint hd]
  rfl

/-- After wrapping, the old rank is the new rank plus the count of unwrapped positions. -/
theorem supportRank_monomial_mul_of_wrap {n : ℕ} (e : Fin n) (σ : Coeff n)
    (j : Fin n) (hj : n ≤ e.val + j.val) :
    supportRank σ j =
      ((support σ).filter fun k => e.val + k.val < n).card +
        supportRank (mul (monomial e 1) σ) (e + j) := by
  classical
  have hn : 0 < n := by have := e.isLt; omega
  let : NeZero n := ⟨by omega⟩
  rw [supportRank, supportRank, support_monomial_mul, Finset.filter_image,
    Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h)]
  have heq : (support σ).filter (fun k => k < j) =
      ((support σ).filter fun k => e.val + k.val < n) ∪
      ((support σ).filter fun k => e + k < e + j) := by
    ext k
    have he := e.isLt
    have hk := k.isLt
    have hj' := j.isLt
    by_cases hmem : k ∈ support σ
    · simp only [Finset.mem_filter, Finset.mem_union, hmem, true_and, Fin.lt_def,
        Fin.val_add_eq_ite]
      split_ifs <;> omega
    · simp [hmem]
  have hd : Disjoint ((support σ).filter fun k => e.val + k.val < n)
      ((support σ).filter fun k => e + k < e + j) := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    have he := e.isLt
    have hk'' := k.isLt
    have hj' := j.isLt
    simp only [Finset.mem_filter, Fin.lt_def, Fin.val_add_eq_ite] at hk hk'
    split_ifs at hk' <;> omega
  rw [heq, Finset.card_union_of_disjoint hd]

/-- Odd alternation survives a signed cyclic shift, including the changed cut. -/
theorem OddAlternating.monomial_mul {n : ℕ} {σ : Coeff n}
    (hσ : OddAlternating σ) (e : Fin n) : OddAlternating (mul (monomial e 1) σ) := by
  classical
  have hn : 0 < n := by have := e.isLt; omega
  let : NeZero n := ⟨by omega⟩
  let a := ((support σ).filter fun k => e.val + k.val < n).card
  let b := ((support σ).filter fun k => n ≤ e.val + k.val).card
  have hab : a + b = (support σ).card := by
    simpa only [not_lt] using (Finset.card_filter_add_card_filter_not
      (s := support σ) (fun k => e.val + k.val < n))
  have hpow : (-1 : ℤ) ^ a * (-1) ^ b = -1 := by
    rw [← pow_add, hab, hσ.2.1.neg_one_pow]
  obtain ⟨η, hη, he⟩ := hσ.2.2
  refine ⟨hσ.1.monomial_mul e, ?_, η * (-1) ^ b, ?_, ?_⟩
  · simpa only [card_support_monomial_mul] using hσ.2.1
  · rcases hη with rfl | rfl <;>
      rcases neg_one_pow_eq_or ℤ b with hb | hb <;> simp [hb]
  · intro r hr
    obtain ⟨j, rfl⟩ := (Equiv.addLeft e).surjective r
    simp only [Equiv.coe_addLeft] at hr ⊢
    have hj : j ∈ support σ := by
      rw [support_monomial_mul] at hr
      obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hr
      have : k = j := add_left_cancel heq
      simpa only [this] using hk
    rw [monomial_mul_at, he j hj]
    by_cases hw : e.val + j.val < n
    · rw [ite_eq_left hw, supportRank_monomial_mul_of_no_wrap e σ j hw, pow_add]
      change 1 * (η * (-1) ^ supportRank σ j) =
        η * (-1) ^ b * ((-1) ^ b * (-1) ^ supportRank σ j)
      have hb : (-1 : ℤ) ^ b * (-1) ^ b = 1 := by
        rcases neg_one_pow_eq_or ℤ b with hb | hb <;> simp [hb]
      calc
        _ = η * (1 * (-1) ^ supportRank σ j) := by ring
        _ = η * ((-1) ^ b * (-1) ^ b) * (-1) ^ supportRank σ j := by rw [hb]; ring
        _ = _ := by ring
    · rw [ite_eq_right hw]
      have hrank := supportRank_monomial_mul_of_wrap e σ j (by omega)
      change supportRank σ j = a + _ at hrank
      rw [hrank, pow_add]
      have hp : (-1 : ℤ) ^ b = -(-1) ^ a := by
        rcases neg_one_pow_eq_or ℤ a with ha | ha <;>
          rcases neg_one_pow_eq_or ℤ b with hb | hb <;> simp_all
      rw [hp]
      ring

/-- All active-field inequalities survive a signed monomial shift. -/
theorem active_fields_monomial_mul_iff {n : ℕ} (e : Fin n) (G σ : Coeff n) (t : ℤ) :
    (∀ i ∈ support (mul (monomial e 1) σ), t ≤ fieldAt G (mul (monomial e 1) σ) i) ↔
      ∀ i ∈ support σ, t ≤ fieldAt G σ i := by
  constructor
  · intro ht j hj
    have hs : e + j ∈ support (mul (monomial e 1) σ) := by
      rw [support_monomial_mul]
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    simpa only [fieldAt_monomial_mul] using ht (e + j) hs
  · intro ht i hi
    rw [support_monomial_mul] at hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    simpa only [fieldAt_monomial_mul] using ht j hj

/-- Signed shifts preserve the finite minimum over active fields. -/
theorem spinValue_monomial_mul {n : ℕ} (e : Fin n) (G σ : Coeff n)
    (hσ : OddAlternating σ) : spinValue G (mul (monomial e 1) σ) = spinValue G σ := by
  apply le_antisymm
  · apply (le_spinValue_iff hσ _).mpr
    exact (active_fields_monomial_mul_iff e G σ _).mp
      ((le_spinValue_iff (hσ.monomial_mul e) _).mp le_rfl)
  · apply (le_spinValue_iff (hσ.monomial_mul e) _).mpr
    exact (active_fields_monomial_mul_iff e G σ _).mpr
      ((le_spinValue_iff hσ _).mp le_rfl)

end Power2IdealSVP.Spin
