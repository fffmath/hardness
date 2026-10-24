import Rank2ModuleSVP.PrimeCyclotomic

/-! Integral sparsification and the second canonical shell. -/
namespace Rank2ModuleSVP
open scoped BigOperators
noncomputable section
variable {q : ℕ} [NeZero q]

/-- Number of nonzero coordinates. -/
def supportCard (x : Coeff ℤ q) : ℕ := (Finset.univ.filter fun a => x a ≠ 0).card

theorem supportCard_le_sqNorm (x : Coeff ℤ q) : (supportCard x : ℤ) ≤ IdealCVP.sqNorm x := by
  classical
  unfold supportCard IdealCVP.sqNorm
  rw [← Finset.sum_boole]
  apply Finset.sum_le_sum
  intro a _
  split_ifs with h
  · have : x a ≤ -1 ∨ 1 ≤ x a := by omega
    rcases this with h | h <;> nlinarith
  · exact sq_nonneg _

/-- Averaging the rows of the pairwise-difference matrix gives sparsification
without needing the paper's small-norm assumption. The bound is written without
division: `q * support ≤ 2 * norm`. -/
theorem sparse_representative (v : IntegerRing q) :
    ∃ x : Coeff ℤ q, classOf x = v ∧ (q : ℤ) * supportCard x ≤ 2 * normSq v := by
  classical
  obtain ⟨z, rfl⟩ := classOf_surjective v
  let row (a : ZMod q) : ℤ := ∑ b, (z b-z a)^2
  have hsum : ∑ a, (q : ℤ) * row a ≤ ∑ _a : ZMod q, 2 * coeffNormSq z := by
    rw [← Finset.mul_sum]
    have he : (∑ a, row a) = 2 * coeffNormSq z := by
      unfold row
      rw [Finset.sum_comm, ← two_mul_coeffNormSq]
    rw [he]
    simp [Finset.card_univ, ZMod.card]
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  let x : Coeff ℤ q := fun b => z b-z a
  refine ⟨x, ?_, ?_⟩
  · simpa only [x, sub_eq_add_neg] using classOf_add_constant z (-z a)
  · rw [normSq_classOf]
    have hc : (supportCard x : ℤ) ≤ row a := supportCard_le_sqNorm x
    have hq : (0 : ℤ) ≤ q := Nat.cast_nonneg q
    exact (mul_le_mul_of_nonneg_left hc hq).trans ha

/-- Paper `sparse-tools` (i), with a rational right-hand side. -/
theorem sparse_tools_i (v : IntegerRing q) (_h : ((normSq v : ℤ) : ℚ) < (q : ℚ)^2 / 4) :
    ∃ x : Coeff ℤ q, classOf x = v ∧ (supportCard x : ℚ) ≤ 2 * ((normSq v : ℤ) : ℚ) / q := by
  obtain ⟨x, hx, hs⟩ := sparse_representative v
  refine ⟨x, hx, (le_div_iff₀ (by exact_mod_cast (NeZero.pos q))).mpr ?_⟩
  exact_mod_cast (by simpa [mul_comm] using hs)


/-- Cauchy--Schwarz restricted to the support. -/
theorem coeffNormSq_support_lower (x : Coeff ℤ q) :
    (supportCard x : ℤ) * (q - supportCard x) ≤ coeffNormSq x := by
  classical
  let t := Finset.univ.filter fun a => x a ≠ 0
  have hsum : ∑ a ∈ t, x a = ∑ a, x a := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha
    exact ha
  have hsq : ∑ a ∈ t, x a^2 = ∑ a, x a^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha
    simp [ha]
  have hc := sq_sum_le_card_mul_sum_sq (s := t) (f := x)
  rw [hsum, hsq] at hc
  have hs : (supportCard x : ℤ) ≤ q := by
    exact_mod_cast (show supportCard x ≤ q from
      (Finset.card_filter_le _ _).trans_eq (by simp [Finset.card_univ, ZMod.card]))
  have hx := supportCard_le_sqNorm x
  change (supportCard x : ℤ) ≤ ∑ a, x a^2 at hx
  change (∑ a, x a)^2 ≤ (supportCard x : ℤ) * ∑ a, x a^2 at hc
  rw [coeffNormSq_eq]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hx)]

/-- The paper's roots of unity, expressed intrinsically in the coefficient model. -/
def IsSignedMonomial (v : IntegerRing q) : Prop :=
  ∃ j : ZMod q, v = monomial j ∨ v = -monomial j

theorem normSq_monomial (j : ZMod q) : normSq (monomial j : IntegerRing q) = q-1 := by
  have he : (monomial j : IntegerRing q) = classOf (fun a => if a = j then 1 else 0) := by
    unfold monomial classOf
    congr 1
    ext a
    simp only [coeff_ofCoeff, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm]
  rw [he, normSq_classOf, coeffNormSq_eq]
  simp

theorem normSq_signedMonomial {v : IntegerRing q} (hv : IsSignedMonomial v) :
    normSq v = q-1 := by
  obtain ⟨j, rfl | rfl⟩ := hv
  · exact normSq_monomial j
  · rw [normSq_neg, normSq_monomial]

/-- Paper `second-shell`: every nonzero class is a signed monomial, or has
squared canonical norm at least `2q-4`. -/
theorem second_shell (v : IntegerRing q) (hv : v ≠ 0) :
    IsSignedMonomial v ∨ 2*(q : ℤ)-4 ≤ normSq v := by
  classical
  by_cases hn : 2*(q : ℤ)-4 ≤ normSq v
  · exact Or.inr hn
  left
  have hn := lt_of_not_ge hn
  have hN := normSq_nonneg v
  have hq : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  obtain ⟨x, hx, hs⟩ := sparse_representative v
  have hnx : coeffNormSq x = normSq v := by rw [← hx, normSq_classOf]
  have hlo := coeffNormSq_support_lower x
  rw [hnx] at hlo
  have hsz : supportCard x < 4 := by
    by_contra h
    have : (4 : ℤ) ≤ supportCard x := by exact_mod_cast (by omega : 4 ≤ supportCard x)
    nlinarith
  have hs1 : supportCard x = 1 := by
    have hne : supportCard x ≠ 0 := by
      intro hz
      have hx0 : x = 0 := by
        funext a
        have hh : (Finset.univ.filter fun a => x a ≠ 0) = ∅ := Finset.card_eq_zero.mp hz
        change x a = 0
        by_contra ha
        have : a ∈ (Finset.univ.filter fun a => x a ≠ 0) := by simp [ha]
        rw [hh] at this
        exact Finset.notMem_empty a this
      apply hv
      rw [← hx, hx0, classOf_zero]
    interval_cases he : supportCard x <;> norm_num [he] at hs hlo ⊢ <;> omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hs1
  have hcoord (a : ZMod q) : x a = if a = j then x j else 0 := by
    split_ifs with ha
    · rw [ha]
    · by_contra hh
      have : a ∈ (Finset.univ.filter fun a => x a ≠ 0) := by simp [hh]
      rw [hj] at this
      exact ha (Finset.mem_singleton.mp this)
  have he : x = fun a => if a = j then x j else 0 := funext hcoord
  have hNj : normSq v = ((q : ℤ)-1) * (x j)^2 := by
    rw [← hnx, he, coeffNormSq_eq]
    simp
    ring
  have hjnz : x j ≠ 0 := by
    have : j ∈ (Finset.univ.filter fun a => x a ≠ 0) := by rw [hj]; simp
    simpa using this
  have hjunit : x j = 1 ∨ x j = -1 := by
    by_contra hh
    have : x j ≤ -2 ∨ 2 ≤ x j := by omega
    rcases this with h | h <;> nlinarith [sq_nonneg (x j - 2), sq_nonneg (x j + 2)]
  refine ⟨j, ?_⟩
  have heq (c : ℤ) : classOf (fun a : ZMod q => if a = j then c else 0) =
      Ideal.Quotient.mk _ (AddMonoidAlgebra.single j c) := by
    unfold classOf
    congr 1
    ext a
    simp only [coeff_ofCoeff, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm]
  rcases hjunit with hjunit | hjunit
  · left
    rw [← hx, he, hjunit, heq]
    rfl
  · right
    rw [← hx, he, hjunit, heq]
    unfold monomial
    rw [← map_neg]
    congr 1
    ext a
    simp

end
end Rank2ModuleSVP
