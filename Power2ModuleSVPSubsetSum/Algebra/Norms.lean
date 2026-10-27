import Power2ModuleSVP.Coset.ParityBlock

/-! # Coefficient norms

Integer coefficient norms and the convolution estimate, for arbitrary negacyclic degrees.
Paper: `paper/power2svp-subsetsum.pdf`, Section 2.1.
-/
namespace Power2ModuleSVPSubsetSum
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- The sum of the absolute values of the coefficients. -/
def coeffL1 {d : ℕ} (a : Coeff d) : ℕ := ∑ i, (a i).natAbs

/-- The zero polynomial has coefficient l1 norm zero. -/
@[simp] theorem coeffL1_zero {d : ℕ} : coeffL1 (0 : Coeff d) = 0 := by
  simp [coeffL1]

/-- Negation preserves the coefficient l1 norm. -/
@[simp] theorem coeffL1_neg {d : ℕ} (a : Coeff d) : coeffL1 (-a) = coeffL1 a := by
  simp [coeffL1]

/-- Scalar multiplication scales the coefficient l1 norm. -/
theorem coeffL1_smul {d : ℕ} (z : ℤ) (a : Coeff d) :
    coeffL1 (z • a) = z.natAbs * coeffL1 a := by
  simp [coeffL1, Int.natAbs_mul, Finset.mul_sum]

/-- The maximum norm bounds each coefficient. -/
theorem natAbs_le_coeffSup {d : ℕ} (a : Coeff d) (i : Fin d) :
    (a i).natAbs ≤ coeffSup a := by
  exact Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)

/-- The maximum coefficient is bounded by the coefficient l1 norm. -/
theorem coeffSup_le_coeffL1 {d : ℕ} (a : Coeff d) : coeffSup a ≤ coeffL1 a := by
  unfold coeffSup coeffL1
  apply Finset.sup_le
  intro i _
  exact Finset.single_le_sum (fun j _ => Nat.zero_le ((a j).natAbs)) (Finset.mem_univ i)

/-- A coefficient maximum bound is equivalent to its coordinate bounds. -/
theorem coeffSup_le_iff {d : ℕ} (a : Coeff d) (T : ℕ) :
    coeffSup a ≤ T ↔ ∀ i, (a i).natAbs ≤ T := by
  simp [coeffSup, Finset.sup_le_iff]

/-- The zero polynomial has coefficient maximum zero. -/
@[simp] theorem coeffSup_zero {d : ℕ} : coeffSup (0 : Coeff d) = 0 := by
  simp [coeffSup]

/-- Negation preserves the coefficient maximum norm. -/
@[simp] theorem coeffSup_neg {d : ℕ} (a : Coeff d) : coeffSup (-a) = coeffSup a := by
  simp [coeffSup]

/-- The coefficient maximum norm vanishes exactly at zero. -/
@[simp] theorem coeffSup_eq_zero_iff {d : ℕ} (a : Coeff d) :
    coeffSup a = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext i
    have := natAbs_le_coeffSup a i
    simpa [h] using this
  · rintro rfl
    exact coeffSup_zero

/-- Triangle inequality for the coefficient maximum norm. -/
theorem coeffSup_add_le {d : ℕ} (a b : Coeff d) :
    coeffSup (a + b) ≤ coeffSup a + coeffSup b := by
  rw [coeffSup_le_iff]
  intro i
  exact (Int.natAbs_add_le _ _).trans
    (Nat.add_le_add (natAbs_le_coeffSup a i) (natAbs_le_coeffSup b i))

/-- Triangle inequality for subtraction. -/
theorem coeffSup_sub_le {d : ℕ} (a b : Coeff d) :
    coeffSup (a - b) ≤ coeffSup a + coeffSup b := by
  simpa [sub_eq_add_neg] using coeffSup_add_le a (-b)

/-- Integer scalar multiplication scales the maximum norm by the absolute scalar. -/
theorem coeffSup_smul {d : ℕ} (z : ℤ) (a : Coeff d) :
    coeffSup (z • a) = z.natAbs * coeffSup a := by
  simp only [coeffSup, Pi.smul_apply, smul_eq_mul, Int.natAbs_mul]
  have hs (s : Finset (Fin d)) :
      s.sup (fun i => z.natAbs * (a i).natAbs) = z.natAbs * s.sup (fun i => (a i).natAbs) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi hs => simp only [Finset.sup_insert, hs, mul_max]
  exact hs _

/-- Finite triangle inequality for the maximum norm. -/
theorem coeffSup_sum_le {ι : Type*} [Fintype ι] {d : ℕ} (a : ι → Coeff d) :
    coeffSup (∑ i, a i) ≤ ∑ i, coeffSup (a i) := by
  classical
  suffices ∀ s : Finset ι, coeffSup (∑ i ∈ s, a i) ≤ ∑ i ∈ s, coeffSup (a i) by
    simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
    simpa [Finset.sum_insert hi] using
      (coeffSup_add_le (a i) (∑ j ∈ s, a j)).trans (Nat.add_le_add_left hs _)

/-- Multiplication by a monomial is a signed permutation of coefficients. -/
theorem monomial_mul_natAbs {d : ℕ} (e j : Fin d) (a : Coeff d) :
    (mul (monomial e 1) a (⟨(e.val + j.val) % d,
      Nat.mod_lt _ (by have := e.isLt; omega)⟩)).natAbs = (a j).natAbs := by
  have hd : 0 < d := by have := e.isLt; omega
  let : NeZero d := ⟨by omega⟩
  have heq : mul (monomial e 1) a = sparse (fun j : Fin d => e + j)
      (fun j => (if e.val + j.val < d then 1 else -1) * a j) := by
    funext r
    rw [mul_monomial_left, sparse_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hc : (e.val + j.val) % d = r.val ↔ r = e + j := by
      simp only [Fin.ext_iff, Fin.val_add]
      omega
    simp only [hc, mul_one]
  change (mul (monomial e 1) a (e + j)).natAbs = _
  rw [heq, sparse_at (fun _ _ h => add_left_cancel h)]
  split_ifs <;> simp

/-- Signed monomial shifts preserve the maximum norm at every radius. -/
theorem coeffSup_monomial_mul {d : ℕ} (e : Fin d) (a : Coeff d) :
    coeffSup (mul (monomial e 1) a) = coeffSup a := by
  have hd : 0 < d := by have := e.isLt; omega
  let : NeZero d := ⟨by omega⟩
  apply Nat.le_antisymm
  · rw [coeffSup_le_iff]
    intro r
    obtain ⟨j, rfl⟩ := (Equiv.addLeft e).surjective r
    exact (monomial_mul_natAbs e j a).trans_le (natAbs_le_coeffSup a j)
  · rw [coeffSup_le_iff]
    intro j
    exact (monomial_mul_natAbs e j a).symm.trans_le
      (natAbs_le_coeffSup _ (e + j))

/-- A monomial shift also preserves the coefficient l1 norm. -/
theorem coeffL1_monomial_mul {d : ℕ} (e : Fin d) (a : Coeff d) :
    coeffL1 (mul (monomial e 1) a) = coeffL1 a := by
  have hd : 0 < d := by have := e.isLt; omega
  let : NeZero d := ⟨by omega⟩
  rw [coeffL1, ← Equiv.sum_comp (Equiv.addLeft e)]
  apply Finset.sum_congr rfl
  intro j _
  exact monomial_mul_natAbs e j a

/-- Triangle inequality for the coefficient l1 norm. -/
theorem coeffL1_add_le {d : ℕ} (a b : Coeff d) :
    coeffL1 (a + b) ≤ coeffL1 a + coeffL1 b := by
  unfold coeffL1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => Int.natAbs_add_le (a i) (b i))

/-- Finite triangle inequality for the coefficient l1 norm. -/
theorem coeffL1_sum_le {ι : Type*} [Fintype ι] {d : ℕ} (a : ι → Coeff d) :
    coeffL1 (∑ i, a i) ≤ ∑ i, coeffL1 (a i) := by
  classical
  suffices ∀ s : Finset ι, coeffL1 (∑ i ∈ s, a i) ≤ ∑ i ∈ s, coeffL1 (a i) by
    simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
    simpa [Finset.sum_insert hi] using
      (coeffL1_add_le (a i) (∑ j ∈ s, a j)).trans (Nat.add_le_add_left hs _)

/-- Every coefficient vector is its monomial expansion. -/
theorem eq_sum_monomial {d : ℕ} (a : Coeff d) :
    a = ∑ i, (a i) • monomial i 1 := by
  ext r
  simp [Finset.sum_apply, monomial]

/-- The coefficient l1/maximum convolution inequality. -/
theorem coeffSup_mul_le {d : ℕ} (a b : Coeff d) :
    coeffSup (mul a b) ≤ coeffL1 a * coeffSup b := by
  conv_lhs => rw [eq_sum_monomial a]
  rw [mul_sum_left]
  calc
    _ ≤ ∑ i, coeffSup (mul ((a i) • monomial i 1) b) := coeffSup_sum_le _
    _ = _ := by
      simp only [mul_smul_left, coeffSup_smul, coeffSup_monomial_mul, coeffL1,
        Finset.sum_mul]

/-- Submultiplicativity of the coefficient l1 norm. -/
theorem coeffL1_mul_le {d : ℕ} (a b : Coeff d) :
    coeffL1 (mul a b) ≤ coeffL1 a * coeffL1 b := by
  conv_lhs => rw [eq_sum_monomial a]
  rw [mul_sum_left]
  calc
    _ ≤ ∑ i, coeffL1 (mul ((a i) • monomial i 1) b) := coeffL1_sum_le _
    _ = _ := by
      simp only [mul_smul_left, coeffL1_smul, coeffL1_monomial_mul]
      rw [← Finset.sum_mul]
      rfl

/-- Explicit negacyclic shift, including its wraparound sign. -/
theorem monomial_mul_apply {d : ℕ} (e r : Fin d) (a : Coeff d) :
    mul (monomial e 1) a r =
      if h : e.val ≤ r.val then a ⟨r.val - e.val, by omega⟩
      else -a ⟨d + r.val - e.val, by omega⟩ := by
  have hd : 0 < d := by have := e.isLt; omega
  let : NeZero d := ⟨by omega⟩
  rw [mul_monomial_left]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨r.val - e.val, by omega⟩ : Fin d)]
    · have he : e.val + (r.val - e.val) = r.val := by omega
      simp [he, Nat.mod_eq_of_lt r.isLt, r.isLt]
    · intro j _ hj
      have hn : (e.val + j.val) % d ≠ r.val := by
        intro he
        have heq : e + j = e + (⟨r.val - e.val, by omega⟩ : Fin d) := by
          apply Fin.ext
          simp only [Fin.val_add]
          have hs : e.val + (r.val - e.val) = r.val := by omega
          simpa [hs, Nat.mod_eq_of_lt r.isLt] using he
        exact hj (add_left_cancel heq)
      simp [hn]
    · simp
  · rw [Finset.sum_eq_single (⟨d + r.val - e.val, by omega⟩ : Fin d)]
    · have he : e.val + (d + r.val - e.val) = d + r.val := by omega
      simp [he, Nat.mod_eq_of_lt r.isLt,
        show ¬d + r.val < d by omega]
    · intro j _ hj
      have hn : (e.val + j.val) % d ≠ r.val := by
        intro he
        have heq : e + j = e + (⟨d + r.val - e.val, by omega⟩ : Fin d) := by
          apply Fin.ext
          simp only [Fin.val_add]
          have hs : e.val + (d + r.val - e.val) = d + r.val := by omega
          simpa [hs, Nat.add_mod, Nat.mod_eq_of_lt r.isLt] using he
        exact hj (add_left_cancel heq)
      simp [hn]
    · simp

end Power2ModuleSVPSubsetSum
