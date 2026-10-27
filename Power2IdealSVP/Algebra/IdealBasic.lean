import Power2ModuleSVP.Coset.ParityBlock

/-!
# Coefficient norm bounds for the principal ideal bridge

Elementary integral coefficient estimates for arbitrary negacyclic multipliers. No symmetry,
dyadic degree, or threshold promise is used.

Paper: `paper/power2-ideal-svp.pdf`, Section 1.5, equations (2) and (3).
-/

namespace Power2IdealSVP.Algebra
open Power2ModuleSVP (Coeff coeffSup Signs)
open IdealCVP.Cyclotomic (mul)

/-- The sum of absolute coefficients. -/
def coeffL1 {n : ℕ} (a : Coeff n) : ℤ := ∑ i, |a i|

/-- The coefficient maximum norm, viewed as an integer. -/
def normInf {n : ℕ} (a : Coeff n) : ℤ := (coeffSup a : ℤ)

/-- The integer-valued coefficient maximum norm is nonnegative. -/
@[simp] theorem normInf_nonneg {n : ℕ} (a : Coeff n) : 0 ≤ normInf a := by
  exact Int.natCast_nonneg _

/-- The integer-valued coefficient one-norm is nonnegative. -/
@[simp] theorem coeffL1_nonneg {n : ℕ} (a : Coeff n) : 0 ≤ coeffL1 a := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Every coefficient is bounded by the coefficient maximum norm. -/
theorem abs_le_normInf {n : ℕ} (a : Coeff n) (i : Fin n) : |a i| ≤ normInf a := by
  have h : (a i).natAbs ≤ coeffSup a := by
    exact Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ i)
  have hc : ((a i).natAbs : ℤ) ≤ (coeffSup a : ℤ) := by exact_mod_cast h
  simpa only [Int.natCast_natAbs, normInf] using hc

/-- Uniform coefficient bounds imply a bound on the maximum norm. -/
theorem normInf_le {n : ℕ} (a : Coeff n) {b : ℤ} (hb : 0 ≤ b)
    (h : ∀ i, |a i| ≤ b) : normInf a ≤ b := by
  have h' : coeffSup a ≤ b.toNat := by
    apply Finset.sup_le
    intro i _
    have hi := h i
    have hb' : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb
    have : ((a i).natAbs : ℤ) ≤ (b.toNat : ℤ) := by
      simpa only [Int.natCast_natAbs, hb'] using hi
    exact_mod_cast this
  calc
    normInf a ≤ (b.toNat : ℤ) := by unfold normInf; exact_mod_cast h'
    _ = b := Int.toNat_of_nonneg hb

/-- The zero coefficient array has maximum norm zero. -/
@[simp] theorem normInf_zero {n : ℕ} : normInf (0 : Coeff n) = 0 := by
  simp [normInf, coeffSup]

/-- The coefficient maximum norm vanishes exactly on the zero vector. -/
theorem normInf_eq_zero_iff {n : ℕ} (a : Coeff n) : normInf a = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext i
    have hi := abs_le_normInf a i
    rw [h] at hi
    exact abs_eq_zero.mp (le_antisymm hi (abs_nonneg _))
  · rintro rfl
    exact normInf_zero

/-- A positive degree supplies a coefficient attaining the maximum norm. -/
theorem exists_abs_eq_normInf {n : ℕ} (hn : 0 < n) (a : Coeff n) :
    ∃ i, |a i| = normInf a := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i : Fin n => (a i).natAbs)
  refine ⟨i, ?_⟩
  unfold normInf coeffSup
  rw [hi, Int.natCast_natAbs]

private theorem mul_at {n : ℕ} (a b : Coeff n) (r : Fin n) :
    mul a b r = ∑ i : Fin n,
      (if i.val + (r - i).val < n then 1 else -1) * a i * b (r - i) := by
  let : NeZero n := ⟨by have := r.isLt; omega⟩
  unfold mul
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (r - i)]
  · have he : (i.val + (r - i).val) % n = r.val := by
      simpa only [Fin.val_add] using congrArg Fin.val (add_sub_cancel i r)
    simp [he]
  · intro j _ hj
    have hne : (i.val + j.val) % n ≠ r.val := by
      intro he
      apply hj
      have : i + j = r := Fin.ext (by simpa only [Fin.val_add] using he)
      exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using this)
    simp [hne]
  · simp

/-- Negacyclic convolution has operator norm bounded by the coefficient one norm. -/
theorem abs_mul_le {n : ℕ} (a b : Coeff n) (i : Fin n) :
    |mul a b i| ≤ coeffL1 a * normInf b := by
  rw [mul_at]
  calc
    _ ≤ ∑ j : Fin n,
        |(if j.val + (i - j).val < n then 1 else -1) * a j * b (i - j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |a j| * |b (i - j)| := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp [abs_mul]
    _ ≤ ∑ j : Fin n, |a j| * normInf b := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (abs_le_normInf b _) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- The coefficient maximum norm version of the convolution bound. -/
theorem normInf_mul_le {n : ℕ} (a b : Coeff n) :
    normInf (mul a b) ≤ coeffL1 a * normInf b :=
  normInf_le _ (mul_nonneg (coeffL1_nonneg a) (normInf_nonneg b)) (abs_mul_le a b)

/-- Domination by a scalar gives the coercivity estimate used in equation (3). -/
theorem coercive {n : ℕ} (hn : 0 < n) (K y : Coeff n) (M : ℤ) (hM : 0 ≤ M) :
    (M - coeffL1 K) * normInf y ≤ normInf (M • y - mul K y) := by
  obtain ⟨i, hi⟩ := exists_abs_eq_normInf hn y
  have h := abs_sub_abs_le_abs_sub (M * y i) (mul K y i)
  have hb := abs_mul_le K y i
  have ho := abs_le_normInf (M • y - mul K y) i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ho
  rw [abs_mul, abs_of_nonneg hM, hi] at h
  nlinarith

/-- Strict scalar domination makes the coefficient operator injective at zero. -/
theorem dominated_eq_zero_iff {n : ℕ} (hn : 0 < n) (K y : Coeff n)
    (M : ℤ) (hM : coeffL1 K < M) : M • y - mul K y = 0 ↔ y = 0 := by
  constructor
  · intro hy
    have h := coercive hn K y M (le_trans (coeffL1_nonneg K) (le_of_lt hM))
    rw [hy, normInf_zero] at h
    have hz : normInf y = 0 := by
      have := normInf_nonneg y
      nlinarith
    exact (normInf_eq_zero_iff y).mp hz
  · rintro rfl
    simp

/-- A full sign vector has coefficient maximum norm one. -/
theorem normInf_signs {n : ℕ} (hn : 0 < n) (s : Coeff n) (hs : Signs s) :
    normInf s = 1 := by
  have ha (i : Fin n) : |s i| = 1 := by
    rcases hs i with hi | hi <;> simp [hi]
  apply le_antisymm
  · exact normInf_le s (by omega) (fun i => le_of_eq (ha i))
  · have := abs_le_normInf s ⟨0, hn⟩
    simpa only [ha] using this

/-- Full signs convert the convolution estimate into the one-norm bound. -/
theorem abs_mul_signs_le {n : ℕ} (hn : 0 < n) (K s : Coeff n)
    (hs : Signs s) (i : Fin n) : |mul K s i| ≤ coeffL1 K := by
  simpa only [normInf_signs hn s hs, mul_one] using abs_mul_le K s i

/-- Scalar domination is injective on all coefficient vectors. -/
theorem dominated_injective {n : ℕ} (hn : 0 < n) (K : Coeff n)
    (M : ℤ) (hM : coeffL1 K < M) :
    Function.Injective (fun y : Coeff n => M • y - mul K y) := by
  intro y z he
  have hz : M • (y - z) - mul K (y - z) = 0 := by
    rw [smul_sub, sub_eq_add_neg y z, IdealCVP.Cyclotomic.mul_add,
      IdealCVP.Cyclotomic.mul_neg]
    ext i
    have hi := congrFun he i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hi ⊢
    omega
  exact sub_eq_zero.mp ((dominated_eq_zero_iff hn K (y - z) M hM).mp hz)

/-- On full signs, a local-field minimum determines the exact norm of the image.

The hypotheses `hm` and `he` say precisely that `m` is an attained minimum of the finite
coefficient fields; keeping that minimum abstract lets callers use either finite-set convention.
-/
theorem normInf_dominated_signs {n : ℕ} (hn : 0 < n) (K s : Coeff n)
    (M : ℤ) (hM : coeffL1 K < M) (hs : Signs s) (m : ℤ)
    (hm : ∀ i, m ≤ s i * mul K s i) (he : ∃ i, m = s i * mul K s i) :
    normInf (M • s - mul K s) = M - m := by
  have habs (i : Fin n) : |M * s i - mul K s i| = M - s i * mul K s i := by
    have hb := abs_le.mp (abs_mul_signs_le hn K s hs i)
    rcases hs i with hi | hi
    · rw [hi]
      simp only [mul_neg, mul_one, sub_neg_eq_add, neg_mul, one_mul]
      rw [abs_of_nonpos (by omega)]
      ring
    · rw [hi]
      simp only [mul_one, one_mul]
      rw [abs_of_nonneg (by omega)]
  obtain ⟨i, hi⟩ := he
  have hnonneg : 0 ≤ M - m := by
    rw [hi, ← habs]
    exact abs_nonneg _
  apply le_antisymm
  · apply normInf_le _ hnonneg
    intro j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, habs]
    have := hm j
    omega
  · have hb := abs_le_normInf (M • s - mul K s) i
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, habs, hi] using hb

end Power2IdealSVP.Algebra
