import Power2IdealSVP.Algebra.IdealBasic

/-!
# Full signs and their finite local-field objective

The full-sign objective is a maximum over a concrete finite set of coefficient arrays, and its
inner minimum is over the nonempty set of all coordinates. Both extrema are attained. The
resulting norm identity applies to every integer negacyclic multiplier, without a source promise.

Paper: `paper/power2-ideal-svp.pdf`, Section 1.5, equations (2) and (3).
-/

namespace Power2IdealSVP.Ideal
open Power2ModuleSVP (Coeff Signs)
open IdealCVP.Cyclotomic (mul)
open Power2IdealSVP.Algebra

/-- All full sign arrays, represented as the image of Boolean coefficient arrays. -/
noncomputable def signSet (n : ℕ) : Finset (Coeff n) := by
  classical
  exact Finset.univ.image (fun b : Fin n → Bool => fun i => if b i then 1 else -1)

/-- Membership in the concrete sign set is exactly the full-sign predicate. -/
@[simp] theorem mem_signSet {n : ℕ} (s : Coeff n) : s ∈ signSet n ↔ Signs s := by
  classical
  constructor
  · intro h
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp h
    intro i
    cases h : b i <;> simp [h]
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨(fun i => decide (s i = 1)), Finset.mem_univ _, ?_⟩
    funext i
    rcases h i with hi | hi <;> simp [hi]

/-- There is a full sign array in every degree, including degree zero. -/
theorem signSet_nonempty (n : ℕ) : (signSet n).Nonempty := by
  refine ⟨(fun _ => 1), (mem_signSet _).mpr ?_⟩
  intro _
  exact Or.inr rfl

/-- The minimum full-sign local field over all coordinates. -/
def minField {n : ℕ} (hn : 0 < n) (K s : Coeff n) : ℤ :=
  Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => s i * mul K s i)

/-- The full-sign local-field objective, with both global signs retained. -/
noncomputable def psi {n : ℕ} (hn : 0 < n) (K : Coeff n) : ℤ :=
  (signSet n).sup' (signSet_nonempty n) (minField hn K)

/-- Every local field bounds the minimum from above. -/
theorem minField_le {n : ℕ} (hn : 0 < n) (K s : Coeff n) (i : Fin n) :
    minField hn K s ≤ s i * mul K s i := Finset.inf'_le _ (Finset.mem_univ i)

/-- A uniform lower field bound is equivalent to a bound on the minimum field. -/
theorem le_minField_iff {n : ℕ} (hn : 0 < n) (K s : Coeff n) (b : ℤ) :
    b ≤ minField hn K s ↔ ∀ i, b ≤ s i * mul K s i := by
  exact ⟨fun h i => h.trans (minField_le hn K s i),
    fun h => Finset.le_inf' _ _ (fun i _ => h i)⟩

/-- The finite coordinate minimum is attained. -/
theorem minField_attained {n : ℕ} (hn : 0 < n) (K s : Coeff n) :
    ∃ i, minField hn K s = s i * mul K s i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
    (⟨⟨0, hn⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin n)).Nonempty)
    (fun i => s i * mul K s i)
  exact ⟨i, hi⟩

/-- Every full sign is a candidate for the outer maximum. -/
theorem minField_le_psi {n : ℕ} (hn : 0 < n) (K s : Coeff n) (hs : Signs s) :
    minField hn K s ≤ psi hn K :=
  Finset.le_sup' _ ((mem_signSet s).mpr hs)

/-- The finite full-sign maximum is attained. -/
theorem psi_attained {n : ℕ} (hn : 0 < n) (K : Coeff n) :
    ∃ s : Coeff n, Signs s ∧ psi hn K = minField hn K s := by
  obtain ⟨s, hs, he⟩ := Finset.exists_mem_eq_sup' (signSet_nonempty n) (minField hn K)
  exact ⟨s, (mem_signSet s).mp hs, he⟩

/-- A bound on the outer maximum is equivalent to a bound on every full sign. -/
theorem psi_le_iff {n : ℕ} (hn : 0 < n) (K : Coeff n) (b : ℤ) :
    psi hn K ≤ b ↔ ∀ s, Signs s → minField hn K s ≤ b := by
  classical
  exact ⟨fun h s hs => (minField_le_psi hn K s hs).trans h,
    fun h => Finset.sup'_le _ _ (fun s hs => h s ((mem_signSet s).mp hs))⟩

/-- Threshold attainment for the full-sign objective. -/
theorem le_psi_iff {n : ℕ} (hn : 0 < n) (K : Coeff n) (b : ℤ) :
    b ≤ psi hn K ↔ ∃ s, Signs s ∧ ∀ i, b ≤ s i * mul K s i := by
  constructor
  · intro hb
    obtain ⟨s, hs, he⟩ := psi_attained hn K
    refine ⟨s, hs, ?_⟩
    exact (le_minField_iff hn K s b).mp (by simpa only [he] using hb)
  · rintro ⟨s, hs, hb⟩
    exact ((le_minField_iff hn K s b).mpr hb).trans (minField_le_psi hn K s hs)

/-- Absolute local fields on full signs are bounded by the coefficient one norm. -/
theorem abs_field_le {n : ℕ} (hn : 0 < n) (K s : Coeff n) (hs : Signs s)
    (i : Fin n) : |s i * mul K s i| ≤ coeffL1 K := by
  have h := abs_mul_signs_le hn K s hs i
  rcases hs i with hi | hi <;> simpa only [hi, neg_one_mul, abs_neg, one_mul] using h

/-- The coordinate minimum lies between the two one-norm bounds. -/
theorem minField_bounds {n : ℕ} (hn : 0 < n) (K s : Coeff n) (hs : Signs s) :
    -coeffL1 K ≤ minField hn K s ∧ minField hn K s ≤ coeffL1 K := by
  constructor
  · apply (le_minField_iff hn K s _).mpr
    intro i
    exact (abs_le.mp (abs_field_le hn K s hs i)).1
  · obtain ⟨i, hi⟩ := minField_attained hn K s
    rw [hi]
    exact (abs_le.mp (abs_field_le hn K s hs i)).2

/-- The full-sign objective lies between the two one-norm bounds. -/
theorem psi_bounds {n : ℕ} (hn : 0 < n) (K : Coeff n) :
    -coeffL1 K ≤ psi hn K ∧ psi hn K ≤ coeffL1 K := by
  obtain ⟨s, hs, he⟩ := psi_attained hn K
  rw [he]
  exact minField_bounds hn K s hs

/-- The norm of a full-sign image is scalar amplitude minus its minimum field. -/
theorem normInf_sign_image {n : ℕ} (hn : 0 < n) (K s : Coeff n)
    (M : ℤ) (hM : coeffL1 K < M) (hs : Signs s) :
    normInf (M • s - mul K s) = M - minField hn K s :=
  normInf_dominated_signs hn K s M hM hs _ (minField_le hn K s)
    (minField_attained hn K s)

/-- Every full-sign image has norm at least scalar amplitude minus the objective. -/
theorem objective_le_sign_image {n : ℕ} (hn : 0 < n) (K s : Coeff n)
    (M : ℤ) (hM : coeffL1 K < M) (hs : Signs s) :
    M - psi hn K ≤ normInf (M • s - mul K s) := by
  rw [normInf_sign_image hn K s M hM hs]
  have := minField_le_psi hn K s hs
  omega

/-- A full sign attains the minimum image norm. -/
theorem exists_sign_image_eq {n : ℕ} (hn : 0 < n) (K : Coeff n)
    (M : ℤ) (hM : coeffL1 K < M) :
    ∃ s : Coeff n, Signs s ∧ normInf (M • s - mul K s) = M - psi hn K := by
  obtain ⟨s, hs, he⟩ := psi_attained hn K
  exact ⟨s, hs, by rw [normInf_sign_image hn K s M hM hs, he]⟩

/-- The finite minimum over the full-sign layer is exactly scalar amplitude minus `psi`. -/
theorem min_sign_image_eq {n : ℕ} (hn : 0 < n) (K : Coeff n)
    (M : ℤ) (hM : coeffL1 K < M) :
    (signSet n).inf' (signSet_nonempty n) (fun s => normInf (M • s - mul K s)) =
      M - psi hn K := by
  classical
  apply le_antisymm
  · obtain ⟨s, hs, he⟩ := exists_sign_image_eq hn K M hM
    rw [← he]
    exact Finset.inf'_le _ ((mem_signSet s).mpr hs)
  · apply Finset.le_inf'
    intro s hs
    exact objective_le_sign_image hn K s M hM ((mem_signSet s).mp hs)

end Power2IdealSVP.Ideal
