import Power2IdealSVP.Ideal.FullSigns
import Power2IdealSVP.Ideal.Walls

/-!
# The finite sparse-spin objective and the clock identity

`thetaOf` is the maximum, over the finite set of all intrinsic odd alternating spins,
of the minimum of `σ i * (Gσ) i` on their nonempty supports. Both initial signs are
retained. The finite set is enumerated by taking walls of full signs; its membership
predicate is proved equivalent to the prefix-sum predicate `OddAlternating`.
No symmetry or threshold promise is imposed on `G`.

Paper: `paper/power2-ideal-svp.pdf`, Section 1.5, equation (2).
-/

namespace Power2IdealSVP.Ideal
open Power2ModuleSVP (Coeff Signs)
open IdealCVP.Cyclotomic
open Power2IdealSVP.Algebra

/-- The active coordinates of a sparse coefficient array. -/
noncomputable def spinSupport {n : ℕ} (σ : Coeff n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => σ i ≠ 0)

/-- Membership in the wall-spin support means the coefficient is nonzero. -/
@[simp] theorem mem_spinSupport {n : ℕ} (σ : Coeff n) (i : Fin n) :
    i ∈ spinSupport σ ↔ σ i ≠ 0 := by
  classical
  simp [spinSupport]

/-- An odd alternating spin has a nonempty active support. -/
theorem spinSupport_nonempty {n : ℕ} {σ : Coeff n} (hσ : OddAlternating σ) :
    (spinSupport σ).Nonempty := by
  classical
  by_contra h
  apply hσ.ne_zero
  funext i
  by_contra hi
  exact h ⟨i, (mem_spinSupport σ i).mpr hi⟩

/-- The minimum active field. The value zero outside the alternating class is unused. -/
noncomputable def spinMin {n : ℕ} (G σ : Coeff n) : ℤ := by
  classical
  exact if h : OddAlternating σ then
    (spinSupport σ).inf' (spinSupport_nonempty h) (fun i => σ i * mul G σ i)
  else 0

/-- Every active field bounds the sparse minimum. -/
theorem spinMin_le {n : ℕ} (G σ : Coeff n) (hσ : OddAlternating σ)
    (i : Fin n) (hi : σ i ≠ 0) : spinMin G σ ≤ σ i * mul G σ i := by
  classical
  simp only [spinMin, dite_eq_left hσ]
  exact Finset.inf'_le _ ((mem_spinSupport σ i).mpr hi)

/-- A uniform active-field lower bound bounds the sparse minimum. -/
theorem le_spinMin {n : ℕ} (G σ : Coeff n) (hσ : OddAlternating σ) (b : ℤ)
    (hb : ∀ i, σ i ≠ 0 → b ≤ σ i * mul G σ i) : b ≤ spinMin G σ := by
  classical
  simp only [spinMin, dite_eq_left hσ]
  exact Finset.le_inf' _ _ (fun i hi => hb i ((mem_spinSupport σ i).mp hi))

/-- The sparse minimum is attained at an active coordinate. -/
theorem spinMin_attained {n : ℕ} (G σ : Coeff n) (hσ : OddAlternating σ) :
    ∃ i, σ i ≠ 0 ∧ spinMin G σ = σ i * mul G σ i := by
  classical
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' (spinSupport_nonempty hσ)
    (fun i => σ i * mul G σ i)
  exact ⟨i, (mem_spinSupport σ i).mp hi, by simpa [spinMin, hσ] using he⟩

/-- A concrete finite enumeration of all odd alternating sparse spins. -/
noncomputable def spinSet {n : ℕ} (hn : 0 < n) : Finset (Coeff n) := by
  classical
  exact (signSet n).image (wallSpin hn)

/-- The finite enumeration has exactly the intrinsic alternating membership predicate. -/
@[simp] theorem mem_spinSet {n : ℕ} (hn : 0 < n) (σ : Coeff n) :
    σ ∈ spinSet hn ↔ OddAlternating σ := by
  classical
  constructor
  · intro h
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp h
    exact oddAlternating_wallSpin hn ((mem_signSet s).mp hs)
  · intro h
    refine Finset.mem_image.mpr ⟨mul (sumPoly n) σ, ?_, wallSpin_sumPoly hn h⟩
    exact (mem_signSet _).mpr ((oddAlternating_iff_signs_sumPoly hn σ).mp h)

/-- The sparse-spin class is nonempty in every positive degree. -/
theorem spinSet_nonempty {n : ℕ} (hn : 0 < n) : (spinSet hn).Nonempty := by
  classical
  exact (signSet_nonempty n).image (wallSpin hn)

/-- The maximum active-field minimum over all odd alternating spins, for arbitrary `G`. -/
noncomputable def thetaOf {n : ℕ} (hn : 0 < n) (G : Coeff n) : ℤ :=
  (spinSet hn).sup' (spinSet_nonempty hn) (spinMin G)

/-- Every odd alternating spin bounds the finite sparse objective from below. -/
theorem spinMin_le_thetaOf {n : ℕ} (hn : 0 < n) (G σ : Coeff n)
    (hσ : OddAlternating σ) : spinMin G σ ≤ thetaOf hn G :=
  Finset.le_sup' _ ((mem_spinSet hn σ).mpr hσ)

/-- The sparse maximum is attained by an odd alternating spin. -/
theorem thetaOf_attained {n : ℕ} (hn : 0 < n) (G : Coeff n) :
    ∃ σ, OddAlternating σ ∧ thetaOf hn G = spinMin G σ := by
  obtain ⟨σ, hσ, he⟩ := Finset.exists_mem_eq_sup' (spinSet_nonempty hn) (spinMin G)
  exact ⟨σ, (mem_spinSet hn σ).mp hσ, he⟩

/-- Threshold attainment for the sparse objective. -/
theorem le_thetaOf_iff {n : ℕ} (hn : 0 < n) (G : Coeff n) (b : ℤ) :
    b ≤ thetaOf hn G ↔
      ∃ σ, OddAlternating σ ∧ ∀ i, σ i ≠ 0 → b ≤ σ i * mul G σ i := by
  constructor
  · intro hb
    obtain ⟨σ, hσ, he⟩ := thetaOf_attained hn G
    refine ⟨σ, hσ, fun i hi => ?_⟩
    exact (show b ≤ spinMin G σ by simpa only [he] using hb).trans (spinMin_le G σ hσ i hi)
  · rintro ⟨σ, hσ, hb⟩
    exact (le_spinMin G σ hσ b hb).trans (spinMin_le_thetaOf hn G σ hσ)

/-- The clock multiplier `BX + G(1-X)`. -/
def clockMultiplier {n : ℕ} (hn : 0 < n) (G : Coeff n) (B : ℤ) : Coeff n :=
  B • xPoly hn + mul G (difference hn)

/-- The perturbation applied to a full sign is twice `G` applied to its walls. -/
theorem perturbation_sign {n : ℕ} (hn : 0 < n) (G s : Coeff n) (hs : Signs s) :
    mul (mul G (difference hn)) s = (2 : ℤ) • mul G (wallSpin hn s) := by
  rw [Power2ModuleSVP.coeff_mul_assoc hn, difference_signs hn hs,
    mul_smul_right]

/-- At a wall, the clock field is `-B` plus twice the sparse local field. -/
theorem clock_field_active {n : ℕ} (hn : 0 < n) (G s : Coeff n) (B : ℤ)
    (hs : Signs s) (i : Fin n) (hi : wallSpin hn s i ≠ 0) :
    s i * mul (clockMultiplier hn G B) s i =
      -B + 2 * (wallSpin hn s i * mul G (wallSpin hn s) i) := by
  have hpred := signs_shift hn hs i
  have hne : s i ≠ shift hn s i := by
    intro he
    simp [wallSpin, he] at hi
  have he : shift hn s i = -s i := by
    rcases hs i with h | h <;> rcases hpred with h' | h' <;> omega
  rw [clockMultiplier, mul_add_left,
    mul_smul_left, xPoly_mul, perturbation_sign hn G s hs]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, he,
    wallSpin_active hn s i hi]
  rcases hs i with h | h <;> rw [h] <;> ring

/-- At a nonwall the clock contribution is positive `B`. -/
theorem clock_field_inactive {n : ℕ} (hn : 0 < n) (G s : Coeff n) (B : ℤ)
    (hs : Signs s) (i : Fin n) (hi : wallSpin hn s i = 0) :
    s i * mul (clockMultiplier hn G B) s i =
      B + s i * mul (mul G (difference hn)) s i := by
  have he : s i = shift hn s i := by
    by_contra he
    have hz : s i = 0 := by simpa [wallSpin, he] using hi
    rcases hs i with h | h <;> omega
  rw [clockMultiplier, mul_add_left,
    mul_smul_left, xPoly_mul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← he]
  rcases hs i with h | h <;> rw [h] <;> ring

/-- Clock domination places the full-sign minimum on its nonempty wall support. -/
theorem minField_clock {n : ℕ} (hn : 0 < n) (G s : Coeff n) (B : ℤ)
    (hB : coeffL1 (mul G (difference hn)) < B) (hs : Signs s) :
    minField hn (clockMultiplier hn G B) s = -B + 2 * spinMin G (wallSpin hn s) := by
  let σ := wallSpin hn s
  have hσ : OddAlternating σ := oddAlternating_wallSpin hn hs
  obtain ⟨j, hj, he⟩ := spinMin_attained G σ hσ
  have hjfield := clock_field_active hn G s B hs j hj
  have hjmin : s j * mul (clockMultiplier hn G B) s j = -B + 2 * spinMin G σ := by
    rw [hjfield, he]
  have hbfield (i : Fin n) := abs_field_le hn (mul G (difference hn)) s hs i
  have htarget : -B + 2 * spinMin G σ ≤ -B + coeffL1 (mul G (difference hn)) := by
    have hpred := signs_shift hn hs j
    have hne : s j ≠ shift hn s j := by
      intro h; simp [σ, wallSpin, h] at hj
    have hp : shift hn s j = -s j := by
      rcases hs j with h | h <;> rcases hpred with h' | h' <;> omega
    have hbound := (abs_le.mp (hbfield j)).2
    have hclock : s j * mul (clockMultiplier hn G B) s j =
        -B + s j * mul (mul G (difference hn)) s j := by
      rw [clockMultiplier, mul_add_left,
        mul_smul_left, xPoly_mul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp]
      rcases hs j with h | h <;> rw [h] <;> ring
    linarith
  apply le_antisymm
  · have := minField_le hn (clockMultiplier hn G B) s j
    rwa [hjmin] at this
  · apply (le_minField_iff hn _ s _).mpr
    intro i
    by_cases hi : σ i = 0
    · change -B + 2 * spinMin G σ ≤ _
      rw [clock_field_inactive hn G s B hs i hi]
      have := (abs_le.mp (hbfield i)).1
      omega
    · change -B + 2 * spinMin G σ ≤ _
      rw [clock_field_active hn G s B hs i hi]
      change -B + 2 * spinMin G σ ≤ -B + 2 * (σ i * mul G σ i)
      have := spinMin_le G σ hσ i hi
      omega

/-- Equation (2), for every multiplier and every clock amplitude dominating the perturbation. -/
theorem psi_clock_eq {n : ℕ} (hn : 0 < n) (G : Coeff n) (B : ℤ)
    (hB : coeffL1 (mul G (difference hn)) < B) :
    psi hn (clockMultiplier hn G B) = -B + 2 * thetaOf hn G := by
  apply le_antisymm
  · apply (psi_le_iff hn _ _).mpr
    intro s hs
    rw [minField_clock hn G s B hB hs]
    have := spinMin_le_thetaOf hn G (wallSpin hn s) (oddAlternating_wallSpin hn hs)
    omega
  · obtain ⟨σ, hσ, he⟩ := thetaOf_attained hn G
    let s := mul (sumPoly n) σ
    have hs : Signs s := (oddAlternating_iff_signs_sumPoly hn σ).mp hσ
    have hwall : wallSpin hn s = σ := wallSpin_sumPoly hn hσ
    have h := minField_le_psi hn (clockMultiplier hn G B) s hs
    rw [minField_clock hn G s B hB hs, hwall, ← he] at h
    exact h

/-- Active positions in increasing order have opposite signs when consecutive. -/
theorem OddAlternating.consecutive {n : ℕ} {σ : Coeff n} (hσ : OddAlternating σ)
    {i j : Fin n} (hij : i.val < j.val) (hi : σ i ≠ 0) (hj : σ j ≠ 0)
    (hgap : ∀ k : Fin n, i.val < k.val → k.val < j.val → σ k = 0) :
    σ j = -σ i := by
  obtain ⟨η, hη, ht, hp⟩ := hσ
  have he : prefixSum σ j.val = prefixSum σ (i.val + 1) := by
    unfold prefixSum
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k.val < i.val + 1
    · have hk' : k.val < j.val := by omega
      simp [hk, hk']
    · by_cases hk' : k.val < j.val
      · have hz := hgap k (by omega) hk'
        simp [hk, hk', hz]
      · simp [hk, hk']
  have h0 := hp i.val (by omega)
  have h1 := hp (i.val + 1) (by omega)
  have h2 := hp (j.val + 1) (by omega)
  have hs0 := prefixSum_succ σ i
  have hs1 := prefixSum_succ σ j
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> omega
/-- Odd alternating support has odd cardinality. -/
theorem OddAlternating.odd_card {n : ℕ} {σ : Coeff n} (hσ : OddAlternating σ) :
    Odd (spinSupport σ).card := by
  classical
  have hsum : Even (∑ i : Fin n, (σ i - if σ i ≠ 0 then (1 : ℤ) else 0)) := by
    apply Finset.even_sum
    intro i _
    rcases hσ.ternary i with hi | hi | hi
    · exact ⟨-1, by simp [hi]⟩
    · exact ⟨0, by simp [hi]⟩
    · exact ⟨0, by simp [hi]⟩
  have hsum' : Even ((∑ i, σ i) - ((spinSupport σ).card : ℤ)) := by
    simpa only [Finset.sum_sub_distrib, Finset.sum_boole, spinSupport] using hsum
  have htotal : Odd (∑ i, σ i) := by
    obtain ⟨η, hη, ht, _⟩ := hσ
    rcases hη with rfl | rfl
    · exact ⟨-1, by omega⟩
    · exact ⟨0, by omega⟩
  have hc : Odd ((spinSupport σ).card : ℤ) := by
    simpa only [sub_sub_cancel] using htotal.sub_even hsum'
  exact (Int.odd_coe_nat _).mp hc

end Power2IdealSVP.Ideal
