import Power2ModuleSVPSubsetSum.Reduction.WeightIdentity
import Power2ModuleSVPSubsetSum.Reduction.Bridge

/-! # Exact norm of a Boolean gadget vector

The two equality-test coefficients determine the entire coefficient maximum norm.

Paper: `paper/power2svp-subsetsum.pdf`, Lemma 4.1.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Power2ModuleSVPSubsetSum.Reduction
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- Opposite deviations around `-M` have maximum absolute value `M + |t|`. -/
theorem max_natAbs_centered (M : ℕ) (t : ℤ) :
    max (t - M).natAbs (-t - M).natAbs = M + t.natAbs := by
  apply Int.ofNat_inj.mp
  simp only [Nat.cast_max, Nat.cast_add, Int.natCast_natAbs]
  have h := Rigidity.max_abs_pair (M : ℤ) t
  simpa only [abs_sub_comm, show -t - (M : ℤ) = -((M : ℤ) + t) by ring,
    abs_neg, abs_of_nonneg (Int.natCast_nonneg M)] using h

/-- The centered Boolean word lies in the unit coefficient cube. -/
theorem centeredWord_cube {n s : ℕ} (hs : s ≤ n) (ξ : Fin s → Bool) :
    Cube ((2 : ℤ) • booleanWord hs ξ - IdealCVP.ofList (mask n s)) := by
  rw [boolean_cube_iff]
  intro i
  by_cases hi : i.val < s
  · simp only [hi, ↓reduceIte, booleanWord]
    cases ξ ⟨i.val, hi⟩ <;> simp
  · simp [hi, booleanWord]

/-- The stored product `DK` has zero constant coefficient. -/
theorem gadget_DK_zero (w : List ℕ) (B : ℕ) :
    IdealCVP.ofList (d := 2 * (gadget w B).m) (gadget w B).DK
      ⟨0, by have := two_le_halfDegree w.length; dsimp [gadget]; omega⟩ = 0 := by
  have hm : 0 < (gadget w B).m :=
    lt_of_lt_of_le (by decide) (two_le_halfDegree w.length)
  exact (congrFun (gadget_DK w B) _).trans (Rigidity.DK_zero hm)

/-- The stored product `DK` has zero half-degree coefficient. -/
theorem gadget_DK_half (w : List ℕ) (B : ℕ) :
    IdealCVP.ofList (d := 2 * (gadget w B).m) (gadget w B).DK
      ⟨(gadget w B).m, by
        have := two_le_halfDegree w.length; dsimp [gadget]; omega⟩ = 0 := by
  have hm : 0 < (gadget w B).m :=
    lt_of_lt_of_le (by decide) (two_le_halfDegree w.length)
  exact (congrFun (gadget_DK w B) _).trans (Rigidity.DK_half hm)

/-- Two opposite test coefficients determine the pair norm when all others are smaller. -/
theorem pairSup_of_centered_coefficients {n : ℕ} (top bottom : Coeff n)
    (M : ℕ) (t : ℤ) (i₀ i₁ : Fin n)
    (h₀ : top i₀ = t - M) (h₁ : top i₁ = -t - M)
    (hother : ∀ i, i ≠ i₀ → i ≠ i₁ → (top i).natAbs ≤ M)
    (hbottom : coeffSup bottom ≤ M) :
    pairSup (top, bottom) = M + t.natAbs := by
  dsimp only [pairSup, Prod.fst, Prod.snd]
  apply Nat.le_antisymm
  · apply max_le
    · rw [coeffSup_le_iff]
      intro i
      by_cases hi₀ : i = i₀
      · subst i
        rw [h₀]
        exact (le_max_left _ _).trans_eq (max_natAbs_centered M t)
      · by_cases hi₁ : i = i₁
        · subst i
          rw [h₁]
          exact (le_max_right _ _).trans_eq (max_natAbs_centered M t)
        · exact (hother i hi₀ hi₁).trans (Nat.le_add_right M t.natAbs)
    · exact hbottom.trans (Nat.le_add_right M t.natAbs)
  · rw [← max_natAbs_centered M t, ← h₀, ← h₁]
    exact (max_le (natAbs_le_coeffSup top i₀) (natAbs_le_coeffSup top i₁)).trans
      (le_max_left _ _)

/-- Explicit coefficients of the stored polynomial `Q`. -/
theorem gadget_Q_apply (w : List ℕ) (B : ℕ)
    (i : Fin (2 * (gadget w B).m)) :
    IdealCVP.ofList (d := 2 * (gadget w B).m) (gadget w B).Q i =
      ((gadget w B).M : ℤ) *
        (if i.val = 0 ∨ i.val = (gadget w B).m then 1 else 0) +
      ((gadget w B).L : ℤ) * IdealCVP.ofList (gadget w B).DK i := by
  have hi : i.val < 2 * halfDegree w.length := i.isLt
  simp [gadget, IdealCVP.ofList, IdealCVP.listAdd, scale, filterD,
    List.getD_eq_getElem?_getD, hi]

/-- Explicit coefficients of the stored target polynomial `V`. -/
theorem gadget_V_apply (w : List ℕ) (B : ℕ)
    (i : Fin (2 * (gadget w B).m)) :
    IdealCVP.ofList (d := 2 * (gadget w B).m) (gadget w B).V i =
      (2 * (B : ℤ) - (w.sum : ℤ)) *
        (if i.val = 0 then 1 else if i.val = (gadget w B).m then -1 else 0) := by
  have hi : i.val < 2 * halfDegree w.length := i.isLt
  simp [gadget, IdealCVP.ofList, scale, filterDStar, List.getD_eq_getElem?_getD, hi]

/-- Lemma 4.1: the Boolean vector has exact norm `M + 2 |A-B|`. -/
theorem gadget_exactNorm (w : List ℕ) (B : ℕ) (ξ : Fin w.length → Bool) :
    let p := gadget w B
    let z := (2 : ℤ) • booleanWord
      (by have := length_le_halfDegree w.length; dsimp [p, gadget]; omega :
        w.length ≤ 2 * p.m) ξ - IdealCVP.ofList (mask (2 * p.m) w.length)
    pairSup (mul (IdealCVP.ofList p.H) z - IdealCVP.ofList p.Q - IdealCVP.ofList p.V,
      (p.M : ℤ) • z) =
      p.M + 2 * ((∑ j : Fin w.length,
        (w.get j : ℤ) * (if ξ j then 1 else 0)) - (B : ℤ)).natAbs := by
  let p := gadget w B
  have hm : 0 < p.m := lt_of_lt_of_le (by decide) (two_le_halfDegree w.length)
  have hw : w.length ≤ p.m := length_le_halfDegree w.length
  let hs : w.length ≤ 2 * p.m := by omega
  let z : Coeff (2 * p.m) :=
    (2 : ℤ) • booleanWord hs ξ - IdealCVP.ofList (mask (2 * p.m) w.length)
  let A : ℤ := ∑ j : Fin w.length, (w.get j : ℤ) * (if ξ j then 1 else 0)
  let top : Coeff (2 * p.m) :=
    mul (IdealCVP.ofList p.H) z - IdealCVP.ofList p.Q - IdealCVP.ofList p.V
  change pairSup (top, (p.M : ℤ) • z) = p.M + 2 * (A - (B : ℤ)).natAbs
  have hz : coeffSup z ≤ 1 := (cube_iff_coeffSup_le z).mp (centeredWord_cube hs ξ)
  have hH : IdealCVP.ofList (d := 2 * p.m) p.H =
      mul (IdealCVP.ofList (filterDStar p.m)) (IdealCVP.ofList (weights (2 * p.m) w)) :=
    IdealCVP.ofList_negacyclicMul (2 * p.m) _ _
  have hH0 : mul (IdealCVP.ofList p.H) z ⟨0, by omega⟩ = 2 * A - (w.sum : ℤ) := by
    rw [hH]
    exact H_centered_zero hm w hw ξ
  have hHm : mul (IdealCVP.ofList p.H) z ⟨p.m, by omega⟩ =
      -(2 * A - (w.sum : ℤ)) := by
    rw [hH]
    exact H_centered_half hm w hw ξ
  have hQ (i : Fin (2 * p.m)) : IdealCVP.ofList p.Q i =
      (p.M : ℤ) * (if i.val = 0 ∨ i.val = p.m then 1 else 0) +
        (p.L : ℤ) * IdealCVP.ofList p.DK i := gadget_Q_apply w B i
  have hV (i : Fin (2 * p.m)) : IdealCVP.ofList p.V i =
      (2 * (B : ℤ) - (w.sum : ℤ)) *
        (if i.val = 0 then 1 else if i.val = p.m then -1 else 0) := gadget_V_apply w B i
  have hDK0 : IdealCVP.ofList (d := 2 * p.m) p.DK ⟨0, by omega⟩ = 0 :=
    gadget_DK_zero w B
  have hDKm : IdealCVP.ofList (d := 2 * p.m) p.DK ⟨p.m, by omega⟩ = 0 :=
    gadget_DK_half w B
  have h₀ : top ⟨0, by omega⟩ = 2 * (A - (B : ℤ)) - (p.M : ℤ) := by
    dsimp only [top, Pi.sub_apply]
    rw [hH0, hQ, hV, hDK0]
    simp only [true_or, ite_true, add_zero, mul_one,
      MulZeroClass.mul_zero]
    ring
  have h₁ : top ⟨p.m, by omega⟩ = -(2 * (A - (B : ℤ))) - (p.M : ℤ) := by
    dsimp only [top, Pi.sub_apply]
    rw [hHm, hQ, hV, hDKm]
    have hne : p.m ≠ 0 := by omega
    simp only [hne, ite_false, or_true, ite_true, mul_one,
      MulZeroClass.mul_zero, add_zero, mul_neg_one]
    ring
  have hn := gadget_norms w B
  have hmul : coeffSup (mul (IdealCVP.ofList (d := 2 * p.m) p.H) z) ≤ p.F := by
    have h := coeffSup_mul_le (IdealCVP.ofList (d := 2 * p.m) p.H) z
    rw [← hn.1] at h
    exact h.trans ((Nat.mul_le_mul_left p.F hz).trans_eq (Nat.mul_one p.F))
  have hDK : coeffSup (IdealCVP.ofList (d := 2 * p.m) p.DK) ≤ p.rho := by
    rw [hn.2.2]
    exact coeffSup_le_coeffL1 _
  have hscale : p.F + p.L * p.rho ≤ p.M := by
    change p.F + p.L * p.rho ≤ 2 * (p.L * p.rho + p.nu) + p.F + 1
    omega
  have hother : ∀ i : Fin (2 * p.m),
      i ≠ ⟨0, by omega⟩ → i ≠ ⟨p.m, by omega⟩ → (top i).natAbs ≤ p.M := by
    intro i hi₀ hi₁
    have hi0 : i.val ≠ 0 := fun h => hi₀ (Fin.ext h)
    have him : i.val ≠ p.m := fun h => hi₁ (Fin.ext h)
    have htop : top i = mul (IdealCVP.ofList p.H) z i -
        (p.L : ℤ) * IdealCVP.ofList p.DK i := by
      dsimp only [top, Pi.sub_apply]
      rw [hQ, hV]
      simp [hi0, him]
    rw [htop]
    calc
      _ ≤ (mul (IdealCVP.ofList p.H) z i).natAbs +
          ((p.L : ℤ) * IdealCVP.ofList p.DK i).natAbs := Int.natAbs_sub_le _ _
      _ ≤ p.F + p.L * p.rho := by
        apply Nat.add_le_add ((natAbs_le_coeffSup _ i).trans hmul)
        simp only [Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.mul_le_mul_left p.L ((natAbs_le_coeffSup _ i).trans hDK)
      _ ≤ p.M := hscale
  have hb : coeffSup ((p.M : ℤ) • z) ≤ p.M := by
    rw [coeffSup_smul, Int.natAbs_natCast]
    exact (Nat.mul_le_mul_left p.M hz).trans_eq (Nat.mul_one p.M)
  have he := pairSup_of_centered_coefficients top ((p.M : ℤ) • z) p.M
    (2 * (A - (B : ℤ))) ⟨0, by omega⟩ ⟨p.m, by omega⟩ h₀ h₁ hother hb
  simpa only [Int.natAbs_mul, show (2 : ℤ).natAbs = 2 by decide] using he

end Power2ModuleSVPSubsetSum.Reduction
