import Power2ModuleSVPSubsetSum.Reduction.Construction
import Power2ModuleSVPSubsetSum.Rigidity.Parameters

/-!
# List-to-coefficient parameter bridge

The executable list program computes the coefficient model's exact l1 norms and scales.

Paper: `paper/power2svp-subsetsum.pdf`, equations (4.1)–(4.3).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Power2ModuleSVPSubsetSum.Reduction
open Power2ModuleSVP IdealCVP.Cyclotomic Rigidity

/-- The list l1 norm equals the coefficient l1 norm for an exact-length array. -/
theorem listL1_eq_coeffL1 {n : ℕ} (a : List ℤ) (ha : a.length = n) :
    listL1 a = coeffL1 (IdealCVP.ofList (d := n) a) := by
  subst n
  conv_lhs => rw [← IdealCVP.toList_ofList a]
  simp [listL1, coeffL1, IdealCVP.toList, List.map_ofFn, List.sum_ofFn]

/-- The list filter `D` is the same coefficient vector used in Section 3. -/
theorem ofList_filterD (m : ℕ) :
    IdealCVP.ofList (d := 2 * m) (filterD m) = D m := by
  ext i
  simp only [IdealCVP.ofList, filterD, D, atom, Pi.add_apply]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range, i.isLt, Option.map_some, Option.getD_some]
  split_ifs <;> omega

/-- The list filter `K` is exactly the balanced-base-five coefficient polynomial. -/
theorem ofList_filterK (m : ℕ) :
    IdealCVP.ofList (d := 2 * m) (filterK m) = K m := by
  ext i
  rw [K_apply]
  simp [IdealCVP.ofList, filterK, List.getD_eq_getElem?_getD, i.isLt]

/-- All arrays retained by the executable gadget have the exact output length. -/
theorem gadget_lengths (w : List ℕ) (B : ℕ) :
    let p := gadget w B
    p.H.length = 2 * p.m ∧ p.V.length = 2 * p.m ∧
      p.DK.length = 2 * p.m ∧ p.u.length = 2 * p.m ∧ p.Q.length = 2 * p.m := by
  simp [gadget, IdealCVP.negacyclicMul, scale, mask, IdealCVP.listAdd]

/-- The executable scalar fields contain the exact norms, including `rho`. -/
theorem gadget_norms (w : List ℕ) (B : ℕ) :
    let p := gadget w B
    p.F = coeffL1 (IdealCVP.ofList (d := 2 * p.m) p.H) ∧
      p.nu = coeffL1 (IdealCVP.ofList (d := 2 * p.m) p.V) ∧
      p.rho = coeffL1 (IdealCVP.ofList (d := 2 * p.m) p.DK) := by
  have hl := gadget_lengths w B
  exact ⟨listL1_eq_coeffL1 _ hl.1, listL1_eq_coeffL1 _ hl.2.1,
    listL1_eq_coeffL1 _ hl.2.2.1⟩

/-- The executable `DK` array is the product of the two Section 3 filters. -/
theorem gadget_DK (w : List ℕ) (B : ℕ) :
    let p := gadget w B
    IdealCVP.ofList (d := 2 * p.m) p.DK = mul (D p.m) (K p.m) := by
  simp only [gadget, IdealCVP.ofList_negacyclicMul, ofList_filterD, ofList_filterK]

/-- First norm parameter agrees with the coefficient model. -/
theorem gadget_F (w : List ℕ) (B : ℕ) :
    let p := gadget w B
    p.F = F (IdealCVP.ofList (d := 2 * p.m) p.H) := (gadget_norms w B).1

/-- Error norm parameter agrees with the coefficient model. -/
theorem gadget_nu (w : List ℕ) (B : ℕ) :
    let p := gadget w B
    p.nu = nu (IdealCVP.ofList (d := 2 * p.m) p.V) := (gadget_norms w B).2.1

/-- The computed filter norm is the exact Section 3 norm. -/
theorem gadget_rho (w : List ℕ) (B : ℕ) :
    (gadget w B).rho = rho (gadget w B).m := by
  rw [(gadget_norms w B).2.2, gadget_DK]
  rfl

/-- The secondary scale agrees with the coefficient formula. -/
theorem gadget_L (w : List ℕ) (B : ℕ) :
    let p := gadget w B
    p.L = L (IdealCVP.ofList (d := 2 * p.m) p.H) (IdealCVP.ofList p.V) := by
  change (gadget w B).F + (gadget w B).nu + 1 = _
  rw [gadget_F, gadget_nu]
  rfl

/-- The main scale agrees with the coefficient formula. -/
theorem gadget_M (w : List ℕ) (B : ℕ) :
    let p := gadget w B
    p.M = M (IdealCVP.ofList (d := 2 * p.m) p.H) (IdealCVP.ofList p.V) := by
  change 2 * ((gadget w B).L * (gadget w B).rho + (gadget w B).nu) +
    (gadget w B).F + 1 = _
  rw [gadget_L, gadget_rho, gadget_nu, gadget_F]
  rfl

/-- The stored multiplier filter agrees with Proposition 3.3. -/
theorem gadget_Q (w : List ℕ) (B : ℕ) :
    let p := gadget w B
    IdealCVP.ofList (d := 2 * p.m) p.Q =
      Q (IdealCVP.ofList (d := 2 * p.m) p.H) (IdealCVP.ofList p.V) := by
  let p := gadget w B
  have hQ : IdealCVP.ofList (d := 2 * p.m) p.Q =
      (p.M : ℤ) • D p.m + (p.L : ℤ) • mul (D p.m) (K p.m) := by
    calc
      _ = IdealCVP.ofList (d := 2 * p.m)
          (scale (2 * p.m) (p.M : ℤ) (filterD p.m)) +
          IdealCVP.ofList (d := 2 * p.m)
            (scale (2 * p.m) (p.L : ℤ) p.DK) :=
        IdealCVP.ofList_listAdd (2 * p.m) _ _
      _ = _ := by
        rw [ofList_scale, ofList_scale, ofList_filterD]
        rw [show IdealCVP.ofList (d := 2 * p.m) p.DK =
          mul (D p.m) (K p.m) from gadget_DK w B]
  change IdealCVP.ofList (d := 2 * p.m) p.Q = _
  rw [hQ, Q]
  have hm := gadget_M w B
  have hl := gadget_L w B
  dsimp only at hm hl
  rw [← hm, ← hl]

end Power2ModuleSVPSubsetSum.Reduction
