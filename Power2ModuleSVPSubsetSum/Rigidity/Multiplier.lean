import Power2ModuleSVPSubsetSum.Rigidity.Parameters
import Power2ModuleSVPSubsetSum.Rigidity.Support
import Power2ModuleSVPSubsetSum.Rigidity.Skew

/-!
# Multiplier rigidity

The explicit scale separation first bounds the opposite-pair mass, then forces every
occupied pair to lie in the kernel of the skew filter. Support rigidity finishes the proof.

Paper: `paper/power2svp-subsetsum.pdf`, Proposition 3.3.
-/

namespace Power2ModuleSVPSubsetSum.Rigidity
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- Proposition 3.3 with the exact norms and scales of the paper. -/
theorem multiplier_rigidity {m : ℕ} (hm : 0 < m) (H V b z : Coeff (2 * m))
    (hz : coeffSup z ≤ 1)
    (hshort : coeffSup (mul H z - mul (Q H V + V) b) ≤ M H V) :
    b = 0 ∨ SignedMonomial b := by
  let r := mul (D m) b
  let v := mul (D m) (mul (K m) b)
  let e := mul V b - mul H z
  have hr : coeffSup r ≤ 1 := filter_mass_le_one hm H V b z hz hshort
  have hb : coeffSup b ≤ 1 := (coeffSup_le_D_mul hm b).trans hr
  have he : coeffSup e ≤ nu V + F H := by
    calc
      _ ≤ coeffSup (mul V b) + coeffSup (mul H z) := coeffSup_sub_le _ _
      _ ≤ nu V * coeffSup b + F H * coeffSup z :=
        Nat.add_le_add (coeffSup_mul_le V b) (coeffSup_mul_le H z)
      _ ≤ nu V * 1 + F H * 1 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hz)
      _ = _ := by omega
  have hidentity : (M H V : ℤ) • r + (L H V : ℤ) • v + e =
      -(mul H z - mul (Q H V + V) b) := by
    dsimp only [r, v, e]
    simp only [Q, mul_add_left, mul_smul_left, coeff_mul_assoc (by omega : 0 < 2 * m)]
    abel
  have hcoord (i : Fin (2 * m)) : r i * v i ≤ 0 := by
    apply saturated_coordinate (M H V) (L H V) (r i) (v i) (e i)
    · rw [← Int.natCast_natAbs]
      exact_mod_cast (coeffSup_le_iff r 1).mp hr i
    · have hi := (natAbs_le_coeffSup e i).trans he
      have hi' : |e i| ≤ ((nu V + F H : ℕ) : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hi
      have hL : (L H V : ℤ) = (F H : ℤ) + (nu V : ℤ) + 1 := by
        simp [L]
      push_cast at hi'
      omega
    · have hi := congrFun hidentity i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at hi
      rw [hi, abs_neg, ← Int.natCast_natAbs]
      exact_mod_cast (natAbs_le_coeffSup _ i).trans hshort
  have hsum : ∑ i, r i * v i = 0 := D_K_inner_zero hm b
  have hzero (i : Fin (2 * m)) : r i * v i = 0 := by
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin (2 * m))), 0 ≤ -(r j * v j) := by
      intro j _
      exact neg_nonneg.mpr (hcoord j)
    have hsum' : ∑ j, -(r j * v j) = 0 := by rw [Finset.sum_neg_distrib, hsum, neg_zero]
    have hi : -(r i * v i) ≤ 0 := by
      simpa [hsum'] using Finset.single_le_sum hnonneg (Finset.mem_univ i)
    exact le_antisymm (hcoord i) (by omega)
  apply support_rigidity hm b hr
  intro j hocc
  have hmass : |b ⟨j.val, by omega⟩| + |b ⟨j.val + m, by omega⟩| ≤ 1 :=
    (pair_mass_le hm b j).trans (by exact_mod_cast hr)
  have hrl : r ⟨j.val, by omega⟩ ≠ 0 := by
    dsimp only [r]
    rw [D_mul_low hm]
    intro h
    have hEq := sub_eq_zero.mp h
    rcases hocc with hocc | hocc
    · have hpos : 1 ≤ |b ⟨j.val, by omega⟩| := by
        have := abs_pos.mpr hocc
        omega
      rw [← hEq] at hmass
      omega
    · have hpos : 1 ≤ |b ⟨j.val + m, by omega⟩| := by
        have := abs_pos.mpr hocc
        omega
      rw [hEq] at hmass
      omega
  have hrh : r ⟨j.val + m, by omega⟩ ≠ 0 := by
    dsimp only [r]
    rw [D_mul_high hm]
    intro h
    have hEq : b ⟨j.val, by omega⟩ = -b ⟨j.val + m, by omega⟩ := by omega
    rw [hEq, abs_neg] at hmass
    have hz : b ⟨j.val + m, by omega⟩ = 0 := by
      have := abs_nonneg (b ⟨j.val + m, by omega⟩)
      have : |b ⟨j.val + m, by omega⟩| = 0 := by omega
      exact abs_eq_zero.mp this
    rcases hocc with hocc | hocc <;> simp_all
  have hvl := (mul_eq_zero.mp (hzero ⟨j.val, by omega⟩)).resolve_left hrl
  have hvh := (mul_eq_zero.mp (hzero ⟨j.val + m, by omega⟩)).resolve_left hrh
  dsimp only [v] at hvl hvh
  rw [D_mul_low hm] at hvl
  rw [D_mul_high hm] at hvh
  constructor <;> omega

/-- The constructed filter plus the error polynomial has trivial multiplication kernel. -/
theorem Q_add_V_mul_eq_zero_iff {m : ℕ} (hm : 0 < m)
    (H V b : Coeff (2 * m)) : mul (Q H V + V) b = 0 ↔ b = 0 := by
  constructor
  · intro hker
    have hshort : coeffSup (mul H 0 - mul (Q H V + V) b) ≤ M H V := by
      simp [hker]
    rcases multiplier_rigidity hm H V b 0 (by simp) hshort with hb | hb
    · exact hb
    · have hn : coeffSup (Q H V + V) = 0 := by
        rw [← SignedMonomial.coeffSup_mul hb (Q H V + V),
          IdealCVP.Cyclotomic.mul_comm b (Q H V + V), hker, coeffSup_zero]
      exact False.elim (Q_add_V_ne_zero hm H V ((coeffSup_eq_zero_iff _).mp hn))
  · rintro rfl
    exact mul_zero _

/-- Multiplication by the constructed filter plus error polynomial is injective. -/
theorem Q_add_V_mul_injective {m : ℕ} (hm : 0 < m) (H V : Coeff (2 * m)) :
    Function.Injective (mul (Q H V + V)) := by
  intro b c h
  apply sub_eq_zero.mp
  apply (Q_add_V_mul_eq_zero_iff hm H V (b - c)).mp
  simp only [sub_eq_add_neg, mul_add, mul_neg, h, add_neg_cancel]

end Power2ModuleSVPSubsetSum.Rigidity
