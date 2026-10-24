import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! The sparse multiplicity bound, proved by repeatedly killing one coefficient
with the Euler differential operator `X * derivative - a`. -/
namespace Rank2ModuleSVP
noncomputable section
open Polynomial

variable {q : ℕ} [Fact q.Prime]

private def killTerm (a : ℕ) (f : (ZMod q)[X]) : (ZMod q)[X] :=
  X * derivative f - C (a : ZMod q) * f

private theorem killTerm_coeff (a n : ℕ) (f : (ZMod q)[X]) :
    (killTerm a f).coeff n = ((n : ZMod q)-a) * f.coeff n := by
  cases n with
  | zero => simp [killTerm]
  | succ n => simp [killTerm, coeff_X_mul, coeff_derivative]; ring

private theorem killTerm_support (f : (ZMod q)[X]) (hd : f.natDegree < q)
    (a : ℕ) (ha : a ∈ f.support) : (killTerm a f).support = f.support.erase a := by
  ext n
  rw [mem_support_iff, killTerm_coeff, mul_ne_zero_iff, Finset.mem_erase, mem_support_iff]
  have hal : a < q := (le_natDegree_of_mem_supp a ha).trans_lt hd
  by_cases hn : f.coeff n = 0
  · simp [hn]
  · have hnl : n < q := (le_natDegree_of_ne_zero hn).trans_lt hd
    have he : (n : ZMod q) = (a : ZMod q) ↔ n = a :=
      by rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hnl, Nat.mod_eq_of_lt hal]
    simp [hn, sub_ne_zero, he, ne_comm]

/-- A nonzero degree-<q polynomial has multiplicity at one smaller than its
number of nonzero coefficients. This is `sparse-tools` (ii). -/
theorem sparse_tools_ii (f : (ZMod q)[X]) (hf : f ≠ 0) (hd : f.natDegree < q) :
    f.rootMultiplicity 1 < f.support.card := by
  classical
  generalize hs : f.support.card = s
  induction s using Nat.strong_induction_on generalizing f with
  | h s ih =>
    have hne : f.support.Nonempty := support_nonempty.mpr hf
    have hpos := Finset.card_pos.mpr hne
    obtain ⟨a, ha⟩ := hne
    by_cases hcard : f.support.card = 1
    · obtain ⟨n, c, hc, rfl⟩ := card_support_eq_one.mp hcard
      have hnroot : ¬ (C c * X ^ n : (ZMod q)[X]).IsRoot 1 := by simp [IsRoot, hc]
      rw [rootMultiplicity_eq_zero hnroot]
      omega
    · let g := killTerm a f
      have hgSupp : g.support = f.support.erase a := killTerm_support f hd a ha
      have hgc : g.support.card = f.support.card - 1 := by rw [hgSupp, Finset.card_erase_of_mem ha]
      have hg : g ≠ 0 := by
        intro hz
        have := hpos
        simp [hz] at hgc
        omega
      have hgd : g.natDegree < q := by
        apply (natDegree_le_natDegree (degree_le_degree ?_)).trans_lt hd
        have hm : g.natDegree ∈ g.support := natDegree_mem_support_of_nonzero hg
        rw [hgSupp] at hm
        exact mem_support_iff.mp (Finset.mem_erase.mp hm).2
      have hi := ih g.support.card (by omega) g hg hgd rfl
      have hm : f.rootMultiplicity 1 - 1 ≤ g.rootMultiplicity 1 := by
        apply (le_rootMultiplicity_iff hg).mpr
        apply dvd_sub
        · exact dvd_mul_of_dvd_right (pow_sub_one_dvd_derivative_of_pow_dvd
            (f.pow_rootMultiplicity_dvd 1)) X
        · exact dvd_mul_of_dvd_right
            (dvd_trans (pow_dvd_pow _ (Nat.sub_le _ _)) (f.pow_rootMultiplicity_dvd 1)) (C (a : ZMod q))
      omega

end
end Rank2ModuleSVP
