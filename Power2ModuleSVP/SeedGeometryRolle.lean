module

public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
Repeated Rolle and quantitative interpolation for the seven-cell argument.
The derivative family is explicit, so these lemmas can be applied to a
trigonometric wave without choosing a representation of higher derivatives.
-/

@[expose] public section
namespace Power2ModuleSVP
open Polynomial Set
open scoped BigOperators
noncomputable section

/-- Repeated Rolle with ordered nodes. Endpoints are allowed in the final
conclusion, including the zero-order case. -/
theorem seed_iterated_rolle (F : ℕ → ℝ → ℝ)
    (hF : ∀ r x, HasDerivAt (F r) (F (r + 1) x) x)
    (n : ℕ) (node : Fin (n + 1) → ℝ) (hnode : StrictMono node)
    (hzero : ∀ i, F 0 (node i) = 0) :
    ∃ x ∈ Icc (node 0) (node (Fin.last n)), F n x = 0 := by
  induction n generalizing F with
  | zero => exact ⟨node 0, ⟨le_rfl, le_rfl⟩, hzero 0⟩
  | succ n ih =>
    have hc : Continuous (F 0) := continuous_iff_continuousAt.mpr
      (fun x => (hF 0 x).continuousAt)
    have hex : ∀ i : Fin (n + 1), ∃ x ∈ Ioo (node i.castSucc) (node i.succ),
        F 1 x = 0 := by
      intro i
      exact exists_hasDerivAt_eq_zero
        (hnode (show i.castSucc < i.succ from Fin.castSucc_lt_succ)) hc.continuousOn
        ((hzero _).trans (hzero _).symm) (fun x _ => hF 0 x)
    choose mid hmid hmidzero using hex
    have hmono : StrictMono mid := by
      intro i j hij
      have hi : i.succ ≤ j.castSucc := by simpa using hij
      exact (hmid i).2.trans_le ((hnode.monotone hi).trans (hmid j).1.le)
    obtain ⟨x, hx, hz⟩ := ih (fun r => F (r + 1))
      (fun r x => hF (r + 1) x) mid hmono hmidzero
    refine ⟨x, ⟨?_, ?_⟩, hz⟩
    · exact (hmid 0).1.le.trans hx.1
    · exact hx.2.trans (hmid (Fin.last n)).2.le

/-- At some point, the `n`th derivative agrees with that of any interpolating
polynomial at `n+1` ordered nodes. -/
theorem seed_interpolation_derivative_point (F : ℕ → ℝ → ℝ)
    (hF : ∀ r x, HasDerivAt (F r) (F (r + 1) x) x)
    (n : ℕ) (node : Fin (n + 1) → ℝ) (hnode : StrictMono node)
    (p : ℝ[X]) (hp : ∀ i, p.eval (node i) = F 0 (node i)) :
    ∃ x ∈ Icc (node 0) (node (Fin.last n)),
      F n x = (Polynomial.derivative^[n] p).eval x := by
  have hd : ∀ r x, HasDerivAt
      (fun x => F r x - (Polynomial.derivative^[r] p).eval x)
      (F (r + 1) x - (Polynomial.derivative^[r + 1] p).eval x) x := by
    intro r x
    rw [Function.iterate_succ_apply']
    convert! (hF r x).sub ((Polynomial.derivative^[r] p).hasDerivAt x) using 1
  obtain ⟨x, hx, he⟩ := seed_iterated_rolle
    (fun r x => F r x - (Polynomial.derivative^[r] p).eval x) hd n node hnode
    (fun i => by simp [hp i])
  exact ⟨x, hx, sub_eq_zero.mp he⟩

/-- A separated-node interpolation bound. The factorial constant is coarse
but retains the margin used for orders one, two and three in the seed. -/
theorem seed_interpolation_derivative_bound (F : ℕ → ℝ → ℝ)
    (hF : ∀ r x, HasDerivAt (F r) (F (r + 1) x) x)
    (n : ℕ) (node : Fin (n + 1) → ℝ) (hnode : StrictMono node)
    {a ε : ℝ} (ha : 0 < a) (hε : 0 ≤ ε)
    (hsep : ∀ i j, i ≠ j → a ≤ |node i - node j|)
    (hsmall : ∀ i, |F 0 (node i)| ≤ ε) :
    ∃ x ∈ Icc (node 0) (node (Fin.last n)),
      |F n x| ≤ ((n + 1 : ℕ) : ℝ) * n.factorial * ε / a ^ n := by
  classical
  let p : ℝ[X] := Lagrange.interpolate Finset.univ node (fun i => F 0 (node i))
  have hp : ∀ i, p.eval (node i) = F 0 (node i) := by
    intro i
    exact Lagrange.eval_interpolate_at_node (fun i => F 0 (node i))
      hnode.injective.injOn (Finset.mem_univ i)
  obtain ⟨x, hx, he⟩ := seed_interpolation_derivative_point F hF n node hnode p hp
  have hderiv : (Polynomial.derivative^[n] p).eval x =
      (n.factorial : ℝ) * ∑ i : Fin (n + 1),
        F 0 (node i) / ∏ j ∈ Finset.univ.erase i, (node i - node j) := by
    dsimp [p]
    rw [Lagrange.iterate_derivative_interpolate (fun i => F 0 (node i)) hnode.injective.injOn
      (by simp : n < (Finset.univ : Finset (Fin (n + 1))).card)]
    simp [Polynomial.eval_finsetSum]
  have hden : ∀ i : Fin (n + 1), a ^ n ≤
      |∏ j ∈ Finset.univ.erase i, (node i - node j)| := by
    intro i
    rw [Finset.abs_prod]
    calc
      a ^ n = ∏ _j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, a := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => ha.le)
        (fun j hj => hsep i j (Finset.ne_of_mem_erase hj).symm)
  refine ⟨x, hx, ?_⟩
  rw [he, hderiv, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ (n.factorial : ℝ) * ∑ i : Fin (n + 1),
        |F 0 (node i) / ∏ j ∈ Finset.univ.erase i, (node i - node j)| := by
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
    _ ≤ (n.factorial : ℝ) * ∑ _i : Fin (n + 1), ε / a ^ n := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_div]
      exact div_le_div₀ hε (hsmall i) (pow_pos ha n) (hden i)
    _ = _ := by simp; ring

end
end Power2ModuleSVP
