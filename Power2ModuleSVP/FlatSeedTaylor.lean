module
public import Power2ModuleSVP.Bernstein
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Finite Taylor propagation for the derivative grid in `thm:spectral-seed`.
The proof uses the already proved sharp Bernstein inequality. A geometric
majorant gives the numerical constant without an assumed exponential bound.
-/
@[expose] public section
namespace Power2ModuleSVP
open scoped BigOperators
open Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem HasTrigDegree.contDiff_seed {q : ℕ} {f : ℝ → ℝ}
    (h : HasTrigDegree q f) : ContDiff ℝ ⊤ f := by
  obtain ⟨P, _, hP⟩ := h
  have he : f = fun t => (laurentTrig q P t).re := by
    funext t
    rw [← hP]
    rfl
  rw [he]
  change ContDiff ℝ ⊤ (Complex.reCLM ∘ laurentTrig q P)
  apply Complex.reCLM.contDiff.comp
  unfold laurentTrig
  have hc : ContDiff ℝ ⊤ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hp (Q : Polynomial ℂ) : ContDiff ℝ ⊤ (fun z : ℂ => Q.eval z) := by
    induction Q using Polynomial.induction_on' with
    | add Q R hQ hR => simpa only [Polynomial.eval_add] using hQ.add hR
    | monomial k a => simp only [Polynomial.eval_monomial]; fun_prop
  have hp' := hp P
  fun_prop

theorem seed_taylor_majorant (n : ℕ) :
    (∑ k ∈ Finset.range n, (5281 + 240 * (k : ℝ)) * (1 / 10 : ℝ) ^ k) ≤
      477690 / 81 := by
  have hgeom : HasSum (fun k : ℕ => (1 / 10 : ℝ) ^ k) (10 / 9) := by
    convert hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 10 : ℝ)‖ < 1) using 1
    norm_num
  have hweight : HasSum (fun k : ℕ => (k : ℝ) * (1 / 10 : ℝ) ^ k) (10 / 81) := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 10 : ℝ)‖ < 1) using 1
    norm_num
  have hh := (hgeom.mul_left 5281).add (hweight.mul_left 240)
  have hh' : HasSum (fun k : ℕ => (5281 + 240 * (k : ℝ)) * (1 / 10 : ℝ) ^ k)
      (477690 / 81) := by
    convert hh using 1
    · funext k; ring
    · norm_num
  exact hh'.summable.sum_le_tsum _ (fun k _ => by positivity) |>.trans_eq hh'.tsum_eq

theorem seed_power_decay (n : ℕ) : (n : ℝ) * (1 / 10 : ℝ) ^ (n + 1) ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp : (1 / 10 : ℝ) ^ (n + 1) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    push_cast
    nlinarith

/-- Propagate normalized derivative samples to a nearby angle. The finite
Taylor order is `N`; Bernstein bounds its remainder on the whole segment.
Only `N ≥ 1` is needed, rather than the eventual enormous seed cutoff. -/
theorem seed_taylor_nearby {N : ℕ} (hN : 1 ≤ N) {f : ℝ → ℝ}
    (hf : HasTrigDegree (2 * N) f)
    (hglobal : ∀ t, |f t| ≤ 2 * N) {a x : ℝ}
    (hnear : (2 * (N : ℝ)) * |x - a| ≤ 1 / 10)
    (hsample : ∀ k ≤ N, |(deriv^[k] f) a| ≤
      (5281 + 240 * (k : ℝ)) * Real.sqrt N * (2 * (N : ℝ)) ^ k) :
    |f x| < 5900 * Real.sqrt N := by
  have hs : 1 ≤ Real.sqrt (N : ℝ) := by
    exact (Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)).mpr (by exact_mod_cast hN)
  have hq : (0 : ℝ) ≤ 2 * N := by positivity
  have hpow (k : ℕ) : (2 * (N : ℝ)) ^ k * |x - a| ^ k ≤ (1 / 10 : ℝ) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hnear k
  have hsum : |taylorWithinEval f N (uIcc a x) a x| ≤
      (477690 / 81) * Real.sqrt N := by
    by_cases he : a = x
    · subst x
      rw [taylorWithinEval_self]
      have := hsample 0 (by omega)
      norm_num at this
      nlinarith
    have hu := uniqueDiffOn_uIcc he
    rw [taylor_within_apply]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1),
          ((5281 + 240 * (k : ℝ)) * (1 / 10 : ℝ) ^ k) * Real.sqrt N := by
        apply Finset.sum_le_sum
        intro k hk
        rw [smul_eq_mul, abs_mul, abs_mul, abs_inv, Nat.abs_cast, abs_pow]
        rw [iteratedDerivWithin_eq_iteratedDeriv hu
          (hf.contDiff_seed.of_le (by simp)).contDiffAt (left_mem_uIcc),
          iteratedDeriv_eq_iterate]
        have hkN : k ≤ N := by simpa using Finset.mem_range.mp hk
        have hfac : (k.factorial : ℝ)⁻¹ ≤ 1 := by
          exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos k)
        calc
          _ ≤ 1 * |x - a| ^ k *
              ((5281 + 240 * (k : ℝ)) * Real.sqrt N * (2 * (N : ℝ)) ^ k) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hfac (by positivity))
              (hsample k hkN) (abs_nonneg _) (by positivity)
          _ = ((5281 + 240 * (k : ℝ)) *
              ((2 * (N : ℝ)) ^ k * |x - a| ^ k)) * Real.sqrt N := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hpow k) (by positivity)) (Real.sqrt_nonneg _)
      _ = (∑ k ∈ Finset.range (N + 1),
          (5281 + 240 * (k : ℝ)) * (1 / 10 : ℝ) ^ k) * Real.sqrt N := by
        rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (seed_taylor_majorant _) (Real.sqrt_nonneg _)
  have hrem : |f x - taylorWithinEval f N (uIcc a x) a x| ≤ 2 := by
    by_cases he : a = x
    · subst x
      simp
    obtain ⟨y, _, hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv he
      (hf.contDiff_seed.of_le (by simp)).contDiffOn
    rw [hy, abs_div, abs_mul, abs_pow, Nat.abs_cast]
    have hb := bernstein_real_iterate hf hglobal (N + 1) y
    rw [← iteratedDeriv_eq_iterate] at hb
    push_cast at hb
    calc
      _ ≤ ((2 * (N : ℝ)) ^ (N + 1) * (2 * N) * |x - a| ^ (N + 1)) /
          (N + 1).factorial := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hb (by positivity)) (by positivity)
      _ ≤ (2 * N) * (1 / 10 : ℝ) ^ (N + 1) := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N + 1).factorial)).mpr
        have hfac : (1 : ℝ) ≤ (N + 1).factorial := by exact_mod_cast Nat.factorial_pos (N + 1)
        have hp := mul_le_mul_of_nonneg_left (hpow (N + 1)) (by positivity : (0 : ℝ) ≤ 2 * N)
        nlinarith [mul_le_mul_of_nonneg_left hfac
          (by positivity : (0 : ℝ) ≤ (2 * N) * (1 / 10 : ℝ) ^ (N + 1))]
      _ ≤ 2 := by nlinarith [seed_power_decay N]
  have htri := abs_add_le (f x - taylorWithinEval f N (uIcc a x) a x)
    (taylorWithinEval f N (uIcc a x) a x)
  simp only [sub_add_cancel] at htri
  nlinarith

end Power2ModuleSVP
