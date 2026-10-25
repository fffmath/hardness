import Mathlib.Data.Nat.Factorial.Basic
import Rank2ModuleSVP.AsymptoticsAux

/-! # Uniform completion counts and coordinate ratios

v2 Theorem 3.4 and its fixed-coordinate consequences.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
namespace Rank2ModuleSVP
open scoped BigOperators
noncomputable section

/-- An integer-power domination lemma avoids logarithmic estimates with moving exponents. -/
theorem wan_power_domination {q k m : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hpow : (2 * k) ^ 1000 ≤ q) (hm : k + 4 ≤ m)
    (hexp : 2 * m ≤ 1000 * (m - k - 4)) :
    (2 * (k : ℝ)) ^ m * (q : ℝ) ^ (((m - k + 2 : ℕ) : ℝ) / 2) ≤
      (q : ℝ) ^ (m - k - 1) := by
  have hb : (1 : ℝ) ≤ 2 * k := by exact_mod_cast (by omega : 1 ≤ 2 * k)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpR : (2 * (k : ℝ)) ^ 1000 ≤ (q : ℝ) := by exact_mod_cast hpow
  have hp : (2 * (k : ℝ)) ^ (2 * m) ≤ (q : ℝ) ^ (m - k - 4) := by
    calc
      _ ≤ (2 * (k : ℝ)) ^ (1000 * (m - k - 4)) := pow_le_pow_right₀ hb hexp
      _ = ((2 * (k : ℝ)) ^ 1000) ^ (m - k - 4) := by rw [pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hpR _
  have hhalf : ((q : ℝ) ^ (((m - k + 2 : ℕ) : ℝ) / 2)) ^ 2 =
      (q : ℝ) ^ (m - k + 2) := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num only [Nat.cast_ofNat]
    rw [show (((m - k + 2 : ℕ) : ℝ) / 2) * (2 : ℝ) = ((m - k + 2 : ℕ) : ℝ) by ring,
      Real.rpow_natCast]
  have hsq : ((2 * (k : ℝ)) ^ m * (q : ℝ) ^ (((m - k + 2 : ℕ) : ℝ) / 2)) ^ 2 ≤
      ((q : ℝ) ^ (m - k - 1)) ^ 2 := by
    rw [mul_pow, ← pow_mul, show m * 2 = 2 * m by omega, hhalf]
    calc
      _ ≤ (q : ℝ) ^ (m - k - 4) * (q : ℝ) ^ (m - k + 2) := by gcongr
      _ = (q : ℝ) ^ ((m - k - 4) + (m - k + 2)) := (pow_add _ _ _).symm
      _ = ((q : ℝ) ^ (m - k - 1)) ^ 2 := by
        rw [← pow_mul]; congr 1; omega
  have hn : 0 ≤ (2 * (k : ℝ)) ^ m * (q : ℝ) ^ (((m - k + 2 : ℕ) : ℝ) / 2) := by positivity
  have hn' : 0 ≤ (q : ℝ) ^ (m - k - 1) := by positivity
  nlinarith

/-- All three absolute Wan errors share this uniform envelope. -/
theorem wan_errors_envelope {q k m : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hpow : (2 * k) ^ 1000 ≤ q) (hm : k + 4 ≤ m)
    (hexp : 2 * m ≤ 1000 * (m - k - 4)) :
    wanError q k m ≤ (q : ℝ) ^ (m - k - 1) ∧
    wanCollisionError q k m ≤ (q : ℝ) ^ (m - k - 1) ∧
    wanCoordinateError q k m ≤ (q : ℝ) ^ (m - k - 1) := by
  have hdom := wan_power_domination hq hk hpow hm hexp
  have hb : (1 : ℝ) ≤ 2 * k := by exact_mod_cast (by omega : 1 ≤ 2 * k)
  have hp : (2 * (k : ℝ)) ^ (m - 1) ≤ (2 * (k : ℝ)) ^ m :=
    pow_le_pow_right₀ hb (by omega)
  have hhalf : (q : ℝ) ^ (((m - k + 1 : ℕ) : ℝ) / 2) ≤
      (q : ℝ) ^ (((m - k + 2 : ℕ) : ℝ) / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq)
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast (by omega : m - k + 1 ≤ m - k + 2)) (by norm_num)
  unfold wanError wanCollisionError wanCoordinateError
  have hn : 0 ≤ (2 * (k : ℝ)) ^ m := by positivity
  have hqn : 0 ≤ (q : ℝ) ^ (((m - k + 2 : ℕ) : ℝ) / 2) := by positivity
  constructor
  · nlinarith
  constructor
  · calc
      _ ≤ (1 / 2 : ℝ) * (2 * (k : ℝ)) ^ m * (q : ℝ) ^ (((m - k + 2 : ℕ) : ℝ) / 2) := by gcongr
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ (1 / 2 : ℝ) * (2 * (k : ℝ)) ^ m * (q : ℝ) ^ (((m - k + 2 : ℕ) : ℝ) / 2) := by gcongr
      _ ≤ _ := by nlinarith

/-- v2 Theorem 3.4, in factorial-multiplied form. -/
theorem uniform_completions_sharp (hWan : WanPowerSumEstimates)
    {q k : ℕ} [NeZero q] (hq : q.Prime) (hk : cntK0 ≤ k)
    (hpow : (2 * k) ^ cntC0 ≤ q)
    (u : Fin k → ZMod q) (P : Finset (ZMod q)) (η : Coeff ℤ q)
    (hP : P.card ≤ Nat.sqrt k) (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1)
    (hu : u ⟨0, by have : 100000000 ≤ k := hk; omega⟩ = (cntH k : ZMod q)) :
    let m := cntH k - (fixedOnes P η).card
    (13 / 16 : ℝ) * wanMain q k m ≤
      (m.factorial : ℝ) * (completions k (cntH k) u P η).card ∧
    (m.factorial : ℝ) * (completions k (cntH k) u P η).card ≤
      (17 / 16 : ℝ) * wanMain q k m := by
  let t := (fixedOnes P η).card
  let m := cntH k - t
  have ht : t ≤ Nat.sqrt k := (Finset.card_filter_le P _).trans hP
  obtain ⟨hk2, hkm, hmle, hmq, hexp⟩ := cnt_parameter_range hk hpow ht
  have htm : m + t = cntH k := by dsimp [m]; omega
  obtain ⟨hl, hu'⟩ := completions_count_bounds hWan hq k (cntH k) m hk2
    (by dsimp [m]; omega) hmq u hu P η hη htm
  obtain ⟨hA, hC, hE⟩ := wan_errors_envelope (by have := hq.two_le; omega)
    (by omega) hpow hkm hexp
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (by have := hq.two_le; omega : 1 ≤ q)
  have hn : 0 ≤ (q : ℝ) ^ (m - k) := by positivity
  have hprev : (q : ℝ) ^ (m - k - 1) ≤ (q : ℝ) ^ (m - k) :=
    pow_le_pow_right₀ hqR (by omega)
  have hC' : wanCollisionError q k m ≤ (q : ℝ) ^ (m - k) := hC.trans hprev
  have hE' : wanCoordinateError q k m ≤ (q : ℝ) ^ (m - k) := hE.trans hprev
  have hp := cnt_q_polynomial hk hpow
  have hPk : P.card ≤ k := hP.trans (Nat.sqrt_le_self k)
  have hk1 : 1 ≤ k := by omega
  have hkpow : k ^ 2 ≤ k ^ 4 := Nat.pow_le_pow_right hk1 (by omega)
  have hpoly : 16 * (m ^ 2 + m * P.card) + 8 ≤ q := by
    have hmm : m ≤ 2 * k := hmle
    have hsq : m ^ 2 ≤ (2 * k) ^ 2 := Nat.pow_le_pow_left hmm 2
    have hmul : m * P.card ≤ 2 * k * k := Nat.mul_le_mul hmm hPk
    nlinarith
  have hpolyR : 16 * ((m : ℝ) ^ 2 + (m : ℝ) * P.card) + 8 ≤ q := by exact_mod_cast hpoly
  have hmain : wanMain q k m = (q : ℝ) ^ (m - k) * (q : ℝ) := by
    unfold wanMain
    rw [pow_succ]
  have hq16 : (16 : ℝ) ≤ q := by
    have hk4 : 1 ≤ k ^ 4 := Nat.one_le_pow _ _ hk1
    have : 16 ≤ q := by omega
    exact_mod_cast this
  have hAr : wanError q k m ≤ wanMain q k m / 16 := by
    have hh := mul_le_mul_of_nonneg_right hq16 hn
    rw [hmain]
    nlinarith [hA.trans hprev]
  have hbudget : (m : ℝ) ^ 2 * ((q : ℝ) ^ (m - k) + wanCollisionError q k m) +
      (m : ℝ) * P.card * ((q : ℝ) ^ (m - k) + wanCoordinateError q k m) ≤
      wanMain q k m / 8 := by
    calc
      _ ≤ 2 * ((m : ℝ) ^ 2 + (m : ℝ) * P.card) * (q : ℝ) ^ (m - k) := by
        nlinarith [mul_le_mul_of_nonneg_left hC' (sq_nonneg (m : ℝ)),
          mul_le_mul_of_nonneg_left hE' (show 0 ≤ (m : ℝ) * P.card by positivity)]
      _ ≤ _ := by
        rw [hmain]
        nlinarith [mul_le_mul_of_nonneg_right hpolyR hn]
  have hMn : 0 ≤ wanMain q k m := by unfold wanMain; positivity
  change (13 / 16 : ℝ) * wanMain q k m ≤ _ ∧ _ ≤ (17 / 16 : ℝ) * wanMain q k m
  constructor <;> nlinarith

/-- v2 Theorem 3.4 with the advertised factors 3/4 and 5/4. -/
theorem uniform_completions (hWan : WanPowerSumEstimates)
    {q k : ℕ} [NeZero q] (hq : q.Prime) (hk : cntK0 ≤ k)
    (hpow : (2 * k) ^ cntC0 ≤ q)
    (u : Fin k → ZMod q) (P : Finset (ZMod q)) (η : Coeff ℤ q)
    (hP : P.card ≤ Nat.sqrt k) (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1)
    (hu : u ⟨0, by have : 100000000 ≤ k := hk; omega⟩ = (cntH k : ZMod q)) :
    let m := cntH k - (fixedOnes P η).card
    (3 / 4 : ℝ) * wanMain q k m ≤
      (m.factorial : ℝ) * (completions k (cntH k) u P η).card ∧
    (m.factorial : ℝ) * (completions k (cntH k) u P η).card ≤
      (5 / 4 : ℝ) * wanMain q k m := by
  obtain ⟨hl, hu'⟩ := uniform_completions_sharp hWan hq hk hpow u P η hP hη hu
  have hM : 0 ≤ wanMain q k (cntH k - (fixedOnes P η).card) := by
    unfold wanMain; positivity
  dsimp only at hl hu' ⊢
  constructor <;> linarith

/-- Theorem 3.4 with the paper's main term q^(h-t-k+1)/(h-t)!. -/
theorem uniform_completions_div (hWan : WanPowerSumEstimates)
    {q k : ℕ} [NeZero q] (hq : q.Prime) (hk : cntK0 ≤ k)
    (hpow : (2 * k) ^ cntC0 ≤ q)
    (u : Fin k → ZMod q) (P : Finset (ZMod q)) (η : Coeff ℤ q)
    (hP : P.card ≤ Nat.sqrt k) (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1)
    (hu : u ⟨0, by have : 100000000 ≤ k := hk; omega⟩ = (cntH k : ZMod q)) :
    let m := cntH k - (fixedOnes P η).card
    (3 / 4 : ℝ) * (wanMain q k m / (m.factorial : ℝ)) ≤
      (completions k (cntH k) u P η).card ∧
    ((completions k (cntH k) u P η).card : ℝ) ≤
      (5 / 4 : ℝ) * (wanMain q k m / (m.factorial : ℝ)) := by
  obtain ⟨hl, hu'⟩ := uniform_completions hWan hq hk hpow u P η hP hη hu
  dsimp only
  have hf : (0 : ℝ) < ((cntH k - (fixedOnes P η).card).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  constructor
  · rw [← mul_div_assoc, div_le_iff₀ hf]
    nlinarith only [hl]
  · rw [← mul_div_assoc, le_div_iff₀ hf]
    nlinarith only [hu']

/-- Nonemptiness uniformly over the syndrome and prescribed bits. -/
theorem uniform_completions_nonempty (hWan : WanPowerSumEstimates)
    {q k : ℕ} [NeZero q] (hq : q.Prime) (hk : cntK0 ≤ k)
    (hpow : (2 * k) ^ cntC0 ≤ q)
    (u : Fin k → ZMod q) (P : Finset (ZMod q)) (η : Coeff ℤ q)
    (hP : P.card ≤ Nat.sqrt k) (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1)
    (hu : u ⟨0, by have : 100000000 ≤ k := hk; omega⟩ = (cntH k : ZMod q)) :
    (completions k (cntH k) u P η).Nonempty := by
  have hl := (uniform_completions hWan hq hk hpow u P η hP hη hu).1
  have hpos : 0 < wanMain q k (cntH k - (fixedOnes P η).card) := by
    unfold wanMain
    exact pow_pos (by exact_mod_cast hq.pos) _
  apply Finset.card_pos.mp
  by_contra hh
  have hz : (completions k (cntH k) u P η).card = 0 := by omega
  rw [hz, Nat.cast_zero, mul_zero] at hl
  linarith

/-- The factorial comparison in the fixed-coordinate estimate, for arbitrary r. -/
theorem factorial_ratio_le_power {m h r : ℕ} (hr : r ≤ m) (hm : m ≤ h) :
    (m.factorial : ℝ) ≤ (h : ℝ) ^ r * ((m - r).factorial : ℝ) := by
  have hh := Nat.descFactorial_le_pow m r
  have he := Nat.factorial_mul_descFactorial hr
  have hpow := Nat.pow_le_pow_left hm r
  have hn : m.factorial ≤ h ^ r * (m - r).factorial := by
    rw [← he]
    exact (Nat.mul_le_mul_left _ (hh.trans hpow)).trans_eq (Nat.mul_comm _ _)
  exact_mod_cast hn

/-- Exact additional-one bookkeeping. -/
theorem fixedOnes_extend {q : ℕ} [NeZero q] (P Q : Finset (ZMod q))
    (η : Coeff ℤ q) (_hPQ : Disjoint P Q) :
    fixedOnes (P ∪ Q) (fun a => if a ∈ Q then 1 else η a) = fixedOnes P η ∪ Q := by
  classical
  ext a
  by_cases ha : a ∈ Q
  · simp [fixedOnes, ha]
  · simp [fixedOnes, ha]

/-- The strict coordinate ratio in v2 §4.3, in cross-multiplied form.
It holds for any number of added coordinates within the square-root budget. -/
theorem fixed_coordinate_ratio (hWan : WanPowerSumEstimates)
    {q k : ℕ} [NeZero q] (hq : q.Prime) (hk : cntK0 ≤ k)
    (hpow : (2 * k) ^ cntC0 ≤ q)
    (u : Fin k → ZMod q) (P J : Finset (ZMod q)) (η : Coeff ℤ q)
    (hsize : P.card + J.card ≤ Nat.sqrt k) (hPJ : Disjoint P J)
    (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1)
    (hu : u ⟨0, by have : 100000000 ≤ k := hk; omega⟩ = (cntH k : ZMod q)) :
    (q : ℝ) ^ J.card * (completionEvent (completions k (cntH k) u P η) J).card <
      2 * (cntH k : ℝ) ^ J.card * (completions k (cntH k) u P η).card := by
  classical
  let t := (fixedOnes P η).card
  let m := cntH k - t
  let r := J.card
  let η' : Coeff ℤ q := fun a => if a ∈ J then 1 else η a
  have ht : t ≤ P.card := Finset.card_filter_le P _
  have hext : (fixedOnes (P ∪ J) η').card = t + r := by
    have hdis : Disjoint (fixedOnes P η) J := hPJ.mono_left (Finset.filter_subset _ _)
    rw [fixedOnes_extend P J η hPJ, Finset.card_union_of_disjoint hdis]
  have hP' : (P ∪ J).card ≤ Nat.sqrt k := by
    rw [Finset.card_union_of_disjoint hPJ]; exact hsize
  have hη' : ∀ a ∈ P ∪ J, η' a = 0 ∨ η' a = 1 := by
    intro a ha
    by_cases haJ : a ∈ J
    · simp [η', haJ]
    · simpa [η', haJ] using hη a ((Finset.mem_union.mp ha).resolve_right haJ)
  have hl := (uniform_completions hWan hq hk hpow u P η (by omega) hη hu).1
  have hu' := (uniform_completions hWan hq hk hpow u (P ∪ J) η' hP' hη' hu).2
  rw [hext] at hu'
  have he : cntH k - (t + r) = m - r := by dsimp [m]; omega
  rw [he] at hu'
  have hevent := completionEvent_eq k (cntH k) u P J η hPJ
  change completionEvent _ J = completions _ _ u (P ∪ J) η' at hevent
  rw [← hevent] at hu'
  obtain ⟨_, hkm, _, _, _⟩ := cnt_parameter_range hk hpow (show t + r ≤ Nat.sqrt k by omega)
  have hrm : r ≤ m := by dsimp [m]; omega
  have hmain : wanMain q k m = wanMain q k (m - r) * (q : ℝ) ^ r := by
    unfold wanMain
    rw [← pow_add]
    congr 1
    omega
  have hf : 0 < ((m - r).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m - r)
  have hfac := factorial_ratio_le_power hrm (Nat.sub_le (cntH k) t)
  change (m.factorial : ℝ) ≤ (cntH k : ℝ) ^ r * ((m - r).factorial : ℝ) at hfac
  have hbound : 3 * ((q : ℝ) ^ r * (completionEvent (completions k (cntH k) u P η) J).card) ≤
      5 * (cntH k : ℝ) ^ r * (completions k (cntH k) u P η).card := by
    apply (mul_le_mul_iff_right₀ hf).mp
    calc
      ((m - r).factorial : ℝ) * (3 * ((q : ℝ) ^ r * (completionEvent _ J).card)) =
          3 * ((m - r).factorial * (completionEvent _ J).card : ℝ) * (q : ℝ) ^ r := by ring
      _ ≤ 3 * ((5 / 4 : ℝ) * wanMain q k (m - r)) * (q : ℝ) ^ r := by gcongr
      _ = (15 / 4 : ℝ) * wanMain q k m := by rw [hmain]; ring
      _ ≤ 5 * (m.factorial : ℝ) * (completions k (cntH k) u P η).card := by
        change (3 / 4 : ℝ) * wanMain q k m ≤ _ at hl
        linarith
      _ ≤ ((m - r).factorial : ℝ) * (5 * (cntH k : ℝ) ^ r *
          (completions k (cntH k) u P η).card) := by
        nlinarith [mul_le_mul_of_nonneg_right hfac
          (show (0 : ℝ) ≤ ((completions k (cntH k) u P η).card : ℝ) by positivity)]
  have hF := Finset.card_pos.mpr
    (uniform_completions_nonempty hWan hq hk hpow u P η (by omega) hη hu)
  have hh := (cntH_bounds k).1
  have hpositive : 0 < (cntH k : ℝ) ^ r * (completions k (cntH k) u P η).card := by
    have : 0 < (cntH k : ℝ) := by exact_mod_cast (by have : 100000000 ≤ k := hk; omega : 0 < cntH k)
    have : 0 < ((completions k (cntH k) u P η).card : ℝ) := by exact_mod_cast hF
    positivity
  change (q : ℝ) ^ r * _ < 2 * (cntH k : ℝ) ^ r * _
  nlinarith

/-- The paper's ratio |F_J|/|F| < 2(h/q)^|J| (in particular for |J|=1,2). -/
theorem fixed_coordinate_ratio_div (hWan : WanPowerSumEstimates)
    {q k : ℕ} [NeZero q] (hq : q.Prime) (hk : cntK0 ≤ k)
    (hpow : (2 * k) ^ cntC0 ≤ q)
    (u : Fin k → ZMod q) (P J : Finset (ZMod q)) (η : Coeff ℤ q)
    (hsize : P.card + J.card ≤ Nat.sqrt k) (hPJ : Disjoint P J)
    (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1)
    (hu : u ⟨0, by have : 100000000 ≤ k := hk; omega⟩ = (cntH k : ZMod q)) :
    ((completionEvent (completions k (cntH k) u P η) J).card : ℝ) /
      (completions k (cntH k) u P η).card < 2 * ((cntH k : ℝ) / q) ^ J.card := by
  have hr := fixed_coordinate_ratio hWan hq hk hpow u P J η hsize hPJ hη hu
  have hF : 0 < ((completions k (cntH k) u P η).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr
      (uniform_completions_nonempty hWan hq hk hpow u P η (by omega) hη hu)
  have hqp : 0 < (q : ℝ) ^ J.card := pow_pos (by exact_mod_cast hq.pos) _
  rw [div_pow, ← mul_div_assoc, div_lt_iff₀ hF, div_mul_eq_mul_div, lt_div_iff₀ hqp]
  nlinarith only [hr]

end
end Rank2ModuleSVP
