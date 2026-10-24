import Rank2ModuleSVP.Checker
import Rank2ModuleSVP.AsymptoticsAux
import Rank2ModuleSVP.Completions
import Rank2ModuleSVP.Wan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-! Uniform Wan errors, completion counts, coordinate ratios, and enhanced-clean representatives.
The companion module exports the rounded gap parameters for the reduction. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

namespace Rank2ModuleSVP
open Filter
open scoped BigOperators
noncomputable section

/-- An integer-power domination lemma avoids logarithmic estimates with moving exponents. -/
theorem wan_power_domination {q k m : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hpow : (2*k)^1000 ≤ q) (hm : k+4 ≤ m)
    (hexp : 2*m ≤ 1000*(m-k-4)) :
    (2*(k : ℝ))^m * (q : ℝ)^(((m-k+2 : ℕ) : ℝ)/2) ≤
      (q : ℝ)^(m-k-1) := by
  have hb : (1 : ℝ) ≤ 2*k := by exact_mod_cast (by omega : 1 ≤ 2*k)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpR : (2*(k : ℝ))^1000 ≤ (q : ℝ) := by exact_mod_cast hpow
  have hp : (2*(k : ℝ))^(2*m) ≤ (q : ℝ)^(m-k-4) := by
    calc
      _ ≤ (2*(k : ℝ))^(1000*(m-k-4)) := pow_le_pow_right₀ hb hexp
      _ = ((2*(k : ℝ))^1000)^(m-k-4) := by rw [pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hpR _
  have hhalf : ((q : ℝ)^(((m-k+2 : ℕ) : ℝ)/2))^2 =
      (q : ℝ)^(m-k+2) := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num only [Nat.cast_ofNat]
    rw [show (((m-k+2 : ℕ) : ℝ)/2)*(2 : ℝ) = ((m-k+2 : ℕ) : ℝ) by ring,
      Real.rpow_natCast]
  have hsq : ((2*(k : ℝ))^m * (q : ℝ)^(((m-k+2 : ℕ) : ℝ)/2))^2 ≤
      ((q : ℝ)^(m-k-1))^2 := by
    rw [mul_pow, ← pow_mul, show m*2 = 2*m by omega, hhalf]
    calc
      _ ≤ (q : ℝ)^(m-k-4) * (q : ℝ)^(m-k+2) := by gcongr
      _ = (q : ℝ)^((m-k-4)+(m-k+2)) := (pow_add _ _ _).symm
      _ = ((q : ℝ)^(m-k-1))^2 := by
        rw [← pow_mul]; congr 1; omega
  have hn : 0 ≤ (2*(k : ℝ))^m * (q : ℝ)^(((m-k+2 : ℕ) : ℝ)/2) := by positivity
  have hn' : 0 ≤ (q : ℝ)^(m-k-1) := by positivity
  nlinarith

/-- All three absolute Wan errors share this uniform envelope. -/
theorem wan_errors_envelope {q k m : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hpow : (2*k)^1000 ≤ q) (hm : k+4 ≤ m)
    (hexp : 2*m ≤ 1000*(m-k-4)) :
    wanError q k m ≤ (q : ℝ)^(m-k-1) ∧
    wanCollisionError q k m ≤ (q : ℝ)^(m-k-1) ∧
    wanCoordinateError q k m ≤ (q : ℝ)^(m-k-1) := by
  have hdom := wan_power_domination hq hk hpow hm hexp
  have hb : (1 : ℝ) ≤ 2*k := by exact_mod_cast (by omega : 1 ≤ 2*k)
  have hp : (2*(k : ℝ))^(m-1) ≤ (2*(k : ℝ))^m :=
    pow_le_pow_right₀ hb (by omega)
  have hhalf : (q : ℝ)^(((m-k+1 : ℕ) : ℝ)/2) ≤
      (q : ℝ)^(((m-k+2 : ℕ) : ℝ)/2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq)
    exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : m-k+1 ≤ m-k+2)) (by norm_num)
  unfold wanError wanCollisionError wanCoordinateError
  have hn : 0 ≤ (2*(k : ℝ))^m := by positivity
  have hqn : 0 ≤ (q : ℝ)^(((m-k+2 : ℕ) : ℝ)/2) := by positivity
  constructor
  · nlinarith
  constructor
  · calc
      _ ≤ (1/2 : ℝ) * (2*(k : ℝ))^m * (q : ℝ)^(((m-k+2 : ℕ) : ℝ)/2) := by gcongr
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ (1/2 : ℝ) * (2*(k : ℝ))^m * (q : ℝ)^(((m-k+2 : ℕ) : ℝ)/2) := by gcongr
      _ ≤ _ := by nlinarith

/-- The envelopes hold simultaneously for every admissible prescribed weight. -/
theorem wan_errors_envelope_eventually : ∀ᶠ q in atTop,
    ∀ t ≤ rsT q, let m := rsH q-t
    wanError q (rsK q) m ≤ (q : ℝ)^(m-rsK q-1) ∧
    wanCollisionError q (rsK q) m ≤ (q : ℝ)^(m-rsK q-1) ∧
    wanCoordinateError q (rsK q) m ≤ (q : ℝ)^(m-rsK q-1) := by
  filter_upwards [rsT_small 2000, rsK_tendsto.eventually_ge_atTop 10000,
    eventually_ge_atTop 1] with q hT hk hq
  intro t ht
  have hr := rsH_rounding q
  have hh := rsH_le q
  apply wan_errors_envelope hq (by omega) (rsK_pow_le q) <;> omega

/-- Uniform convergence of all three relative errors, in epsilon form.
The collision and coordinate main terms are q^(m-k); the first main term is larger. -/
theorem wan_relative_errors_eventually (ε : ℝ) (hε : 0 < ε) : ∀ᶠ q in atTop,
    ∀ t ≤ rsT q, let m := rsH q-t
    wanError q (rsK q) m ≤ ε * wanMain q (rsK q) m ∧
    wanCollisionError q (rsK q) m ≤ ε * (q : ℝ)^(m-rsK q) ∧
    wanCoordinateError q (rsK q) m ≤ ε * (q : ℝ)^(m-rsK q) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1/ε)
  filter_upwards [wan_errors_envelope_eventually, completion_parameter_range,
    eventually_ge_atTop (max N 1)] with q he hr hq
  intro t ht
  obtain ⟨hA, hC, hE⟩ := he t ht
  obtain ⟨hk, hkm, _⟩ := hr t ht
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (le_max_right N 1 |>.trans hq)
  have hNq : (N : ℝ) ≤ q := by exact_mod_cast (le_max_left N 1 |>.trans hq)
  have hεq : 1 ≤ ε * (q : ℝ) := by
    have := (div_lt_iff₀ hε).mp (hN.trans_le hNq)
    nlinarith
  have hp : (q : ℝ)^(rsH q-t-rsK q-1) ≤ ε * (q : ℝ)^(rsH q-t-rsK q) := by
    have heq : rsH q-t-rsK q = (rsH q-t-rsK q-1)+1 := by omega
    conv_rhs => rw [heq, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hεq (show 0 ≤ (q : ℝ)^(rsH q-t-rsK q-1) by positivity)]
  refine ⟨hA.trans (hp.trans ?_), hC.trans hp, hE.trans hp⟩
  unfold wanMain
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hqR (by omega)) hε.le

/-- Every fixed polynomial of degree below 1000 is negligible compared with q. -/
theorem rsK_polynomial_small (C d : ℕ) (hd : d < 1000) :
    ∀ᶠ q in atTop, C * rsK q^d < q := by
  filter_upwards [rsK_tendsto.eventually_ge_atTop (C+2)] with q hk
  have hk1 : 1 ≤ rsK q := by omega
  have hp : C * rsK q^d < rsK q^(d+1) := by
    rw [pow_succ]
    simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right
      (by omega : C < rsK q) (pow_pos (by omega : 0 < rsK q) d)
  exact hp.trans_le ((Nat.pow_le_pow_right hk1 (by omega)).trans
    ((Nat.pow_le_pow_left (by omega : rsK q ≤ 2*rsK q) _).trans (rsK_pow_le q)))

/-- Uniform constant-factor form of the completion theorem; constants are 1/2 and 2. -/
theorem uniform_completions_eventually (hWan : WanPowerSumEstimates) :
    ∀ᶠ q in atTop, ∀ (hq : q.Prime),
    letI : NeZero q := ⟨hq.ne_zero⟩
    ∀ (u : Fin (rsK q) → ZMod q) (P : Finset (ZMod q)) (η : Coeff ℤ q),
      P.card ≤ rsT q → (∀ a ∈ P, η a = 0 ∨ η a = 1) →
      (∀ hk : 0 < rsK q, u ⟨0,hk⟩ = (rsH q : ZMod q)) →
      let m := rsH q - (fixedOnes P η).card
      wanMain q (rsK q) m / 2 ≤
        (m.factorial : ℝ) * (completions (rsK q) (rsH q) u P η).card ∧
      (m.factorial : ℝ) * (completions (rsK q) (rsH q) u P η).card ≤
        2 * wanMain q (rsK q) m := by
  filter_upwards [wan_relative_errors_eventually (1/8) (by norm_num),
    completion_parameter_range, rsT_small 1,
    rsK_polynomial_small 100 2 (by norm_num)] with q he hr hT hp
  intro hq
  letI : NeZero q := ⟨hq.ne_zero⟩
  intro u P η hP hη hu
  let t := (fixedOnes P η).card
  let m := rsH q-t
  have ht : t ≤ rsT q := (Finset.card_filter_le P _).trans hP
  obtain ⟨hk, hkm, hmq⟩ := hr t ht
  have htm : m+t = rsH q := by dsimp [m]; omega
  obtain ⟨hl, hu'⟩ := completions_count_bounds hWan hq (rsK q) (rsH q) m hk hkm hmq
    u (hu (by omega)) P η hη htm
  obtain ⟨hA, hC, hE⟩ := he t ht
  have hn : 0 ≤ (q : ℝ)^(m-rsK q) := by positivity
  have hC' : wanCollisionError q (rsK q) m ≤ (q : ℝ)^(m-rsK q) := by
    change _ ≤ (q : ℝ)^(rsH q-t-rsK q)
    nlinarith
  have hE' : wanCoordinateError q (rsK q) m ≤ (q : ℝ)^(m-rsK q) := by
    change _ ≤ (q : ℝ)^(rsH q-t-rsK q)
    nlinarith
  have hpoly : 8*(m^2+m*P.card) ≤ q := by
    have hh := rsH_le q
    have hm : m ≤ 2*rsK q := (Nat.sub_le _ _).trans hh
    have hPk : P.card ≤ rsK q := hP.trans (by simpa using hT)
    nlinarith
  have hpolyR : 8*((m : ℝ)^2+(m : ℝ)*P.card) ≤ q := by exact_mod_cast hpoly
  have hmain : wanMain q (rsK q) m = (q : ℝ)^(m-rsK q)*(q : ℝ) := by
    unfold wanMain
    rw [pow_succ]
  have hbudget : (m : ℝ)^2 * ((q : ℝ)^(m-rsK q) + wanCollisionError q (rsK q) m) +
      (m : ℝ)*P.card * ((q : ℝ)^(m-rsK q) + wanCoordinateError q (rsK q) m) ≤
      wanMain q (rsK q) m / 4 := by
    calc
      _ ≤ 2*((m : ℝ)^2+(m : ℝ)*P.card)*(q : ℝ)^(m-rsK q) := by
        nlinarith [mul_le_mul_of_nonneg_left hC' (sq_nonneg (m : ℝ)),
          mul_le_mul_of_nonneg_left hE' (show 0 ≤ (m : ℝ)*P.card by positivity)]
      _ ≤ _ := by
        rw [hmain]
        nlinarith [mul_le_mul_of_nonneg_right hpolyR hn]
  change wanMain q (rsK q) m / 2 ≤ _ ∧ _ ≤ 2*wanMain q (rsK q) m
  have hMn : 0 ≤ wanMain q (rsK q) m := by unfold wanMain; positivity
  constructor <;> nlinarith

/-- The factorial comparison in the fixed-coordinate estimate, for arbitrary r. -/
theorem factorial_ratio_le_power {m h r : ℕ} (hr : r ≤ m) (hm : m ≤ h) :
    (m.factorial : ℝ) ≤ (h : ℝ)^r * ((m-r).factorial : ℝ) := by
  have hh := Nat.descFactorial_le_pow m r
  have he := Nat.factorial_mul_descFactorial hr
  have hpow := Nat.pow_le_pow_left hm r
  have hn : m.factorial ≤ h^r*(m-r).factorial := by
    rw [← he]
    exact (Nat.mul_le_mul_left _ (hh.trans hpow)).trans_eq (Nat.mul_comm _ _)
  exact_mod_cast hn

/-- Nonemptiness, uniform over the syndrome and prescribed bits. -/
theorem uniform_completions_nonempty_eventually (hWan : WanPowerSumEstimates) :
    ∀ᶠ q in atTop, ∀ (hq : q.Prime),
    letI : NeZero q := ⟨hq.ne_zero⟩
    ∀ (u : Fin (rsK q) → ZMod q) (P : Finset (ZMod q)) (η : Coeff ℤ q),
      P.card ≤ rsT q → (∀ a ∈ P, η a = 0 ∨ η a = 1) →
      (∀ hk : 0 < rsK q, u ⟨0,hk⟩ = (rsH q : ZMod q)) →
      (completions (rsK q) (rsH q) u P η).Nonempty := by
  filter_upwards [uniform_completions_eventually hWan] with q hq
  intro hp
  letI : NeZero q := ⟨hp.ne_zero⟩
  intro u P η hP hη hu
  have hl := (hq hp u P η hP hη hu).1
  have hpos : 0 < wanMain q (rsK q) (rsH q-(fixedOnes P η).card) := by
    unfold wanMain
    exact pow_pos (by exact_mod_cast hp.pos) _
  apply Finset.card_pos.mp
  by_contra hh
  have hz : (completions (rsK q) (rsH q) u P η).card = 0 := by omega
  rw [hz, Nat.cast_zero, mul_zero] at hl
  linarith

/-- Exact additional-one bookkeeping. -/
theorem fixedOnes_extend {q : ℕ} [NeZero q] (P Q : Finset (ZMod q))
    (η : Coeff ℤ q) (_hPQ : Disjoint P Q) :
    fixedOnes (P ∪ Q) (fun a => if a ∈ Q then 1 else η a) = fixedOnes P η ∪ Q := by
  classical
  ext a
  by_cases ha : a ∈ Q
  · simp [fixedOnes, ha]
  · simp [fixedOnes, ha]

/-- Cross-multiplied fixed-coordinate ratio, with the absolute uniform constant 4.
This applies to any number r of additional coordinates, hence in particular r=1,2. -/
theorem fixed_coordinate_ratio_eventually (hWan : WanPowerSumEstimates) :
    ∀ᶠ q in atTop, ∀ (hq : q.Prime),
    letI : NeZero q := ⟨hq.ne_zero⟩
    ∀ (u : Fin (rsK q) → ZMod q) (P Q : Finset (ZMod q)) (η : Coeff ℤ q),
      P.card + Q.card ≤ rsT q → Disjoint P Q →
      (∀ a ∈ P, η a = 0 ∨ η a = 1) →
      (∀ hk : 0 < rsK q, u ⟨0,hk⟩ = (rsH q : ZMod q)) →
      (q : ℝ)^Q.card * (completionEvent (completions (rsK q) (rsH q) u P η) Q).card ≤
        4*(rsH q : ℝ)^Q.card * (completions (rsK q) (rsH q) u P η).card := by
  filter_upwards [uniform_completions_eventually hWan, completion_parameter_range] with q hc hr
  intro hq
  letI : NeZero q := ⟨hq.ne_zero⟩
  intro u P Q η hsize hPQ hη hu
  let t := (fixedOnes P η).card
  let m := rsH q-t
  let r := Q.card
  let η' : Coeff ℤ q := fun a => if a ∈ Q then 1 else η a
  have ht : t ≤ P.card := Finset.card_filter_le P _
  have hext : (fixedOnes (P ∪ Q) η').card = t+r := by
    have hdis : Disjoint (fixedOnes P η) Q := hPQ.mono_left (Finset.filter_subset _ _)
    rw [fixedOnes_extend P Q η hPQ, Finset.card_union_of_disjoint hdis]
  have hP' : (P ∪ Q).card ≤ rsT q := by rw [Finset.card_union_of_disjoint hPQ]; exact hsize
  have hη' : ∀ a ∈ P ∪ Q, η' a = 0 ∨ η' a = 1 := by
    intro a ha
    by_cases haQ : a ∈ Q
    · simp [η', haQ]
    · simpa [η', haQ] using hη a ((Finset.mem_union.mp ha).resolve_right haQ)
  have hl := (hc hq u P η (by omega) hη hu).1
  have hu' := (hc hq u (P ∪ Q) η' hP' hη' hu).2
  rw [hext] at hu'
  have he : rsH q-(t+r) = m-r := by dsimp [m]; omega
  rw [he] at hu'
  have hevent := completionEvent_eq (rsK q) (rsH q) u P Q η hPQ
  change completionEvent _ Q = completions _ _ u (P ∪ Q) η' at hevent
  rw [← hevent] at hu'
  obtain ⟨hk, hkm, _⟩ := hr (t+r) (by omega)
  have hrm : r ≤ m := by dsimp [m]; omega
  have hmain : wanMain q (rsK q) m = wanMain q (rsK q) (m-r)*(q : ℝ)^r := by
    unfold wanMain
    rw [← pow_add]
    congr 1
    omega
  have hf : 0 < ((m-r).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m-r)
  have hfac := factorial_ratio_le_power hrm (Nat.sub_le (rsH q) t)
  change (m.factorial : ℝ) ≤ (rsH q : ℝ)^r * ((m-r).factorial : ℝ) at hfac
  apply (mul_le_mul_iff_right₀ hf).mp
  calc
    ((m-r).factorial : ℝ) * ((q : ℝ)^r * (completionEvent _ Q).card) =
        ((m-r).factorial * (completionEvent _ Q).card : ℝ)*(q : ℝ)^r := by ring
    _ ≤ (2*wanMain q (rsK q) (m-r))*(q : ℝ)^r := by gcongr
    _ = 2*wanMain q (rsK q) m := by rw [hmain]; ring
    _ ≤ 4*(m.factorial : ℝ)*(completions (rsK q) (rsH q) u P η).card := by
      change wanMain q (rsK q) m / 2 ≤ _ at hl
      linarith
    _ ≤ ((m-r).factorial : ℝ) * (4*(rsH q : ℝ)^r *
        (completions (rsK q) (rsH q) u P η).card) := by
      nlinarith [mul_le_mul_of_nonneg_right hfac
        (show (0 : ℝ) ≤ ((completions (rsK q) (rsH q) u P η).card : ℝ) by positivity)]

/-- At most twice |P| ordered pairs at an offset touch P. -/
theorem touching_pairs_card {q : ℕ} [NeZero q] (P : Finset (ZMod q)) (d : ZMod q) :
    (Finset.univ.filter fun a => a ∈ P ∨ a+d ∈ P).card ≤ 2*P.card := by
  classical
  have he : (Finset.univ.filter fun a => a ∈ P ∨ a+d ∈ P) =
      P ∪ P.image (fun b => b-d) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image]
    constructor
    · rintro (ha | ha)
      · exact Or.inl ha
      · exact Or.inr ⟨a+d, ha, by abel⟩
    · rintro (ha | ⟨b, hb, rfl⟩)
      · exact Or.inl ha
      · exact Or.inr (by simpa using hb)
  rw [he]
  have hh := Finset.card_image_le (s := P) (f := fun b => b-d)
  have hu := Finset.card_union_le P (P.image fun b => b-d)
  omega

/-- A finite quantitative union bound, using exactly the one- and two-free-endpoint counts. -/
theorem clean_event_budget {q h : ℕ} [NeZero q]
    (F : Finset (Coeff ℤ q)) (P D : Finset (ZMod q))
    (hq : 0 < q) (hF : F.Nonempty) (hD : (0 : ZMod q) ∉ D)
    (hratio : ∀ Q : Finset (ZMod q), Disjoint P Q → Q.card ≤ 2 →
      (q : ℝ)^Q.card*(completionEvent F Q).card ≤ 4*(h : ℝ)^Q.card*F.card)
    (hsmall : 4*D.card*(2*P.card*h+h^2) < q) :
    (∑ p ∈ forbiddenPairIndices P D,
      (F.filter fun x => x p.2 = 1 ∧ x (p.2+p.1) = 1).card) < F.card := by
  classical
  let e : ZMod q → ZMod q → ℝ := fun d a =>
    if a ∉ P ∨ a+d ∉ P then (F.filter fun x => x a = 1 ∧ x (a+d) = 1).card else 0
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hFR : 0 < (F.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hF
  have hpairs (d : ZMod q) (hd : d ∈ D) (a : ZMod q) :
      (q : ℝ)^2*e d a ≤
        if a ∈ P ∨ a+d ∈ P then 4*(h : ℝ)*q*F.card else 4*(h : ℝ)^2*F.card := by
    have hd0 : d ≠ 0 := fun he => hD (he ▸ hd)
    have hab : a ≠ a+d := by intro he; exact hd0 (add_left_cancel (he.symm.trans (add_zero a).symm))
    by_cases ha : a ∉ P ∨ a+d ∉ P
    · let Q : Finset (ZMod q) := {a,a+d} \ P
      have hPQ : Disjoint P Q := Finset.disjoint_left.mpr
        (fun a ha hb => (Finset.mem_sdiff.mp hb).2 ha)
      have hQ2 : Q.card ≤ 2 := (Finset.card_le_card Finset.sdiff_subset).trans_eq
        (Finset.card_pair hab)
      have hr := hratio Q hPQ hQ2
      have hsub : ((F.filter fun x => x a = 1 ∧ x (a+d) = 1).card : ℝ) ≤
          (completionEvent F Q).card := by exact_mod_cast card_pairEvent_le F P a (a+d)
      dsimp [e]
      rw [if_pos ha]
      by_cases ht : a ∈ P ∨ a+d ∈ P
      · have hQ1 : Q.card = 1 := by
          rcases ht with haP | hbP
          · have hb : a+d ∉ P := ha.resolve_left (not_not.mpr haP)
            have heQ : Q = {a+d} := by
              ext b
              simp only [Q, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
              aesop
            rw [heQ, Finset.card_singleton]
          · have ha' : a ∉ P := ha.resolve_right (not_not.mpr hbP)
            have heQ : Q = {a} := by
              ext b
              simp only [Q, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
              aesop
            rw [heQ, Finset.card_singleton]
        rw [hQ1, pow_one, pow_one] at hr
        rw [if_pos ht]
        have hs := mul_le_mul_of_nonneg_left hsub hqR.le
        have hs' := mul_le_mul_of_nonneg_left (hs.trans hr) hqR.le
        nlinarith only [hs']
      · have haP : a ∉ P := fun h => ht (Or.inl h)
        have hbP : a+d ∉ P := fun h => ht (Or.inr h)
        have hQ : Q = {a,a+d} := by ext b; simp [Q]; aesop
        have hcard : Q.card = 2 := by rw [hQ, Finset.card_pair hab]
        rw [hcard] at hr
        rw [if_neg ht]
        exact (mul_le_mul_of_nonneg_left hsub (sq_nonneg (q : ℝ))).trans hr
    · dsimp [e]
      rw [if_neg ha, mul_zero]
      split_ifs <;> positivity
  have hsum (d : ZMod q) (hd : d ∈ D) :
      (q : ℝ)^2*(∑ a, e d a) ≤
        4*(2*(P.card : ℝ)*h*q+(q : ℝ)*h^2)*F.card := by
    have hh := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (ZMod q))) => hpairs d hd a)
    rw [← Finset.mul_sum] at hh
    have hcard := touching_pairs_card P d
    have hcardR : ((Finset.univ.filter fun a => a ∈ P ∨ a+d ∈ P).card : ℝ) ≤ 2*P.card := by
      exact_mod_cast hcard
    have hcomp : ((Finset.univ.filter fun a : ZMod q => ¬(a ∈ P ∨ a+d ∈ P)).card : ℝ) ≤ q := by
      exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset (ZMod q)) _ |>.trans_eq (by simp))
    conv_rhs at hh =>
      rw [Finset.sum_ite]
      simp only [Finset.sum_const, nsmul_eq_mul]
    have hc1 := mul_le_mul_of_nonneg_right hcardR
      (show 0 ≤ 4*(h : ℝ)*q*F.card by positivity)
    have hc2 := mul_le_mul_of_nonneg_right hcomp
      (show 0 ≤ 4*(h : ℝ)^2*F.card by positivity)
    nlinarith only [hh, hc1, hc2]
  have htotal := Finset.sum_le_sum hsum
  rw [← Finset.mul_sum] at htotal
  simp only [Finset.sum_const, nsmul_eq_mul] at htotal
  have heq : ((∑ p ∈ forbiddenPairIndices P D,
      (F.filter fun x => x p.2 = 1 ∧ x (p.2+p.1) = 1).card : ℕ) : ℝ) =
      ∑ d ∈ D, ∑ a, e d a := by
    simp only [forbiddenPairIndices, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_zero, e]
    exact Finset.sum_product D Finset.univ _
  have hsmallR : 4*(D.card : ℝ)*(2*(P.card : ℝ)*h+(h : ℝ)^2) < q := by exact_mod_cast hsmall
  have hstrict := mul_lt_mul_of_pos_right hsmallR (mul_pos hqR hFR)
  have hbudget : ((∑ p ∈ forbiddenPairIndices P D,
      (F.filter fun x => x p.2 = 1 ∧ x (p.2+p.1) = 1).card : ℕ) : ℝ) < F.card := by
    rw [← heq] at htotal
    have hlt : (q : ℝ)^2 * ((∑ p ∈ forbiddenPairIndices P D,
        (F.filter fun x => x p.2 = 1 ∧ x (p.2+p.1) = 1).card : ℕ) : ℝ) <
        (q : ℝ)^2*F.card := by nlinarith only [htotal, hstrict]
    exact (mul_lt_mul_iff_right₀ (sq_pos_of_pos hqR)).mp hlt
  exact_mod_cast hbudget

/-- The exact event budget from round 2 is eventually discharged. -/
theorem clean_event_budget_eventually (hWan : WanPowerSumEstimates) (C : ℕ) :
    ∀ᶠ q in atTop, ∀ (hq : q.Prime),
    letI : NeZero q := ⟨hq.ne_zero⟩
    ∀ (u : Fin (rsK q) → ZMod q) (P D : Finset (ZMod q)) (η : Coeff ℤ q),
      P.card+2 ≤ rsT q → D.card ≤ C*rsT q^2 → (0 : ZMod q) ∉ D →
      (∀ a ∈ P, η a = 0 ∨ η a = 1) →
      (∀ hk : 0 < rsK q, u ⟨0,hk⟩ = (rsH q : ZMod q)) →
      (∑ p ∈ forbiddenPairIndices P D,
        ((completions (rsK q) (rsH q) u P η).filter
          fun x => x p.2 = 1 ∧ x (p.2+p.1) = 1).card) <
        (completions (rsK q) (rsH q) u P η).card := by
  filter_upwards [fixed_coordinate_ratio_eventually hWan,
    uniform_completions_nonempty_eventually hWan, clean_budget_eventually (4*C)] with q hr hn hs
  intro hq
  letI : NeZero q := ⟨hq.ne_zero⟩
  intro u P D η hP hD hD0 hη hu
  apply clean_event_budget _ P D hq.pos (hn hq u P η (by omega) hη hu) hD0
  · intro Q hPQ hQ
    exact hr hq u P Q η (by omega) hPQ hη hu
  · calc
      4*D.card*(2*P.card*rsH q+rsH q^2) ≤
          4*(C*rsT q^2)*(2*rsT q*rsH q+rsH q^2) := by gcongr; omega
      _ < q := by nlinarith only [hs]

/-- Paper enhanced-clean theorem, uniform for a fixed quadratic offset bound C. -/
theorem enhanced_clean_eventually (hWan : WanPowerSumEstimates) (C : ℕ) :
    ∀ᶠ q in atTop, ∀ (hq : q.Prime),
    letI : NeZero q := ⟨hq.ne_zero⟩
    ∀ {n : ℕ} (α : Fin n → ZMod q), Function.Injective α →
      (∀ j l j' l', j ≠ l → j' ≠ l' → α l-α j = α l'-α j' → j=j' ∧ l=l') →
    ∀ (Dbad : Finset (ZMod q)), (0 : ZMod q) ∉ Dbad →
      Disjoint Dbad (completionWitnessOffsets α) → n+2 ≤ rsT q →
      (completionWitnessOffsets α ∪ Dbad).card ≤ C*rsT q^2 →
    ∀ (u : Fin (rsK q) → ZMod q) (η : Coeff ℤ q),
      (∀ a ∈ Finset.univ.image α, η a = 0 ∨ η a = 1) →
      (∀ hk : 0 < rsK q, u ⟨0,hk⟩ = (rsH q : ZMod q)) →
      ∃ x ∈ completions (rsK q) (rsH q) u (Finset.univ.image α) η,
        (∀ j l, j ≠ l → cyclicCorrelation x (α l-α j) = η (α j)*η (α l)) ∧
        ∀ d ∈ Dbad, cyclicCorrelation x d = 0 := by
  filter_upwards [clean_event_budget_eventually hWan C] with q hb
  intro hq
  letI : NeZero q := ⟨hq.ne_zero⟩
  intro n α hα hSidon Dbad hD0 hdis hn hcard u η hη hu
  apply enhanced_clean_of_budget α hα hSidon Dbad hD0 hdis (rsK q) (rsH q) u η
  apply hb hq u (Finset.univ.image α) (completionWitnessOffsets α ∪ Dbad) η
  · have hh := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := α)
    simp only [Finset.card_univ, Fintype.card_fin] at hh
    omega
  · exact hcard
  · simp only [Finset.mem_union, not_or]
    refine ⟨?_, hD0⟩
    intro h
    obtain ⟨⟨j,l⟩, hmem, he⟩ := Finset.mem_image.mp h
    have hjl : j ≠ l := (Finset.mem_filter.mp hmem).2
    exact hjl (hα (sub_eq_zero.mp he).symm)
  · exact hη
  · exact hu

/-- Reduction modulo q is injective on the open centered interval of length q. -/
theorem asymptotic_intCast_inj {q : ℕ} {a b : ℤ}
    (ha : -(q : ℤ) < 2*a) (ha' : 2*a < q)
    (hb : -(q : ℤ) < 2*b) (hb' : 2*b < q)
    (he : (a : ZMod q) = b) : a = b := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub a b q).mp he
  have hab : |b-a| < (q : ℤ) := by rw [abs_lt]; omega
  by_contra hh
  have hn : b-a ≠ 0 := by omega
  have hle : (q : ℤ) ≤ |b-a| :=
    Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs (q : ℤ) (b-a)).mpr hd)
  omega

/-- Sidon uniqueness survives reduction modulo q under the paper's size bound. -/
theorem checker_sidon_mod {q : ℕ} (I : IdealCVP.X3CInstance)
    (s : IdealCVP.SidonPositions I.n) (hq : 4*Checker.tau I s*(3*I.q) < q) :
    Function.Injective (fun j => (s.α j : ZMod q)) ∧
    (∀ j l j' l', j ≠ l → j' ≠ l' →
      (s.α l : ZMod q)-s.α j = (s.α l' : ZMod q)-s.α j' → j=j' ∧ l=l') := by
  have hM : 1 ≤ 3*I.q := by have := I.q_pos; omega
  have hsmall : 2*Checker.alphaStar I s < q := by
    have ht := Nat.mul_le_mul_left (4*Checker.tau I s) hM
    unfold Checker.tau at ht hq
    omega
  have hα (j : Fin I.n) : 2*(s.α j : ℤ) < q := by
    have hh := Checker.alpha_le_alphaStar I s j
    exact_mod_cast (by omega : 2*s.α j < q)
  have hα0 (j : Fin I.n) : (0 : ℤ) ≤ s.α j := by positivity
  constructor
  · intro j l he
    apply s.strictMono.injective
    have he' : ((s.α j : ℤ) : ZMod q) = (s.α l : ℤ) := by simpa using he
    have hh := asymptotic_intCast_inj (by have := hα j; omega) (hα j)
      (by have := hα l; omega) (hα l) he'
    exact_mod_cast hh
  · intro j l j' l' hjl hjl' he
    apply s.differences j l j' l' hjl hjl'
    have he' : (((s.α l : ℤ)-s.α j : ℤ) : ZMod q) = (((s.α l' : ℤ)-s.α j' : ℤ) : ZMod q) := by
      simpa using he
    apply asymptotic_intCast_inj _ _ _ _ he'
    all_goals
      have hj := hα j
      have hl := hα l
      have hj' := hα j'
      have hl' := hα l'
      have hj0 := hα0 j
      have hl0 := hα0 l
      have hj'0 := hα0 j'
      have hl'0 := hα0 l'
      omega

/-- The enhanced-clean theorem for the concrete separated-offset checker.
All size and event-count bounds are discharged; only Wan is passed as input. -/
theorem checker_enhanced_clean_eventually (hWan : WanPowerSumEstimates) :
    ∀ᶠ q in atTop, ∀ (hq : q.Prime),
    letI : NeZero q := ⟨hq.ne_zero⟩
    ∀ (I : IdealCVP.X3CInstance) (s : IdealCVP.SidonPositions I.n),
      I.n+2 ≤ rsT q → 4*Checker.tau I s*(3*I.q) < q →
    ∀ (u : Fin (rsK q) → ZMod q) (η : Coeff ℤ q),
      (∀ j, η (s.α j) = 0 ∨ η (s.α j) = 1) →
      (∀ hk : 0 < rsK q, u ⟨0,hk⟩ = (rsH q : ZMod q)) →
      ∃ x ∈ completions (rsK q) (rsH q) u
          (Finset.univ.image (fun j => (s.α j : ZMod q))) η,
        Checker.Clean I s (fun a => (x a : ℚ)) := by
  filter_upwards [enhanced_clean_eventually hWan 19] with q hc
  intro hq
  letI : NeZero q := ⟨hq.ne_zero⟩
  intro I s hn hqsize u η hη hu
  obtain ⟨hα, hSidon⟩ := checker_sidon_mod I s hqsize
  obtain ⟨hbad0, hdis⟩ := Checker.row_shift_bad_separation I s hqsize
  have hcard : (completionWitnessOffsets (fun j => (s.α j : ZMod q)) ∪
      Checker.D_bad I s).card ≤ 19*rsT q^2 := by
    have hw : (completionWitnessOffsets (fun j => (s.α j : ZMod q))).card ≤ I.n^2 := by
      apply Finset.card_image_le.trans
      have hh := Finset.card_filter_le (Finset.univ : Finset (Fin I.n × Fin I.n))
        (fun p => p.1 ≠ p.2)
      simpa [pow_two] using hh
    have hb := Checker.bad_card_bound (q := q) I s
    rw [Checker.incidence_count] at hb
    have hU := Finset.card_union_le
      (completionWitnessOffsets (fun j => (s.α j : ZMod q))) (Checker.D_bad I s)
    have hs : I.n^2 ≤ rsT q^2 := Nat.pow_le_pow_left (by omega) _
    nlinarith
  have hη' : ∀ a ∈ Finset.univ.image (fun j => (s.α j : ZMod q)), η a = 0 ∨ η a = 1 := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    exact hη j
  obtain ⟨x, hx, hw, hb⟩ := hc hq (fun j => (s.α j : ZMod q)) hα hSidon
    (Checker.D_bad I s) hbad0 hdis hn hcard u η hη' hu
  refine ⟨x, hx, ?_⟩
  have hfix := (mem_completions _ _ _ _ _ _).mp hx |>.2.2.2
  have hpres (j : Fin I.n) : x (s.α j) = η (s.α j) :=
    hfix _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hcorr (d : ZMod q) : Checker.correlation (fun a => (x a : ℚ)) d =
      (cyclicCorrelation x d : ℚ) := by
    unfold Checker.correlation cyclicCorrelation
    push_cast
    rfl
  constructor
  · intro j l hjl
    simp only [hcorr, hw j l hjl, Int.cast_mul, hpres]
  · intro d hd
    rw [hcorr, hb d hd, Int.cast_zero]

end
end Rank2ModuleSVP
