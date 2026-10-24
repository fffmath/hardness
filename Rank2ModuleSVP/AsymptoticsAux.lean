import Rank2ModuleSVP.Checker
import Rank2ModuleSVP.Completions
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring

/-! Rounded reduction parameters and numerical gaps, uniformly in the checker instance.
All estimates are proved in the coefficient model through the existing checker API. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Rank2ModuleSVP
open Filter
noncomputable section

/-- The exact squared target of equation Gamma-target-exact. -/
def rsGammaTarget (q : ℕ) : ℝ := 99*(rsK q : ℝ)*q/(100*((q : ℝ)-1))

/-- Nearest positive integer, with ties rounded upward, as in the paper. -/
def rsGamma (q : ℕ) : ℕ := max 1 ⌊Real.sqrt (rsGammaTarget q)+(1/2 : ℝ)⌋₊

def reductionL (q : ℕ) : ℝ := 2*(rsK q : ℝ)*q
def reductionH (q : ℕ) : ℝ := (rsH q : ℝ)*((q : ℝ)-rsH q)
def reductionF (q : ℕ) : ℝ := (rsGamma q : ℝ)^2*((q : ℝ)-1)

/-- Baseline with the three instance statistics made explicit. Here v is ||V||². -/
def reductionBaseline (q : ℕ) (W M v : ℝ) : ℝ :=
  reductionH q+v+2*W*rsH q-2*M+
    (2*(rsH q : ℝ)*W-4*(rsH q : ℝ)^2*W^2)/(q : ℝ)

def reductionNu (q : ℕ) (W : ℝ) : ℝ := W/((q : ℝ)*rsGamma q)
def reductionThreshold (q : ℕ) (W M v : ℝ) : ℝ :=
  reductionBaseline q W M v+reductionF q

/-- A uniform quantitative estimate for the paper's integer rounding. -/
theorem rsGamma_sq_bounds {q : ℕ} (hq : 100001 ≤ q) (hk : 1000000000000 ≤ rsK q) :
    (9899/10000 : ℝ)*rsK q ≤ (rsGamma q : ℝ)^2 ∧
    (rsGamma q : ℝ)^2 ≤ (9901/10000 : ℝ)*rsK q := by
  have hqR : (100001 : ℝ) ≤ q := by exact_mod_cast hq
  have hkR : (1000000000000 : ℝ) ≤ rsK q := by exact_mod_cast hk
  have hd : 0 < 100*((q : ℝ)-1) := by linarith
  have htlo : (99/100 : ℝ)*rsK q ≤ rsGammaTarget q := by
    unfold rsGammaTarget
    apply (le_div_iff₀ hd).mpr
    nlinarith only [hkR]
  have hthi : rsGammaTarget q ≤ (99001/100000 : ℝ)*rsK q := by
    unfold rsGammaTarget
    apply (div_le_iff₀ hd).mpr
    nlinarith only [mul_nonneg (show 0 ≤ (rsK q : ℝ) by positivity) (show 0 ≤ (q : ℝ)-100001 by linarith)]
  have ht0 : 0 ≤ rsGammaTarget q := by linarith
  have hs0 := Real.sqrt_nonneg (rsGammaTarget q)
  have hs2 := Real.sq_sqrt ht0
  have hs1 : 1 ≤ Real.sqrt (rsGammaTarget q) := by nlinarith only [htlo, hkR, hs2, hs0]
  have hsmall : Real.sqrt (rsGammaTarget q) ≤ (rsK q : ℝ)/100000 := by
    have hh : rsGammaTarget q ≤ ((rsK q : ℝ)/100000)^2 := by
      nlinarith only [hthi, hkR,
        mul_nonneg (show 0 ≤ (rsK q : ℝ) by positivity)
          (show 0 ≤ (rsK q : ℝ)-1000000000000 by linarith)]
    nlinarith only [hh, hs2, hs0, hkR]
  have hfloor : 1 ≤ ⌊Real.sqrt (rsGammaTarget q)+(1/2 : ℝ)⌋₊ :=
    Nat.le_floor (by linarith)
  have he : rsGamma q = ⌊Real.sqrt (rsGammaTarget q)+(1/2 : ℝ)⌋₊ := max_eq_right hfloor
  have hroundhi : (rsGamma q : ℝ) ≤ Real.sqrt (rsGammaTarget q)+1 := by
    rw [he]
    have := Nat.floor_le (show 0 ≤ Real.sqrt (rsGammaTarget q)+(1/2 : ℝ) by positivity)
    linarith
  have hroundlo : Real.sqrt (rsGammaTarget q)-1 ≤ (rsGamma q : ℝ) := by
    rw [he]
    have := Nat.lt_floor_add_one (Real.sqrt (rsGammaTarget q)+(1/2 : ℝ))
    linarith
  have hsqlo : (Real.sqrt (rsGammaTarget q)-1)^2 ≤ (rsGamma q : ℝ)^2 :=
    pow_le_pow_left₀ (by linarith) hroundlo 2
  have hsqhi : (rsGamma q : ℝ)^2 ≤ (Real.sqrt (rsGammaTarget q)+1)^2 :=
    pow_le_pow_left₀ (by positivity) hroundhi 2
  constructor <;> nlinarith only [hsqlo, hsqhi, hs2, htlo, hthi, hsmall, hkR]

/-- The rounding estimate is unconditional and eventually uniform in q. -/
theorem rsGamma_sq_bounds_eventually : ∀ᶠ q in atTop,
    (9899/10000 : ℝ)*rsK q ≤ (rsGamma q : ℝ)^2 ∧
    (rsGamma q : ℝ)^2 ≤ (9901/10000 : ℝ)*rsK q := by
  filter_upwards [eventually_ge_atTop 100001,
    rsK_tendsto.eventually_ge_atTop 1000000000000] with q hq hk
  exact rsGamma_sq_bounds hq hk

/-- Elementary real arithmetic underlying all four soundness cases.
The estimates deliberately leave substantial room for integer rounding. -/
theorem reduction_gap_arithmetic {q k h g W M v : ℝ}
    (hk : 1000000000000 ≤ k) (hq : 1000000*k^4 ≤ q)
    (hhlo : 201*k/200-1 ≤ h) (hhhi : h ≤ 201*k/200)
    (hg : 1 ≤ g) (hglo : 9899/10000*k ≤ g^2) (hghi : g^2 ≤ 9901/10000*k)
    (hW0 : 0 < W) (hW : W ≤ 3*k) (hM0 : 0 ≤ M) (hM : M ≤ W)
    (hv0 : 0 ≤ v) (hv : v ≤ W^2/q) :
    let H := h*(q-h)
    let L := 2*k*q
    let F := g^2*(q-1)
    let B := H+v+2*W*h-2*M+(2*h*W-4*h^2*W^2)/q
    let ν := W/(q*g)
    0 < B ∧ 0 < ν ∧ ν < 1 ∧
      B+F < L ∧ (1-ν)*(H+2*q+F) > B+F ∧
      (1-ν)*(L/100+g^2*(2*q-4)) > B+F ∧ 3*F > B+F := by
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hk2 : 1 ≤ k^2 := by nlinarith only [hk1]
  have hk4 : k^2 ≤ k^4 := by nlinarith only [mul_nonneg (sq_nonneg k) (sub_nonneg.mpr hk2)]
  have hq2 : 1000000*k^2 ≤ q := by linarith only [hq, hk4]
  have hqk : 1000000*k ≤ q := by nlinarith only [hq2, hk1]
  have hq0 : 0 < q := by nlinarith only [hq2, hk2]
  have hh0 : 0 ≤ h := by linarith
  have hh2 : h ≤ 2*k := by linarith
  have hWn : 0 ≤ W := hW0.le
  have hWh : W*h ≤ 6*k^2 := by nlinarith only [mul_le_mul hW hh2 hh0 (by positivity : 0 ≤ 3*k)]
  have hWsq : W^2 ≤ 9*k^2 := by nlinarith only [sq_le_sq₀ hWn (by positivity : 0 ≤ 3*k) |>.mpr hW]
  have hhsq : h^2 ≤ 4*k^2 := by nlinarith only [sq_le_sq₀ hh0 (by positivity : 0 ≤ 2*k) |>.mpr hh2]
  have hprod : h^2*W^2 ≤ 36*k^4 := by
    have hsq := (sq_le_sq₀ (mul_nonneg hWn hh0) (by positivity : 0 ≤ 6*k^2)).mpr hWh
    nlinarith only [hsq]
  have hv1 : v ≤ 1 := by
    have hdiv : W^2/q ≤ 1 := (div_le_iff₀ hq0).mpr (by nlinarith only [hWsq, hq2])
    exact hv.trans hdiv
  have htermlo : -1 ≤ (2*h*W-4*h^2*W^2)/q := by
    apply (le_div_iff₀ hq0).mpr
    nlinarith only [hq, hprod, mul_nonneg hh0 hWn]
  have htermhi : (2*h*W-4*h^2*W^2)/q ≤ 1 := by
    apply (div_le_iff₀ hq0).mpr
    nlinarith only [hWh, hq2, mul_nonneg (sq_nonneg h) (sq_nonneg W)]
  have hBerrlo : -q/100 ≤ v+2*W*h-2*M+(2*h*W-4*h^2*W^2)/q := by
    nlinarith only [hv0, htermlo, mul_nonneg hWn hh0, hM, hW, hqk, hk]
  have hBerrhi : v+2*W*h-2*M+(2*h*W-4*h^2*W^2)/q ≤ q/100 := by
    nlinarith only [hv1, hWh, hM0, htermhi, hq2, hk2]
  have hHhi : h*(q-h) ≤ 10050/10000*(k*q) := by
    nlinarith only [mul_le_mul_of_nonneg_right hhhi hq0.le, sq_nonneg h]
  have hHlo : 10048/10000*(k*q) ≤ h*(q-h) := by
    have hhq := mul_le_mul_of_nonneg_right hhlo hq0.le
    have hkkq := mul_le_mul_of_nonneg_right hqk hk0.le
    have hkq := mul_le_mul_of_nonneg_right hk hq0.le
    nlinarith only [hhq, hhsq, hkkq, hkq]
  have hFhi : g^2*(q-1) ≤ 9901/10000*(k*q) := by
    nlinarith only [mul_le_mul_of_nonneg_right hghi (show 0 ≤ q-1 by nlinarith only [hq2, hk2]), sq_nonneg g, hk0]
  have hFlo : 9898/10000*(k*q) ≤ g^2*(q-1) := by
    have hp := mul_le_mul_of_nonneg_right hglo (show 0 ≤ q-1 by nlinarith only [hq2, hk2])
    have hqq : 1000000 ≤ q := by nlinarith only [hq2, hk2]
    nlinarith only [hp, mul_nonneg hk0.le (sub_nonneg.mpr hqq)]
  have hshortlo : 19794/10000*(k*q) ≤ g^2*(2*q-4) := by
    have hp := mul_le_mul_of_nonneg_right hglo (show 0 ≤ 2*q-4 by nlinarith only [hq2, hk2])
    have hqq : 1000000 ≤ q := by nlinarith only [hq2, hk2]
    nlinarith only [hp, mul_nonneg hk0.le (sub_nonneg.mpr hqq)]
  have hshorthi : 2*k*q/100+g^2*(2*q-4) ≤ 3*(k*q) := by
    have hp := mul_le_mul_of_nonneg_right hghi (show 0 ≤ 2*q-4 by nlinarith only [hq2, hk2])
    nlinarith only [hp, mul_pos hk0 hq0]
  have hν0 : 0 < W/(q*g) := div_pos hW0 (mul_pos hq0 (by linarith))
  have hνk : W/(q*g)*(k*q) ≤ 3*k^2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos hq0 (show 0 < g by linarith))).mpr
    have hp := mul_le_mul_of_nonneg_right hW (mul_nonneg hk0.le hq0.le)
    have hp' := mul_le_mul_of_nonneg_left hg (show 0 ≤ 3*k^2*q by positivity)
    nlinarith only [hp, hp']
  have hνsmall : W/(q*g) < 1 := by
    apply (div_lt_iff₀ (mul_pos hq0 (show 0 < g by linarith))).mpr
    nlinarith only [hW, hqk, hk, mul_le_mul_of_nonneg_left hg hq0.le]
  have hcancel : W/(q*g)*(h*(q-h)+2*q+g^2*(q-1)) ≤ q/2 := by
    have harg : h*(q-h)+2*q+g^2*(q-1) ≤ 4*(k*q) := by
      nlinarith only [hHhi, hFhi, mul_le_mul_of_nonneg_right hk1 hq0.le, mul_pos hk0 hq0]
    have hp := mul_le_mul_of_nonneg_left harg hν0.le
    nlinarith only [hp, hνk, hq2]
  have hcancel' : W/(q*g)*(2*k*q/100+g^2*(2*q-4)) ≤ (k*q)/10000 := by
    have hp := mul_le_mul_of_nonneg_left hshorthi hν0.le
    have hp' := mul_le_mul_of_nonneg_left hqk hk0.le
    nlinarith only [hp, hνk, hp']
  dsimp
  refine ⟨?_, hν0, hνsmall, ?_, ?_, ?_, ?_⟩
  · have hkq := mul_le_mul_of_nonneg_right hk hq0.le
    nlinarith only [hHlo, hBerrlo, hkq, hq0]
  · have hkq := mul_le_mul_of_nonneg_right hk hq0.le
    nlinarith only [hHhi, hBerrhi, hFhi, hkq, hq0]
  · nlinarith only [hcancel, hBerrhi, hq0]
  · have hkq := mul_le_mul_of_nonneg_right hk hq0.le
    nlinarith only [hcancel', hshortlo, hBerrhi, hHhi, hFhi, hkq, hq0]
  · have hkq := mul_le_mul_of_nonneg_right hk hq0.le
    nlinarith only [hFlo, hBerrhi, hHhi, hkq, hq0]

/-- Each field names the corresponding branch in the paper's soundness proof. -/
structure GapInequalities (q : ℕ) (W M v : ℝ) : Prop where
  baseline_pos : 0 < reductionBaseline q W M v
  nu_pos : 0 < reductionNu q W
  nu_lt_one : reductionNu q W < 1
  zero_multiplier : reductionThreshold q W M v < reductionL q
  nonbinary_unit : (1-reductionNu q W)*(reductionH q+2*q+reductionF q) >
    reductionThreshold q W M v
  short_nonunit : (1-reductionNu q W)*(reductionL q/100+
    (rsGamma q : ℝ)^2*(2*(q : ℝ)-4)) > reductionThreshold q W M v
  long_nonunit : 3*reductionF q > reductionThreshold q W M v

/-- Uniform instance-independent parameters for the later reduction module. -/
structure ReductionParameters (q : ℕ) : Prop where
  q_large : 100001 ≤ q
  k_large : 1000000000000 ≤ rsK q
  gamma_pos : 0 < rsGamma q
  gamma_sq_lower : (9899/10000 : ℝ)*rsK q ≤ (rsGamma q : ℝ)^2
  gamma_sq_upper : (rsGamma q : ℝ)^2 ≤ (9901/10000 : ℝ)*rsK q
  gaps : ∀ W M v : ℝ, 0 < W → W ≤ 3*(rsT q : ℝ) →
    0 ≤ M → M ≤ W → 0 ≤ v → v ≤ W^2/(q : ℝ) → GapInequalities q W M v

/-- All the numerical gap obligations hold for every sufficiently large q,
uniformly in every instance of size at most T. No analytic hypothesis is used. -/
theorem reductionParameters_eventually : ∀ᶠ q in atTop, ReductionParameters q := by
  have hpoly : ∀ᶠ q in atTop, 1000000*rsK q^4 ≤ q := by
    filter_upwards [rsK_tendsto.eventually_ge_atTop 1000002] with q hk
    have hk1 : 1 ≤ rsK q := by omega
    have hp : 1000000*rsK q^4 ≤ rsK q^5 := by
      rw [pow_succ]
      nlinarith only [Nat.mul_le_mul_right (rsK q^4) (show 1000000 ≤ rsK q by omega)]
    exact hp.trans ((Nat.pow_le_pow_right hk1 (by norm_num : 5 ≤ 1000)).trans
      ((Nat.pow_le_pow_left (by omega : rsK q ≤ 2*rsK q) _).trans (rsK_pow_le q)))
  filter_upwards [eventually_ge_atTop 100001,
    rsK_tendsto.eventually_ge_atTop 1000000000000, rsT_small 1, hpoly] with q hq hk hT hp
  obtain ⟨hgl, hgu⟩ := rsGamma_sq_bounds hq hk
  have hg : 1 ≤ rsGamma q := le_max_left _ _
  refine ⟨hq, hk, by omega, hgl, hgu, ?_⟩
  intro W M v hW0 hW hM0 hM hv0 hv
  obtain ⟨hhlo, hhhi⟩ := rsH_real_rounding q
  have hTk : (rsT q : ℝ) ≤ rsK q := by exact_mod_cast (by simpa using hT : rsT q ≤ rsK q)
  have hh := reduction_gap_arithmetic (q := (q : ℝ)) (k := (rsK q : ℝ))
    (h := (rsH q : ℝ)) (g := (rsGamma q : ℝ))
    (by exact_mod_cast hk) (by exact_mod_cast hp) hhlo.le hhhi
    (by exact_mod_cast hg) hgl hgu hW0 (hW.trans (by linarith)) hM0 hM hv0 hv
  exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1,
    hh.2.2.2.2.2.1, hh.2.2.2.2.2.2⟩

/-- A direct projection convenient for consumers needing only the four gaps. -/
theorem gap_inequalities_eventually : ∀ᶠ q in atTop,
    ∀ W M v : ℝ, 0 < W → W ≤ 3*(rsT q : ℝ) →
      0 ≤ M → M ≤ W → 0 ≤ v → v ≤ W^2/(q : ℝ) → GapInequalities q W M v := by
  filter_upwards [reductionParameters_eventually] with q hq
  exact hq.gaps

/-- Completeness uses exactly the same threshold as soundness. -/
theorem reduction_completeness_threshold (q : ℕ) (W M v : ℝ) :
    reductionBaseline q W M v+(rsGamma q : ℝ)^2*((q : ℝ)-1) =
      reductionThreshold q W M v := rfl

/-- The strict final step of the long-multiplier case. -/
theorem ReductionParameters.long_coordinate {q : ℕ} (hq : ReductionParameters q) :
    3*reductionF q < 3*(q : ℝ)*(rsGamma q : ℝ)^2 := by
  have hg : 0 < (rsGamma q : ℝ) := by exact_mod_cast hq.gamma_pos
  unfold reductionF
  nlinarith only [sq_pos_of_pos hg]

/-- Binary root-of-unity soundness has the fixed additive gap two. -/
theorem reduction_binary_gap (q : ℕ) (W M v : ℝ) :
    reductionThreshold q W M v < reductionBaseline q W M v+2+reductionF q := by
  unfold reductionThreshold
  linarith

/-- The statistics-only baseline agrees with the existing rational checker API. -/
theorem checker_baseline_eq {q : ℕ} [NeZero q] (I : IdealCVP.X3CInstance)
    (V : RationalRing q) :
    ((Checker.B₀ I (rsH q) V : ℚ) : ℝ) =
      reductionBaseline q (Checker.W I) (3*I.q) ((normSq V : ℚ) : ℝ) := by
  unfold Checker.B₀ reductionBaseline reductionH
  push_cast
  ring

/-- The concrete checker satisfies the statistics bounds of the uniform interface. -/
theorem ReductionParameters.checker_gap {q : ℕ} [NeZero q] [Fact q.Prime]
    (hparams : ReductionParameters q) (I : IdealCVP.X3CInstance)
    (hq : q % 4 = 3) (s : IdealCVP.SidonPositions I.n)
    (hsize : I.n ≤ rsT q)
    (hcover : ∀ i : Fin (3*I.q), ∃ j, i ∈ I.triples j) :
    GapInequalities q (Checker.W I) (3*I.q)
      ((normSq (Checker.checkerV I hq s) : ℚ) : ℝ) := by
  have hW : Checker.W I = 3*I.n := Checker.incidence_count I
  have hrows := Checker.rows_le_incidence_count I hcover
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by have := hparams.q_large; omega : 0 < q)
  apply hparams.gaps
  · rw [hW]
    exact_mod_cast (by have := I.n_pos; omega : 0 < 3*I.n)
  · rw [hW]
    exact_mod_cast Nat.mul_le_mul_left 3 hsize
  · positivity
  · exact_mod_cast hrows
  · exact_mod_cast normSq_nonneg (Checker.checkerV I hq s)
  · have hv := Checker.checker_V_norm_bound I hq s (1 : RationalRing q)
    rw [mul_one, Checker.normSq_one] at hv
    have hvR : ((normSq (Checker.checkerV I hq s) : ℚ) : ℝ) ≤
        ((Checker.W I : ℝ)/(q : ℝ))^2*((q : ℝ)-1) := by
      have hh := (Rat.cast_le (K := ℝ)).mpr hv
      simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_sub,
        Rat.cast_natCast, Rat.cast_one] using hh
    apply hvR.trans
    apply (le_div_iff₀ hq0).mpr
    have he : (((Checker.W I : ℝ)/(q : ℝ))^2*((q : ℝ)-1))*(q : ℝ) =
        (Checker.W I : ℝ)^2-(Checker.W I : ℝ)^2/(q : ℝ) := by field_simp
    rw [he]
    linarith [div_nonneg (sq_nonneg (Checker.W I : ℝ)) hq0.le]

/-- The completed gap-and-stability lemma in the actual coefficient quotient model. -/
theorem ReductionParameters.checker_stability {q : ℕ} [NeZero q] [Fact q.Prime]
    (hparams : ReductionParameters q) (I : IdealCVP.X3CInstance)
    (hq : q % 4 = 3) (s : IdealCVP.SidonPositions I.n)
    (hsize : I.n ≤ rsT q)
    (hcover : ∀ i : Fin (3*I.q), ∃ j, i ∈ I.triples j)
    (y w : RationalRing q) :
    (1-reductionNu q (Checker.W I))*(((normSq y : ℚ) : ℝ)+
      (rsGamma q : ℝ)^2*((normSq w : ℚ) : ℝ)) ≤
      ((normSq (Checker.U (Checker.p I s)*y-Checker.checkerV I hq s*w) : ℚ) : ℝ)+
        (rsGamma q : ℝ)^2*((normSq w : ℚ) : ℝ) := by
  have hg : 0 < (rsGamma q : ℝ) := by exact_mod_cast hparams.gamma_pos
  have hgap := hparams.checker_gap I hq s hsize hcover
  exact Checker.checker_global_stability_real I hq s (rsGamma q) hg hgap.nu_pos hgap.nu_lt_one y w

/-- An explicit (very conservative) threshold for the entire reduction parameter package. -/
theorem reductionParameters_explicit {q : ℕ}
    (hq : max 100001 ((2*1000000000000)^1000) ≤ q) : ReductionParameters q := by
  have hq' : 100001 ≤ q := (le_max_left _ _).trans hq
  have hk : 1000000000000 ≤ rsK q :=
    le_rsK ((le_max_right _ _).trans hq)
  have hk1 : 1 ≤ rsK q := by omega
  have hT : rsT q ≤ rsK q := by
    have hs := rsT_sq_le q
    by_contra hn
    have hp := Nat.pow_le_pow_left (show rsK q+1 ≤ rsT q by omega) 2
    nlinarith
  have hp : 1000000*rsK q^4 ≤ q := by
    have hsmall : 1000000*rsK q^4 ≤ rsK q^5 := by
      rw [pow_succ]
      nlinarith only [Nat.mul_le_mul_right (rsK q^4) (show 1000000 ≤ rsK q by omega)]
    exact hsmall.trans ((Nat.pow_le_pow_right hk1 (by omega : 5 ≤ 1000)).trans
      ((Nat.pow_le_pow_left (by omega : rsK q ≤ 2*rsK q) _).trans (rsK_pow_le q)))
  obtain ⟨hgl, hgu⟩ := rsGamma_sq_bounds hq' hk
  have hg : 1 ≤ rsGamma q := le_max_left _ _
  refine ⟨hq', hk, by omega, hgl, hgu, ?_⟩
  intro W M v hW0 hW hM0 hM hv0 hv
  obtain ⟨hhlo, hhhi⟩ := rsH_real_rounding q
  have hTk : (rsT q : ℝ) ≤ rsK q := by exact_mod_cast hT
  have hh := reduction_gap_arithmetic (q := (q : ℝ)) (k := (rsK q : ℝ))
    (h := (rsH q : ℝ)) (g := (rsGamma q : ℝ))
    (by exact_mod_cast hk) (by exact_mod_cast hp) hhlo.le hhhi
    (by exact_mod_cast hg) hgl hgu hW0 (hW.trans (by linarith)) hM0 hM hv0 hv
  exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1,
    hh.2.2.2.2.2.1, hh.2.2.2.2.2.2⟩

/-- Positivity needed when clearing denominators and constructing the integral threshold. -/
theorem ReductionParameters.threshold_pos {q : ℕ} (hparams : ReductionParameters q)
    {W M v : ℝ} (hgap : GapInequalities q W M v) :
    0 < reductionThreshold q W M v := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by have := hparams.q_large; omega)
  have hF : 0 ≤ reductionF q := by
    unfold reductionF
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hq)
  unfold reductionThreshold
  exact add_pos_of_pos_of_nonneg hgap.baseline_pos hF

end
end Rank2ModuleSVP
