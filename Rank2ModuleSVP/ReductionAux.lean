import Rank2ModuleSVP.Checker
import Rank2ModuleSVP.Admissible
import Rank2ModuleSVP.RobustCenter
import Rank2ModuleSVP.BennettPeikert
import Rank2ModuleSVP.Problem

/-! # Parameters and geometry of the rank-two reduction

Paper v2 §5: explicit cutoffs, scale estimates, and elementary norm bounds.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Rank2ModuleSVP
noncomputable section
open scoped BigOperators
open Checker
variable {q : ℕ} [NeZero q]

/-- A common lower cutoff for the counting and separation bounds. -/
def redK0 : ℕ := max cntK0 sepK0
/-- A common exponent for the counting and separation regimes. -/
def redC0 : ℕ := max cntC0 sepC0

theorem cntH_eq_sepWeight (k : ℕ) : cntH k = sepWeight k := rfl

/-- The floor of the real square root in (23), computed entirely in naturals. -/
def redGamma (k : ℕ) : ℕ := Nat.sqrt (9 * k / 10)
/-- The integral squared-norm budget for the second module coordinate. -/
def redF (k q : ℕ) : ℤ := (redGamma k : ℤ) ^ 2 * ((q : ℤ) - 1)
/-- Relative error parameter used in the global stability bound. -/
def redNu (I : IdealCVP.X3CInstance) (k : ℕ) : ℚ :=
  2 * (W I) / (Q I (cntH k) * redGamma k)
/-- The integral squared-norm threshold of the reduction. -/
def redS (I : IdealCVP.X3CInstance) (k : ℕ) : ℤ :=
  thresholdNumerator (q := q) I (cntH k) (redF k q)
/-- The first integral module generator in paper v2 equation (22). -/
def redM1 (I : IdealCVP.X3CInstance) (s : IdealCVP.SidonPositions I.n)
    (k : ℕ) : IntegerRing q × IntegerRing q :=
  (U I s (cntH k) * (pi : IntegerRing q) ^ k, 0)
/-- The second integral module generator in paper v2 equation (22). -/
def redM2 (I : IdealCVP.X3CInstance) (s : IdealCVP.SidonPositions I.n)
    (k : ℕ) : IntegerRing q × IntegerRing q :=
  (U I s (cntH k) * sepCenter k - V I s, -((Q I (cntH k) * redGamma k : ℕ) : IntegerRing q))

omit [NeZero q] in
theorem red_regime {k : ℕ} (hk : redK0 ≤ k) (hq : (2 * k) ^ redC0 ≤ q) :
    cntK0 ≤ k ∧ sepK0 ≤ k ∧ (2 * k) ^ cntC0 ≤ q ∧ 2 * k ≤ q := by
  have hc := cnt_regime_mono (le_max_left _ _) (le_max_left _ _) hk hq
  have hs : sepK0 ≤ k := (le_max_right _ _).trans hk
  have hp := cnt_q_polynomial hc.1 hc.2
  have hk0 : 100000000 ≤ k := hc.1
  have hkp : k ≤ k ^ 4 := Nat.le_self_pow (by norm_num) k
  exact ⟨hc.1, hs, hc.2, by omega⟩

theorem redGamma_rounding (k : ℕ) :
    10 * (redGamma k) ^ 2 ≤ 9 * k ∧ 9 * k < 10 * (redGamma k + 1) ^ 2 := by
  have hl := Nat.sqrt_le (9 * k / 10)
  have hu := Nat.lt_succ_sqrt (9 * k / 10)
  change Nat.sqrt (9 * k / 10) * Nat.sqrt (9 * k / 10) ≤ 9 * k / 10 at hl
  change 9 * k / 10 < (Nat.sqrt (9 * k / 10) + 1) * (Nat.sqrt (9 * k / 10) + 1) at hu
  constructor <;> simp only [redGamma, pow_two] <;> omega

theorem redGamma_bounds {k : ℕ} (hk : redK0 ≤ k) :
    100 ≤ redGamma k ∧ 89 * k ≤ 100 * (redGamma k) ^ 2 ∧ 10 * (redGamma k) ^ 2 ≤ 9 * k := by
  have hk0 : 100000000 ≤ k := (le_max_left _ _).trans hk
  obtain ⟨hl, hu⟩ := redGamma_rounding k
  have hg : 100 ≤ redGamma k := by
    by_contra hn
    have : redGamma k ≤ 99 := by omega
    nlinarith
  have hg2 : 9000 ≤ redGamma k := by
    by_contra hn
    have : redGamma k ≤ 8999 := by omega
    nlinarith
  refine ⟨hg, ?_, hl⟩
  have hm : 9000 * redGamma k ≤ (redGamma k) ^ 2 := by
    nlinarith [Nat.mul_le_mul_left (redGamma k) hg2]
  nlinarith

theorem redQ_pos (I : IdealCVP.X3CInstance) {k : ℕ} (hk : redK0 ≤ k) :
    0 < Q I (cntH k) := by
  have hk0 : 100000000 ≤ k := (le_max_left _ _).trans hk
  exact Q_pos I _ (by have := (cntH_bounds k).1; omega)

theorem redNu_bounds (I : IdealCVP.X3CInstance) {k : ℕ} (hk : redK0 ≤ k) :
    0 < redNu I k ∧ redNu I k ≤ 1 / (100 * (k : ℚ)) ∧ redNu I k < 1 := by
  have hk0 : 100000000 ≤ k := (le_max_left _ _).trans hk
  have hkQ : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hW : (3 : ℚ) ≤ W I := by exact_mod_cast W_ge_three I
  have hh : (k : ℚ) ≤ cntH k := by exact_mod_cast (cntH_bounds k).1
  have hg : (100 : ℚ) ≤ redGamma k := by exact_mod_cast (redGamma_bounds hk).1
  have hW1 : (W I : ℚ) ≤ (W I : ℚ) ^ 4 := by
    have : (1 : ℚ) ≤ W I := by linarith
    simpa using (le_self_pow₀ this (by norm_num : (4 : ℕ) ≠ 0))
  have hQ : (Q I (cntH k) : ℚ) = 128 * (W I : ℚ) ^ 4 * cntH k := by simp [Q]
  have hhp : (0 : ℚ) < cntH k := hkQ.trans_le hh
  have hWp : (0 : ℚ) < W I := by linarith
  have hgp : (0 : ℚ) < redGamma k := by linarith
  have hd : (0 : ℚ) < Q I (cntH k) * redGamma k := by rw [hQ]; positivity
  have hb : 200 * (W I : ℚ) * k ≤ Q I (cntH k) * redGamma k := by
    rw [hQ]
    have h1 := mul_le_mul_of_nonneg_right hW1 hkQ.le
    have h2 := mul_le_mul_of_nonneg_left hh (pow_nonneg (by positivity : (0 : ℚ) ≤ W I) 4)
    have h3 := mul_le_mul_of_nonneg_left hg
      (show (0 : ℚ) ≤ 128 * (W I : ℚ) ^ 4 * cntH k by positivity)
    nlinarith
  have hn : redNu I k ≤ 1 / (100 * (k : ℚ)) := by
    unfold redNu
    apply (div_le_div_iff₀ hd (by positivity)).mpr
    nlinarith
  refine ⟨by unfold redNu; positivity, hn, ?_⟩
  have : 1 / (100 * (k : ℚ)) < 1 := (div_lt_one (by positivity)).mpr (by exact_mod_cast (show
      1 < 100 * k by omega))
  exact hn.trans_lt this

theorem redS_eq (I : IdealCVP.X3CInstance) {k : ℕ} (hk : redK0 ≤ k) :
    (redS (q := q) I k : ℚ) = (Q I (cntH k) : ℚ) ^ 2 *
      (B₀ (q := q) I (cntH k) + (redF k q : ℚ) + kappa (q := q) I (cntH k)) := by
  have hk0 : 100000000 ≤ k := (le_max_left _ _).trans hk
  have hh : 1 ≤ cntH k := by have := (cntH_bounds k).1; omega
  symm
  rw [mul_add, mul_add, baseline_scale_eq I _ hh, kappa_scale_eq I _ hh]
  simp [redS, thresholdNumerator]

/-- Multiplication by an integer scales the canonical squared norm. -/
theorem red_normSq_int_mul (a : ℤ) (v : IntegerRing q) :
    normSq ((a : IntegerRing q) * v) = a ^ 2 * normSq v := by
  obtain ⟨x, rfl⟩ := classOf_surjective v
  have he : ((a : IntegerRing q) * classOf x) = classOf (fun b => a * x b) := by
    have h := ((classOfAddHom (q := q)).map_zsmul a x).symm
    have hx : (a • x : Coeff ℤ q) = (fun b => a * x b) := by
      ext b
      simp only [Pi.smul_apply, zsmul_eq_mul]
      rfl
    rw [hx] at h
    simpa only [classOfAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, zsmul_eq_mul] using h
  rw [he, normSq_classOf, normSq_classOf, coeffNormSq_mul_int]

theorem red_normSq_nat_mul (a : ℕ) (v : IntegerRing q) :
    normSq ((a : IntegerRing q) * v) = (a : ℤ) ^ 2 * normSq v := by
  simpa using red_normSq_int_mul (q := q) (a : ℤ) v

theorem red_normSq_one : normSq (1 : IntegerRing q) = (q : ℤ) - 1 := by
  simpa using normSq_monomial (q := q) 0

theorem red_moduleVector (I : IdealCVP.X3CInstance) (s : IdealCVP.SidonPositions I.n)
    (k : ℕ) (z w : IntegerRing q) :
    moduleVector (redM1 I s k) (redM2 I s k) z w =
      (U I s (cntH k) * (z * (pi : IntegerRing q) ^ k + w * sepCenter k) - V I s * w,
        -((Q I (cntH k) * redGamma k : ℕ) : IntegerRing q) * w) := by
  ext <;> simp [moduleVector, redM1, redM2] <;> ring

theorem red_moduleVector_norm (I : IdealCVP.X3CInstance) (s : IdealCVP.SidonPositions I.n)
    (k : ℕ) (z w : IntegerRing q) :
    pairNormSq (moduleVector (redM1 I s k) (redM2 I s k) z w) =
      normSq (U I s (cntH k) * (z * (pi : IntegerRing q) ^ k + w * sepCenter k) - V I s * w) +
        (Q I (cntH k) : ℤ) ^ 2 * (redGamma k : ℤ) ^ 2 * normSq w := by
  rw [red_moduleVector]
  simp only [pairNormSq]
  change normSq _ + normSq (-((Q I (cntH k) * redGamma k : ℕ) : IntegerRing q) * w) = _
  rw [show - ((Q I (cntH k) * redGamma k : ℕ) : IntegerRing q) * w =
    -(((Q I (cntH k) * redGamma k : ℕ) : IntegerRing q) * w) by ring, normSq_neg,
        red_normSq_nat_mul]
  push_cast
  ring

/-- Lemma 5.1, over all rational cyclotomic elements. -/
theorem red_global_stability (I : IdealCVP.X3CInstance) (s : IdealCVP.SidonPositions I.n)
    {k : ℕ} (hk : redK0 ≤ k) (y w : RationalRing q) :
    (Q I (cntH k) : ℚ) ^ 2 * (1 - redNu I k) *
      (normSq y + (redGamma k : ℚ) ^ 2 * normSq w) ≤
        normSq (UQ I s (cntH k) * y - VQ I s * w) +
          (Q I (cntH k) : ℚ) ^ 2 * (redGamma k : ℚ) ^ 2 * normSq w := by
  obtain ⟨hn, hb, hn1⟩ := redNu_bounds I hk
  have hQ : (0 : ℚ) < Q I (cntH k) := by exact_mod_cast redQ_pos I hk
  have hg : (0 : ℚ) < redGamma k := by
    have := (redGamma_bounds hk).1
    exact_mod_cast (show 0 < redGamma k by omega)
  have h := global_stability_exact
    ((Q I (cntH k) : ℚ)⁻¹ • UQ I s (cntH k))
    ((Q I (cntH k) : ℚ)⁻¹ • VQ I s) y w (redGamma k : ℚ) (redNu I k)
    hn hn1 ?_ ?_
  · have hm := mul_le_mul_of_nonneg_left h (sq_nonneg (Q I (cntH k) : ℚ))
    simp only [smul_mul_assoc, ← smul_sub, normSq_smul] at hm
    have he : (Q I (cntH k) : ℚ) ^ 2 * ((Q I (cntH k) : ℚ)⁻¹) ^ 2 = 1 := by field_simp
    have hr : (Q I (cntH k) : ℚ) ^ 2 *
        ((Q I (cntH k) : ℚ)⁻¹ ^ 2 * normSq (UQ I s (cntH k) * y - VQ I s * w) +
          (redGamma k : ℚ) ^ 2 * normSq w) =
        normSq (UQ I s (cntH k) * y - VQ I s * w) +
          (Q I (cntH k) : ℚ) ^ 2 * (redGamma k : ℚ) ^ 2 * normSq w := by
      rw [mul_add, ← mul_assoc, he, one_mul]
      ring
    rw [hr] at hm
    convert hm using 1; ring
  · rw [smul_mul_assoc, normSq_smul]
    have hu := checker_U_norm_lower I s (cntH k) y
    have he : ((Q I (cntH k) : ℚ)⁻¹) ^ 2 * (Q I (cntH k) : ℚ) ^ 2 = 1 := by field_simp
    have hm := mul_le_mul_of_nonneg_left hu (sq_nonneg (Q I (cntH k) : ℚ)⁻¹)
    rwa [← mul_assoc, he, one_mul] at hm
  · rw [smul_mul_assoc, normSq_smul]
    have hv := checker_V_norm_bound I s w
    have he : (redNu I k) ^ 2 * (redGamma k : ℚ) ^ 2 =
        ((Q I (cntH k) : ℚ)⁻¹) ^ 2 * (2 * (W I : ℚ)) ^ 2 := by
      unfold redNu
      field_simp
    rw [he]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hv (sq_nonneg (Q I (cntH k) : ℚ)⁻¹)

/-- A coarse scale inequality, convenient for all four soundness cases. -/
theorem redQ_large (I : IdealCVP.X3CInstance) (k : ℕ) :
    (128 : ℚ) * (W I) * cntH k ≤ Q I (cntH k) ∧
      (10000 : ℚ) * k ≤ Q I (cntH k) := by
  have hW : (3 : ℚ) ≤ W I := by exact_mod_cast W_ge_three I
  have hh : (k : ℚ) ≤ cntH k := by exact_mod_cast (cntH_bounds k).1
  have hW4 : (81 : ℚ) ≤ (W I : ℚ) ^ 4 := by
    have h2 : (9 : ℚ) ≤ (W I : ℚ) ^ 2 := by nlinarith
    nlinarith [sq_nonneg ((W I : ℚ) ^ 2 - 9)]
  have hW1 : (W I : ℚ) ≤ (W I : ℚ) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hQ : (Q I (cntH k) : ℚ) = 128 * (W I : ℚ) ^ 4 * cntH k := by simp [Q]
  rw [hQ]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hW1 (Nat.cast_nonneg (cntH k) : (0 : ℚ) ≤ _)]
  · have hm := mul_le_mul_of_nonneg_right hW4 (Nat.cast_nonneg (cntH k) : (0 : ℚ) ≤ _)
    nlinarith

/-- The upper estimate needs no assumption about zero rows in the X3C input. -/
theorem red_baseline_upper (I : IdealCVP.X3CInstance) {k : ℕ} (hk : redK0 ≤ k) :
    B₀ (q := q) I (cntH k) - (cntH k : ℚ) * (q - cntH k) ≤ ((q : ℚ) + 1) / 32 := by
  have hq : (0 : ℚ) < q := by exact_mod_cast NeZero.pos q
  have hQ : (0 : ℚ) < Q I (cntH k) := by exact_mod_cast redQ_pos I hk
  have hkappa : 0 ≤ kappa (q := q) I (cntH k) := by unfold kappa; positivity
  have hb : 2 * (W I : ℚ) * cntH k - 2 * (3 * I.q) +
      (2 * (cntH k : ℚ) * W I - 4 * (cntH k : ℚ) ^ 2 * (W I : ℚ) ^ 2) / q ≤
      2 * (W I : ℚ) * cntH k + 2 * (cntH k : ℚ) * W I / q := by
    have hm : 0 ≤ (3 * I.q : ℚ) := by positivity
    have hn : 0 ≤ 4 * (cntH k : ℚ) ^ 2 * (W I : ℚ) ^ 2 / q := by positivity
    rw [sub_div]
    linarith
  have hm := mul_le_mul_of_nonneg_left hb hkappa
  have he : kappa (q := q) I (cntH k) *
      (2 * (W I : ℚ) * cntH k + 2 * (cntH k : ℚ) * W I / q) =
      4 * (cntH k : ℚ) * W I * ((q : ℚ) + 1) / (Q I (cntH k)) := by
    unfold kappa
    field_simp
    ring
  rw [he] at hm
  have hscale := (redQ_large I k).1
  have hh : 4 * (cntH k : ℚ) * W I * ((q : ℚ) + 1) / (Q I (cntH k)) ≤ ((q : ℚ) + 1) / 32 := by
    apply (div_le_iff₀ hQ).mpr
    nlinarith [mul_le_mul_of_nonneg_right hscale (show (0 : ℚ) ≤ q + 1 by positivity)]
  unfold B₀
  linarith

/-- A uniform, explicit version of κ = O(q/k). -/
theorem red_kappa_bounds (I : IdealCVP.X3CInstance) {k : ℕ} (hk : redK0 ≤ k) :
    0 < kappa (q := q) I (cntH k) ∧
      kappa (q := q) I (cntH k) ≤ (q : ℚ) / (5000 * k) := by
  have hk0 : 100000000 ≤ k := (le_max_left _ _).trans hk
  have hk' : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hq : (0 : ℚ) < q := by exact_mod_cast NeZero.pos q
  have hQ : (0 : ℚ) < Q I (cntH k) := by exact_mod_cast redQ_pos I hk
  refine ⟨by unfold kappa; positivity, ?_⟩
  unfold kappa
  apply (div_le_div_iff₀ hQ (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left (redQ_large I k).2 hq.le]

/-- A fixed margin below the ideal minimum; no zero-row premise is needed. -/
theorem red_threshold_upper (I : IdealCVP.X3CInstance) {k : ℕ} (hk : redK0 ≤ k) :
    B₀ (q := q) I (cntH k) + (redF k q : ℚ) + kappa (q := q) I (cntH k) <
      49 * (k : ℚ) * q / 25 := by
  have hk0 : 100000000 ≤ k := (le_max_left _ _).trans hk
  have hk' : (100000000 : ℚ) ≤ k := by exact_mod_cast hk0
  have hq : (1 : ℚ) ≤ q := by exact_mod_cast NeZero.pos q
  have hh := (cntH_real_rounding k).2
  have hh : (cntH k : ℚ) ≤ 21 * k / 20 := by
    have h := (cntH_rounding k).1
    have h' : (20 : ℚ) * cntH k ≤ 21 * k := by exact_mod_cast h
    linarith
  have hg : (10 : ℚ) * (redGamma k : ℚ) ^ 2 ≤ 9 * k := by
    exact_mod_cast (redGamma_rounding k).1
  have hH : (cntH k : ℚ) * (q - cntH k) ≤ 21 * (k : ℚ) * q / 20 := by
    nlinarith [mul_le_mul_of_nonneg_right hh (show (0 : ℚ) ≤ q by positivity), sq_nonneg (cntH
        k : ℚ)]
  have hF : (redF k q : ℚ) ≤ 9 * (k : ℚ) * q / 10 := by
    dsimp [redF]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hg (show (0 : ℚ) ≤ q by positivity)]
  have hB := red_baseline_upper (q := q) I hk
  have hκ := (red_kappa_bounds (q := q) I hk).2
  have hκ' : kappa (q := q) I (cntH k) ≤ (q : ℚ) := by
    apply hκ.trans
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 5000 * k)).mpr
    nlinarith
  have hkq : (100000000 : ℚ) * q ≤ (k : ℚ) * q :=
    mul_le_mul_of_nonneg_right hk' (by positivity)
  linarith

/-- Lemma 5.1 in the integral model, with all denominators outside the norm. -/
theorem red_global_stability_int (I : IdealCVP.X3CInstance) (s : IdealCVP.SidonPositions I.n)
    {k : ℕ} (hk : redK0 ≤ k) (y w : IntegerRing q) :
    (Q I (cntH k) : ℚ) ^ 2 * (1 - redNu I k) *
      (((normSq y : ℤ) : ℚ) + (redGamma k : ℚ) ^ 2 * ((normSq w : ℤ) : ℚ)) ≤
        ((normSq (U I s (cntH k) * y - V I s * w) : ℤ) : ℚ) +
          (Q I (cntH k) : ℚ) ^ 2 * (redGamma k : ℚ) ^ 2 * ((normSq w : ℤ) : ℚ) := by
  have h := red_global_stability I s hk (rationalize y) (rationalize w)
  change _ ≤ normSq (rationalize (U I s (cntH k)) * rationalize y-
    rationalize (V I s) * rationalize w) + _ at h
  simpa only [← map_mul, ← map_sub, normSq_rationalize] using h

theorem red_nonbinary_margin (I : IdealCVP.X3CInstance) {k : ℕ} (hk : redK0 ≤ k) :
    B₀ (q := q) I (cntH k) + (redF k q : ℚ) + kappa (q := q) I (cntH k) <
      (1 - redNu I k) * ((cntH k : ℚ) * (q - cntH k) + 2 * q + (redF k q : ℚ)) := by
  have hk0 : 100000000 ≤ k := (le_max_left _ _).trans hk
  have hk' : (100000000 : ℚ) ≤ k := by exact_mod_cast hk0
  have hq : (1 : ℚ) ≤ q := by exact_mod_cast NeZero.pos q
  have hh : (cntH k : ℚ) ≤ 21 * k / 20 := by
    have h : (20 : ℚ) * cntH k ≤ 21 * k := by exact_mod_cast (cntH_rounding k).1
    linarith
  have hg : (10 : ℚ) * (redGamma k : ℚ) ^ 2 ≤ 9 * k := by exact_mod_cast (redGamma_rounding k).1
  have hH : (cntH k : ℚ) * (q - cntH k) ≤ 21 * (k : ℚ) * q / 20 := by
    nlinarith [mul_le_mul_of_nonneg_right hh (show (0 : ℚ) ≤ q by positivity), sq_nonneg (cntH
        k : ℚ)]
  have hF : (redF k q : ℚ) ≤ 9 * (k : ℚ) * q / 10 := by
    dsimp [redF]; push_cast
    nlinarith [mul_le_mul_of_nonneg_right hg (show (0 : ℚ) ≤ q by positivity)]
  obtain ⟨hν, hνb, hν1⟩ := redNu_bounds I hk
  have hνk : redNu I k * (k : ℚ) ≤ 1 / 100 := by
    have h := (le_div_iff₀ (show (0 : ℚ) < 100 * k by positivity)).mp hνb
    linarith
  have hT : (cntH k : ℚ) * (q - cntH k) + 2 * q + (redF k q : ℚ) ≤ 3 * (k : ℚ) * q := by
    have : (100000000 : ℚ) * q ≤ (k : ℚ) * q := mul_le_mul_of_nonneg_right hk' (by positivity)
    linarith
  have hm := mul_le_mul_of_nonneg_left hT hν.le
  have hm' := mul_le_mul_of_nonneg_right hνk (show (0 : ℚ) ≤ 3 * q by positivity)
  have hB := red_baseline_upper (q := q) I hk
  have hκ := (red_kappa_bounds (q := q) I hk).2
  have hκ' : kappa (q := q) I (cntH k) ≤ (q : ℚ) := by
    apply hκ.trans
    apply (div_le_iff₀ (show (0 : ℚ) < 5000 * k by positivity)).mpr
    nlinarith
  nlinarith

theorem red_small_multiplier_margin (I : IdealCVP.X3CInstance) {k : ℕ}
    (hk : redK0 ≤ k) (hpow : (2 * k) ^ redC0 ≤ q) :
    B₀ (q := q) I (cntH k) + (redF k q : ℚ) + kappa (q := q) I (cntH k) <
      (1 - redNu I k) * ((k : ℚ) * q / 5 + (redGamma k : ℚ) ^ 2 * (2 * q - 4)) := by
  obtain ⟨hcnt, hsep, hcntq, hkq⟩ := red_regime hk hpow
  have hk0 : 100000000 ≤ k := hcnt
  have hk' : (100000000 : ℚ) ≤ k := by exact_mod_cast hk0
  have hq' : 1000 ≤ q := by
    have := cnt_q_polynomial hcnt hcntq
    have := Nat.le_self_pow (by norm_num : (4 : ℕ) ≠ 0) k
    omega
  have hq : (1000 : ℚ) ≤ q := by exact_mod_cast hq'
  have hglo : (89 : ℚ) * k ≤ 100 * (redGamma k : ℚ) ^ 2 := by
    exact_mod_cast (redGamma_bounds hk).2.1
  have hghi : (redGamma k : ℚ) ^ 2 ≤ k := by
    have h : (10 : ℚ) * (redGamma k : ℚ) ^ 2 ≤ 9 * k := by exact_mod_cast (redGamma_rounding k).1
    nlinarith
  obtain ⟨hν, hνb, hν1⟩ := redNu_bounds I hk
  have hνk : redNu I k * (k : ℚ) ≤ 1 / 100 := by
    have h := (le_div_iff₀ (show (0 : ℚ) < 100 * k by positivity)).mp hνb
    linarith
  have hlo := mul_le_mul_of_nonneg_right hglo (show (0 : ℚ) ≤ 2 * q - 4 by linarith)
  have hhi := mul_le_mul_of_nonneg_right hghi (show (0 : ℚ) ≤ 2 * q - 4 by linarith)
  have hT : (k : ℚ) * q / 5 + (redGamma k : ℚ) ^ 2 * (2 * q - 4) ≤ 3 * (k : ℚ) * q := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hT hν.le
  have hm' := mul_le_mul_of_nonneg_right hνk (show (0 : ℚ) ≤ 3 * q by positivity)
  have hqk := mul_le_mul_of_nonneg_left hq (show (0 : ℚ) ≤ k by positivity)
  have hkq' := mul_le_mul_of_nonneg_right hk' (show (0 : ℚ) ≤ q by positivity)
  have hu := red_threshold_upper (q := q) I hk
  nlinarith

theorem red_large_multiplier_margin (I : IdealCVP.X3CInstance) {k : ℕ}
    (hk : redK0 ≤ k) (hpow : (2 * k) ^ redC0 ≤ q) :
    B₀ (q := q) I (cntH k) + (redF k q : ℚ) + kappa (q := q) I (cntH k) < 3 * (redF k q : ℚ) := by
  obtain ⟨hcnt, hsep, hcntq, hkq⟩ := red_regime hk hpow
  have hk0 : 100000000 ≤ k := hcnt
  have hk' : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hq' : 1000 ≤ q := by
    have := cnt_q_polynomial hcnt hcntq
    have := Nat.le_self_pow (by norm_num : (4 : ℕ) ≠ 0) k
    omega
  have hq : (1000 : ℚ) ≤ q := by exact_mod_cast hq'
  have hglo : (89 : ℚ) * k ≤ 100 * (redGamma k : ℚ) ^ 2 := by
    exact_mod_cast (redGamma_bounds hk).2.1
  have hlo := mul_le_mul_of_nonneg_right hglo (show (0 : ℚ) ≤ q - 1 by linarith)
  have hqk := mul_le_mul_of_nonneg_left hq hk'.le
  have hu := red_threshold_upper (q := q) I hk
  have he : (redF k q : ℚ) = (redGamma k : ℚ) ^ 2 * (q - 1) := by simp [redF]
  rw [he]
  nlinarith

/-- Explicit lower baseline estimate; the paper assumes M ≤ W after preprocessing. -/
theorem red_baseline_lower (I : IdealCVP.X3CInstance) {k : ℕ} (hk : redK0 ≤ k)
    (hrows : 3 * I.q ≤ W I) :
    -(cntH k : ℚ) / 16 ≤ B₀ (q := q) I (cntH k) - (cntH k : ℚ) * (q - cntH k) := by
  have hq : (0 : ℚ) < q := by exact_mod_cast NeZero.pos q
  have hQ : (0 : ℚ) < Q I (cntH k) := by exact_mod_cast redQ_pos I hk
  have hk0 : 100000000 ≤ k := (le_max_left _ _).trans hk
  have hh : (1 : ℚ) ≤ cntH k := by
    exact_mod_cast (show 1 ≤ cntH k by have := (cntH_bounds k).1; omega)
  have hW : (3 : ℚ) ≤ W I := by exact_mod_cast W_ge_three I
  have hM : (3 * I.q : ℚ) ≤ W I := by exact_mod_cast hrows
  have hκ : 0 ≤ kappa (q := q) I (cntH k) := (red_kappa_bounds (q := q) I hk).1.le
  have hb : -(4 * (cntH k : ℚ) ^ 2 * (W I : ℚ) ^ 2 / q) ≤
      2 * (W I : ℚ) * cntH k - 2 * (3 * I.q) +
        (2 * (cntH k : ℚ) * W I - 4 * (cntH k : ℚ) ^ 2 * (W I : ℚ) ^ 2) / q := by
    have hprod := mul_le_mul_of_nonneg_left hh (show (0 : ℚ) ≤ W I by positivity)
    have : (0 : ℚ) ≤ 2 * (cntH k : ℚ) * W I / q := by positivity
    rw [sub_div]
    linarith
  have hm := mul_le_mul_of_nonneg_left hb hκ
  have he : kappa (q := q) I (cntH k) * (-(4 * (cntH k : ℚ) ^ 2 * (W I : ℚ) ^ 2 / q)) =
      -8 * (cntH k : ℚ) ^ 2 * (W I : ℚ) ^ 2 / (Q I (cntH k)) := by
    unfold kappa
    field_simp
    ring
  rw [he] at hm
  have hW2 : (W I : ℚ) ^ 2 ≤ (W I : ℚ) ^ 4 := by
    have h2 : (1 : ℚ) ≤ (W I : ℚ) ^ 2 := by nlinarith
    nlinarith
  have hscale : (128 : ℚ) * (W I : ℚ) ^ 2 * cntH k ≤ Q I (cntH k) := by
    simp only [Q, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    nlinarith [mul_le_mul_of_nonneg_right hW2 (show (0 : ℚ) ≤ cntH k by positivity)]
  have hbound : -(cntH k : ℚ) / 16 ≤ -8 * (cntH k : ℚ) ^ 2 * (W I : ℚ) ^ 2 / (Q I (cntH k)) := by
    apply (le_div_iff₀ hQ).mpr
    nlinarith [mul_le_mul_of_nonneg_right hscale (show (0 : ℚ) ≤ cntH k by positivity)]
  unfold B₀
  linarith

/-- Nonnegativity for the preprocessed inputs of paper Section 5.3.
Without M ≤ W, the requested unconditional assertion is false. -/
theorem redS_nonneg (I : IdealCVP.X3CInstance) {k : ℕ} (hk : redK0 ≤ k)
    (hpow : (2 * k) ^ redC0 ≤ q) (hrows : 3 * I.q ≤ W I) : 0 ≤ redS (q := q) I k := by
  obtain ⟨hcnt, hsep, hcntq, hkq⟩ := red_regime hk hpow
  have hk0 : 100000000 ≤ k := hcnt
  have hp := cnt_q_polynomial hcnt hcntq
  have hkp : k ≤ k ^ 4 := Nat.le_self_pow (by norm_num) k
  have hh : cntH k ≤ 2 * k := (cntH_bounds k).2
  have hq : (cntH k : ℚ) + 1 ≤ q := by exact_mod_cast (show cntH k + 1 ≤ q by omega)
  have hB := red_baseline_lower (q := q) I hk hrows
  have hH : (cntH k : ℚ) ≤ (cntH k : ℚ) * (q - cntH k) := by
    nlinarith [mul_nonneg (show (0 : ℚ) ≤ cntH k by positivity) (show (0 : ℚ) ≤ q - cntH k - 1
        by linarith)]
  have hF : (0 : ℚ) ≤ redF k q := by
    have hq1 : (1 : ℚ) ≤ q := by exact_mod_cast NeZero.pos q
    simp only [redF, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_sub, Int.cast_one]
    positivity
  have hκ := (red_kappa_bounds (q := q) I hk).1
  have hT : (0 : ℚ) ≤ B₀ (q := q) I (cntH k) + (redF k q : ℚ) + kappa (q := q) I (cntH k) := by
    linarith [Nat.cast_nonneg (α := ℚ) (cntH k)]
  have hS : (0 : ℚ) ≤ redS (q := q) I k := by rw [redS_eq I hk]; exact mul_nonneg (sq_nonneg _) hT
  exact_mod_cast hS

/-- Downstream choices may increase both absolute constants. -/
theorem red_regime_mono {K C k q : ℕ} (hK : redK0 ≤ K) (hC : redC0 ≤ C)
    (hk : K ≤ k) (hq : (2 * k) ^ C ≤ q) : redK0 ≤ k ∧ (2 * k) ^ redC0 ≤ q := by
  have hk0 : 100000000 ≤ k := (le_max_left _ _).trans (hK.trans hk)
  exact ⟨hK.trans hk, (Nat.pow_le_pow_right (by omega : 1 ≤ 2 * k) hC).trans hq⟩

end
end Rank2ModuleSVP
