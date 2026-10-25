module

public import Power2ModuleSVP.Seed.RudinShapiro.Derivative
public import Power2ModuleSVP.Seed.Geometry.JetSeparation
public import Power2ModuleSVP.Seed.Geometry.Cells
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Wave

The normalized slowly varying Rudin--Shapiro blocks and their two-frequency
real wave. Exact carrier-modulated derivative formulas give the first five
jet bounds and the four-jet nondegeneracy estimate. This instantiates the
seven-cell argument with actual polynomials, rather than a new hypothesis.

Paper: `paper/power2svp.pdf`, Appendix A.1 (Lemma 9, Rudin–Shapiro waves and small intervals).
-/

@[expose] public section
namespace Power2ModuleSVP
open scoped BigOperators ContDiff
noncomputable section

private theorem smooth_derivative_family (A : ℕ → ℝ → ℂ)
    (hA : ∀ r x, HasDerivAt (A r) (A (r + 1) x) x) (n r : ℕ) :
    ContDiff ℝ n (A r) := by
  induction n generalizing r with
  | zero =>
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun x => (hA r x).continuousAt)
  | succ n ih =>
    change ContDiff ℝ ((n : ℕ∞ω) + 1) (A r)
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun x => (hA r x).differentiableAt, by simp, ?_⟩
    have he : _root_.deriv (A r) = A (r + 1) := funext fun x => (hA r x).deriv
    rw [he]
    exact ih (r + 1)

private theorem derivative_family_eq_iterate (A : ℕ → ℝ → ℂ)
    (hA : ∀ r x, HasDerivAt (A r) (A (r + 1) x) x) (r : ℕ) :
    A r = _root_.deriv^[r] (A 0) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ← ih]
    exact funext fun x => (hA r x).deriv.symm

/-- The unit circle carrier at a real frequency. -/
def seedWavePhase (freq x : ℝ) : ℂ := Complex.exp ((freq : ℂ) * (x : ℂ) * Complex.I)

theorem seedWavePhase_norm (freq x : ℝ) : ‖seedWavePhase freq x‖ = 1 := by
  simp [seedWavePhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem seedWavePhase_hasDerivAt (freq x : ℝ) :
    HasDerivAt (seedWavePhase freq) ((freq : ℂ) * Complex.I * seedWavePhase freq x) x := by
  have h := ((((hasDerivAt_id (x : ℂ)).const_mul (freq : ℂ)).mul_const Complex.I).cexp).comp_ofReal
  convert! h using 1
  simp only [seedWavePhase, id_eq, mul_one]
  ring

private theorem seedWavePhase_derivatives (freq : ℝ) (r : ℕ) :
    iteratedDeriv r (seedWavePhase freq) =
      fun x => ((freq : ℂ) * Complex.I) ^ r * seedWavePhase freq x := by
  let A : ℕ → ℝ → ℂ := fun r x => ((freq : ℂ) * Complex.I) ^ r * seedWavePhase freq x
  have hA : ∀ r x, HasDerivAt (A r) (A (r + 1) x) x := by
    intro r x
    convert! (seedWavePhase_hasDerivAt freq x).const_mul
      (((freq : ℂ) * Complex.I) ^ r) using 1
    simp only [A, pow_succ]
    ring
  have hbase : A 0 = seedWavePhase freq := by funext x; simp [A]
  rw [iteratedDeriv_eq_iterate, ← hbase, ← derivative_family_eq_iterate A hA r]
  funext x
  simp [A]

/-- Exact carrier-modulated jets, with the slowly varying corrections
separated from the zeroth-order amplitude. -/
def seedModulatedJet (A : ℕ → ℝ → ℂ) (freq : ℝ) (r : ℕ) (x : ℝ) : ℂ :=
  seedWavePhase freq x *
    (((freq : ℂ) * Complex.I) ^ r * A 0 x +
      ∑ j ∈ Finset.range r, (r.choose (j + 1) : ℂ) *
        ((freq : ℂ) * Complex.I) ^ (r - (j + 1)) * A (j + 1) x)

private theorem seedModulatedJet_eq_iteratedDeriv (A : ℕ → ℝ → ℂ)
    (hA : ∀ r x, HasDerivAt (A r) (A (r + 1) x) x) (freq : ℝ) (r : ℕ) :
    seedModulatedJet A freq r =
      iteratedDeriv r (fun x => A 0 x * seedWavePhase freq x) := by
  funext x
  have hf : ContDiff ℝ r (A 0) := smooth_derivative_family A hA r 0
  have hg : ContDiff ℝ r (seedWavePhase freq) := by
    have hreal : ContDiff ℝ r (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    unfold seedWavePhase
    fun_prop
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt]
  have hrepr (j : ℕ) : iteratedDeriv j (A 0) x = A j x := by
    rw [iteratedDeriv_eq_iterate, ← derivative_family_eq_iterate A hA j]
  simp_rw [hrepr, seedWavePhase_derivatives]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  rw [add_comm]
  unfold seedModulatedJet
  rw [mul_add, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    ring

theorem seedModulatedJet_hasDerivAt (A : ℕ → ℝ → ℂ)
    (hA : ∀ r x, HasDerivAt (A r) (A (r + 1) x) x)
    (freq : ℝ) (r : ℕ) (x : ℝ) :
    HasDerivAt (seedModulatedJet A freq r) (seedModulatedJet A freq (r + 1) x) x := by
  have hf : ContDiff ℝ (r + 1) (fun x => A 0 x * seedWavePhase freq x) := by
    apply (smooth_derivative_family A hA (r + 1) 0).mul
    have hreal : ContDiff ℝ (r + 1) (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    unfold seedWavePhase
    fun_prop
  rw [seedModulatedJet_eq_iteratedDeriv A hA,
    seedModulatedJet_eq_iteratedDeriv A hA]
  rw [iteratedDeriv_succ]
  exact (hf.differentiable_iteratedDeriv' r x).hasDerivAt

/-- A real two-carrier derivative family. -/
def seedWaveJet (A B : ℕ → ℝ → ℂ) (r : ℕ) (x : ℝ) : ℝ :=
  (seedModulatedJet A 1 r x + seedModulatedJet B 2 r x).re

/-- The leading, frozen-amplitude part of a real jet. -/
def seedWaveLeadingJet (A B : ℕ → ℝ → ℂ) (r : ℕ) (x : ℝ) : ℝ :=
  (seedWavePhase 1 x * Complex.I ^ r * A 0 x +
    seedWavePhase 2 x * ((2 : ℂ) * Complex.I) ^ r * B 0 x).re

private def seedWaveErrorBound (freq : ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, (r.choose (j + 1) : ℝ) *
    |freq| ^ (r - (j + 1)) * (1 / 1024 : ℝ) ^ (j + 1)

theorem seedWaveJet_hasDerivAt (A B : ℕ → ℝ → ℂ)
    (hA : ∀ r x, HasDerivAt (A r) (A (r + 1) x) x)
    (hB : ∀ r x, HasDerivAt (B r) (B (r + 1) x) x) (r : ℕ) (x : ℝ) :
    HasDerivAt (seedWaveJet A B r) (seedWaveJet A B (r + 1) x) x := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    ((seedModulatedJet_hasDerivAt A hA 1 r x).add
      (seedModulatedJet_hasDerivAt B hB 2 r x))
  convert! hd using 1

private theorem seedModulatedJet_remainder_bound (A : ℕ → ℝ → ℂ)
    (hA : ∀ r x, ‖A r x‖ ≤ (1 / 1024 : ℝ) ^ r) (freq : ℝ) (r : ℕ) (x : ℝ) :
    ‖seedModulatedJet A freq r x -
      seedWavePhase freq x * (((freq : ℂ) * Complex.I) ^ r * A 0 x)‖ ≤
      seedWaveErrorBound freq r := by
  unfold seedModulatedJet
  rw [mul_add, add_sub_cancel_left, norm_mul, seedWavePhase_norm, one_mul]
  unfold seedWaveErrorBound
  apply norm_sum_le_of_le
  intro j hj
  simp only [norm_mul, norm_pow, norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one]
  exact mul_le_mul_of_nonneg_left (hA (j + 1) x) (by positivity)

/-- Freezing the slowly varying blocks changes any of the first five jets
by less than one eighth. -/
theorem seedWaveJet_error_lt (A B : ℕ → ℝ → ℂ)
    (hA : ∀ r x, ‖A r x‖ ≤ (1 / 1024 : ℝ) ^ r)
    (hB : ∀ r x, ‖B r x‖ ≤ (1 / 1024 : ℝ) ^ r)
    {r : ℕ} (hr : r ≤ 4) (x : ℝ) :
    |seedWaveJet A B r x - seedWaveLeadingJet A B r x| < 1 / 8 := by
  let a := seedWavePhase 1 x * (Complex.I ^ r * A 0 x)
  let b := seedWavePhase 2 x * (((2 : ℂ) * Complex.I) ^ r * B 0 x)
  have he : seedWaveJet A B r x - seedWaveLeadingJet A B r x =
      ((seedModulatedJet A 1 r x - a) + (seedModulatedJet B 2 r x - b)).re := by
    simp only [seedWaveJet, seedWaveLeadingJet, Complex.add_re, Complex.sub_re]
    dsimp [a, b]
    simp only [mul_assoc]
    ring
  rw [he]
  calc
    _ ≤ ‖(seedModulatedJet A 1 r x - a) + (seedModulatedJet B 2 r x - b)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖seedModulatedJet A 1 r x - a‖ + ‖seedModulatedJet B 2 r x - b‖ := norm_add_le _ _
    _ ≤ seedWaveErrorBound 1 r + seedWaveErrorBound 2 r :=
      add_le_add (by simpa only [a, Complex.ofReal_one, one_mul] using
        seedModulatedJet_remainder_bound A hA 1 r x)
        (seedModulatedJet_remainder_bound B hB 2 r x)
    _ < 1 / 8 := by
      interval_cases r <;> norm_num [seedWaveErrorBound, Finset.sum_range_succ, Nat.choose]

/-- A uniform bound for each of the first five real derivatives. -/
theorem seedWaveJet_bound (A B : ℕ → ℝ → ℂ)
    (hA : ∀ r x, ‖A r x‖ ≤ (1 / 1024 : ℝ) ^ r)
    (hB : ∀ r x, ‖B r x‖ ≤ (1 / 1024 : ℝ) ^ r)
    {r : ℕ} (hr : r ≤ 4) (x : ℝ) :
    |seedWaveJet A B r x| ≤ (2 : ℝ) ^ r + 2 := by
  have ha : ‖A 0 x‖ ≤ 1 := by simpa using hA 0 x
  have hb : ‖B 0 x‖ ≤ 1 := by simpa using hB 0 x
  have hleading : |seedWaveLeadingJet A B r x| ≤ 1 + (2 : ℝ) ^ r := by
    apply (Complex.abs_re_le_norm _).trans
    apply (norm_add_le _ _).trans
    have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    simp only [norm_mul, norm_pow, seedWavePhase_norm, Complex.norm_I,
      htwo, one_mul, one_pow, mul_one]
    exact add_le_add ha (mul_le_of_le_one_right (by positivity) hb)
  have he := seedWaveJet_error_lt A B hA hB hr x
  have ht := abs_add_le (seedWaveJet A B r x - seedWaveLeadingJet A B r x)
    (seedWaveLeadingJet A B r x)
  rw [sub_add_cancel] at ht
  linarith

/-- Joint squared norm one prevents all four low-order real jets from
being small simultaneously. -/
theorem seedWaveJet_nondegenerate (A B : ℕ → ℝ → ℂ)
    (hA : ∀ r x, ‖A r x‖ ≤ (1 / 1024 : ℝ) ^ r)
    (hB : ∀ r x, ‖B r x‖ ≤ (1 / 1024 : ℝ) ^ r)
    (hnorm : ∀ x, Complex.normSq (A 0 x) + Complex.normSq (B 0 x) = 1) (x : ℝ) :
    ∃ r : Fin 4, 1 / 4 ≤ |seedWaveJet A B r.val x| := by
  let a := seedWavePhase 1 x * A 0 x
  let b := seedWavePhase 2 x * B 0 x
  have hab : Complex.normSq a + Complex.normSq b = 1 := by
    simp only [a, b, ← Complex.sq_norm, norm_mul, seedWavePhase_norm, one_mul]
    simpa only [← Complex.sq_norm] using hnorm x
  have he0 : seedWaveLeadingJet A B 0 x = (a + b).re := by
    simp [seedWaveLeadingJet, a, b]
  have he1 : seedWaveLeadingJet A B 1 x =
      (Complex.I * a + (2 * Complex.I) * b).re := by
    apply congrArg Complex.re
    dsimp [seedWaveLeadingJet, a, b]
    ring
  have he2 : seedWaveLeadingJet A B 2 x = (-a - 4 * b).re := by
    apply congrArg Complex.re
    dsimp [seedWaveLeadingJet, a, b]
    ring_nf
    simp only [Complex.I_sq]
    ring
  have he3 : seedWaveLeadingJet A B 3 x =
      (-Complex.I * a - (8 * Complex.I) * b).re := by
    apply congrArg Complex.re
    dsimp [seedWaveLeadingJet, a, b]
    ring_nf
    norm_num [pow_succ, Complex.I_sq]
    ring
  apply seed_two_frequency_jet_separation a b hab (fun r => seedWaveJet A B r.val x)
  · simpa [he0] using seedWaveJet_error_lt A B hA hB (by norm_num : 0 ≤ 4) x
  · simpa [he1] using seedWaveJet_error_lt A B hA hB (by norm_num : 1 ≤ 4) x
  · simpa [he2] using seedWaveJet_error_lt A B hA hB (by norm_num : 2 ≤ 4) x
  · simpa [he3] using seedWaveJet_error_lt A B hA hB (by norm_num : 3 ≤ 4) x

/-- Normalized slowly varying first Rudin--Shapiro block and all its
rescaled angular derivatives. -/
def rudinShapiroSlowP (k r : ℕ) (x : ℝ) : ℂ :=
  rsScaledDerivative (2 ^ k) (rsCenteredPolynomial (2 ^ k) (rudinShapiroP k))
    (1 / (2 : ℝ) ^ (k + 10)) r x / (Real.sqrt ((2 : ℝ) ^ (k + 1)) : ℂ)

/-- The corresponding normalized second block. -/
def rudinShapiroSlowQ (k r : ℕ) (x : ℝ) : ℂ :=
  rsScaledDerivative (2 ^ k) (rsCenteredPolynomial (2 ^ k) (rudinShapiroQ k))
    (1 / (2 : ℝ) ^ (k + 10)) r x / (Real.sqrt ((2 : ℝ) ^ (k + 1)) : ℂ)

theorem rudinShapiroSlowP_hasDerivAt (k r : ℕ) (x : ℝ) :
    HasDerivAt (rudinShapiroSlowP k r) (rudinShapiroSlowP k (r + 1) x) x := by
  exact (rsScaledDerivative_hasDerivAt _ _ _ r x).div_const _

theorem rudinShapiroSlowQ_hasDerivAt (k r : ℕ) (x : ℝ) :
    HasDerivAt (rudinShapiroSlowQ k r) (rudinShapiroSlowQ k (r + 1) x) x := by
  exact (rsScaledDerivative_hasDerivAt _ _ _ r x).div_const _

theorem rudinShapiroSlow_bounds (k r : ℕ) (x : ℝ) :
    ‖rudinShapiroSlowP k r x‖ ≤ (1 / 1024 : ℝ) ^ r ∧
    ‖rudinShapiroSlowQ k r x‖ ≤ (1 / 1024 : ℝ) ^ r := by
  simpa only [rudinShapiroSlowP, rudinShapiroSlowQ, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
      rudinShapiro_slow_block_bounds k r x

theorem rudinShapiroSlow_norm_identity (k : ℕ) (x : ℝ) :
    Complex.normSq (rudinShapiroSlowP k 0 x) +
      Complex.normSq (rudinShapiroSlowQ k 0 x) = 1 := by
  have hident := rudinShapiro_norm_identity k
    (z := Complex.exp ((((1 / (2 : ℝ) ^ (k + 10)) * x : ℝ) : ℂ) * Complex.I))
    (by simpa only [seedWavePhase, Complex.ofReal_one, one_mul] using
      seedWavePhase_norm 1 ((1 / (2 : ℝ) ^ (k + 10)) * x))
  have hscaled :
      ‖rsScaledDerivative (2 ^ k) (rsCenteredPolynomial (2 ^ k) (rudinShapiroP k))
        (1 / (2 : ℝ) ^ (k + 10)) 0 x‖ ^ 2 +
      ‖rsScaledDerivative (2 ^ k) (rsCenteredPolynomial (2 ^ k) (rudinShapiroQ k))
        (1 / (2 : ℝ) ^ (k + 10)) 0 x‖ ^ 2 = (2 : ℝ) ^ (k + 1) := by
    simpa only [rsScaledDerivative, pow_zero, one_mul, Function.iterate_zero_apply,
      rsCenteredPolynomial_eval] using hident
  simp only [rudinShapiroSlowP, rudinShapiroSlowQ, ← Complex.sq_norm, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow]
  rw [← add_div, hscaled, Real.sq_sqrt (by positivity)]
  exact div_self (by positivity)

/-- The normalized two-frequency Rudin--Shapiro real wave, with its exact
derivative family. -/
def rudinShapiroWave (k r : ℕ) (x : ℝ) : ℝ :=
  seedWaveJet (rudinShapiroSlowP k) (rudinShapiroSlowQ k) r x

theorem rudinShapiroWave_hasDerivAt (k r : ℕ) (x : ℝ) :
    HasDerivAt (rudinShapiroWave k r) (rudinShapiroWave k (r + 1) x) x :=
  seedWaveJet_hasDerivAt _ _ (rudinShapiroSlowP_hasDerivAt k)
    (rudinShapiroSlowQ_hasDerivAt k) r x

theorem rudinShapiroWave_bound (k : ℕ) {r : ℕ} (hr : r ≤ 4) (x : ℝ) :
    |rudinShapiroWave k r x| ≤ (2 : ℝ) ^ r + 2 :=
  seedWaveJet_bound _ _ (fun r x => (rudinShapiroSlow_bounds k r x).1)
    (fun r x => (rudinShapiroSlow_bounds k r x).2) hr x

theorem rudinShapiroWave_nondegenerate (k : ℕ) (x : ℝ) :
    ∃ r : Fin 4, 1 / 4 ≤ |rudinShapiroWave k r.val x| :=
  seedWaveJet_nondegenerate _ _ (fun r x => (rudinShapiroSlow_bounds k r x).1)
    (fun r x => (rudinShapiroSlow_bounds k r x).2) (rudinShapiroSlow_norm_identity k) x

/-- Seven-cell exclusion now applies to the actual Rudin--Shapiro wave
without an analytic nondegeneracy premise. -/
theorem rudinShapiroWave_seven_cells_unmarked (k : ℕ) {a b : ℝ}
    (ha : 0 < a) (haMax : a ≤ 1 / 2048) :
    ∃ i : Fin 7, ∀ x ∈ Set.Icc (b + (i.val : ℝ) * a)
      (b + ((i.val : ℝ) + 1) * a), a ^ 3 / 128 < |rudinShapiroWave k 0 x| :=
  seed_seven_cells_unmarked (rudinShapiroWave k) (rudinShapiroWave_hasDerivAt k)
    (rudinShapiroWave_nondegenerate k) (fun _ hr x => rudinShapiroWave_bound k hr x)
    ha haMax

/-- Zeroth jet in the original circle-evaluation notation. -/
theorem rudinShapiroWave_zero (k : ℕ) (x : ℝ) :
    rudinShapiroWave k 0 x =
      (seedWavePhase 1 x * rsEval (rudinShapiroP k)
          (Complex.exp ((((1 / (2 : ℝ) ^ (k + 10)) * x : ℝ) : ℂ) * Complex.I)) +
        seedWavePhase 2 x * rsEval (rudinShapiroQ k)
          (Complex.exp ((((1 / (2 : ℝ) ^ (k + 10)) * x : ℝ) : ℂ) * Complex.I))).re /
        Real.sqrt ((2 : ℝ) ^ (k + 1)) := by
  simp only [rudinShapiroWave, seedWaveJet, seedModulatedJet, Finset.range_zero,
    Finset.sum_empty, pow_zero, one_mul, add_zero,
    rudinShapiroSlowP, rudinShapiroSlowQ, rsScaledDerivative,
    Function.iterate_zero_apply, rsCenteredPolynomial_eval, ← mul_div_assoc,
    ← add_div, Complex.div_ofReal_re]

/-- The normalized odd-stage wave equals one at the zero axis. -/
theorem rudinShapiroWave_odd_zero_axis (m : ℕ) :
    rudinShapiroWave (2 * m + 1) 0 0 = 1 := by
  rw [rudinShapiroWave_zero]
  have hs : Real.sqrt ((2 : ℝ) ^ (2 * m + 1 + 1)) = (2 : ℝ) ^ (m + 1) := by
    rw [show 2 * m + 1 + 1 = (m + 1) * 2 by omega, pow_mul,
      Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
  simp only [seedWavePhase, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
    one_mul, (rudinShapiro_odd_endpoints m).1, (rudinShapiro_odd_endpoints m).2.1,
    add_zero, hs]
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact div_self (by positivity : (2 : ℝ) ^ (m + 1) ≠ 0)

/-- The odd-stage wave avoids the small-value threshold in the full
101-cell neighborhood of the zero axis. -/
theorem rudinShapiroWave_zero_axis_clearance (m : ℕ) {x a : ℝ}
    (haMax : a ≤ 1 / 2048) (hnear : |x| ≤ 101 * a) :
    1 / 2 < |rudinShapiroWave (2 * m + 1) 0 x| := by
  apply seed_axis_clearance (rudinShapiroWave_hasDerivAt (2 * m + 1) 0)
    (fun x => by
      have hb := rudinShapiroWave_bound (2 * m + 1) (by norm_num : 1 ≤ 4) x
      norm_num at hb
      exact hb)
    (rudinShapiroWave_odd_zero_axis m) haMax
  simpa using hnear

end
end Power2ModuleSVP
