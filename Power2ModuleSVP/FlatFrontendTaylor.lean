import Power2ModuleSVP.FlatFrontendParameters
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-! Rational Taylor programs with explicit truncation orders. The certified
factorial remainder is independent of a precision-selection policy. -/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

def phase : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => (-(phase n).2, (phase n).1)

def expTaylor : ℕ → ℚ → ℚ × ℚ
  | 0, _ => (0, 0)
  | n + 1, q =>
    let p := expTaylor n q
    let a := q ^ n / (n.factorial : ℚ)
    (p.1 + a * (phase n).1, p.2 + a * (phase n).2)

def cosTaylor (n : ℕ) (q : ℚ) : ℚ := (expTaylor n q).1
def sinTaylor (n : ℕ) (q : ℚ) : ℚ := (expTaylor n q).2

def taylorError (n : ℕ) (q : ℚ) : ℚ := 2 * |q| ^ n / (n.factorial : ℚ)

theorem phase_cast (n : ℕ) :
    ((phase n).1 : ℂ) + ((phase n).2 : ℂ) * Complex.I = Complex.I ^ n := by
  induction n with
  | zero => simp [phase]
  | succ n ih =>
    simp only [phase, Rat.cast_neg, pow_succ]
    rw [← ih]
    ring_nf
    simp [Complex.I_sq]

theorem expTaylor_cast (n : ℕ) (q : ℚ) :
    ((cosTaylor n q : ℚ) : ℂ) + ((sinTaylor n q : ℚ) : ℂ) * Complex.I =
      ∑ k ∈ Finset.range n, ((q : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) := by
  induction n with
  | zero => simp [cosTaylor, sinTaylor, expTaylor]
  | succ n ih =>
    simp only [cosTaylor, sinTaylor, expTaylor, Rat.cast_add, Rat.cast_mul,
      Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Finset.sum_range_succ, mul_pow]
    change ((cosTaylor n q : ℚ) : ℂ) + _ +
      (((sinTaylor n q : ℚ) : ℂ) + _) * Complex.I = _
    calc
      _ = (((cosTaylor n q : ℚ) : ℂ) + ((sinTaylor n q : ℚ) : ℂ) * Complex.I) +
          ((q : ℂ) ^ n / (n.factorial : ℂ)) *
            (((phase n).1 : ℂ) + ((phase n).2 : ℂ) * Complex.I) := by ring
      _ = (∑ k ∈ Finset.range n, (q : ℂ) ^ k * Complex.I ^ k / (k.factorial : ℂ)) +
          (q : ℂ) ^ n * Complex.I ^ n / (n.factorial : ℂ) := by
        simp only [mul_pow] at ih
        rw [ih, phase_cast]
        ring

theorem taylorError_nonnegative (n : ℕ) (q : ℚ) : 0 ≤ taylorError n q := by
  unfold taylorError
  positivity

/-- Both coordinates of the same rational computation have a certified
remainder. The test on the order is an entirely rational comparison. -/
theorem sin_cos_taylor_error {n : ℕ} {q : ℚ}
    (h : |q| / (n + 1 : ℚ) ≤ 1 / 2) :
    |Real.cos (q : ℝ) - (cosTaylor n q : ℝ)| ≤ (taylorError n q : ℝ) ∧
    |Real.sin (q : ℝ) - (sinTaylor n q : ℝ)| ≤ (taylorError n q : ℝ) := by
  have hn : ‖(q : ℂ) * Complex.I‖ = |(q : ℝ)| := by simp
  have hh : ‖(q : ℂ) * Complex.I‖ / (n + 1 : ℝ) ≤ 1 / 2 := by
    rw [hn]
    have hc := (Rat.cast_le (K := ℝ)).mpr h
    simpa using hc
  have he := Complex.exp_bound' (x := (q : ℂ) * Complex.I) (n := n)
    (by simpa using hh)
  rw [← expTaylor_cast, hn] at he
  have hr := (Complex.abs_re_le_norm _).trans he
  have hi := (Complex.abs_im_le_norm _).trans he
  have hc : (Complex.exp ((q : ℂ) * Complex.I)).re = Real.cos (q : ℝ) := by
    simp [Complex.exp_re]
  have hs : (Complex.exp ((q : ℂ) * Complex.I)).im = Real.sin (q : ℝ) := by
    simp [Complex.exp_im]
  have heq : (taylorError n q : ℝ) = |(q : ℝ)| ^ n / (n.factorial : ℝ) * 2 := by
    simp only [taylorError, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_abs, Rat.cast_natCast]
    ring
  rw [heq]
  constructor
  · simpa [hc] using hr
  · simpa [hs] using hi

def arctanTaylor (n : ℕ) (q : ℚ) : ℚ :=
  ((List.range n).map fun k => (-1 : ℚ) ^ k * q ^ (2 * k + 1) /
    ((2 * k + 1 : ℕ) : ℚ)).sum

def piTaylor (n : ℕ) : ℚ :=
  16 * arctanTaylor n (1 / 5) - 4 * arctanTaylor n (1 / 239)

def arctanError (n : ℕ) (q : ℚ) : ℚ := |q| ^ (2 * n + 1) / (1 - |q| ^ 2)

theorem arctan_taylor_error {q : ℚ} (hq : |q| < 1) (n : ℕ) :
    |Real.arctan (q : ℝ) - (arctanTaylor n q : ℝ)| ≤ (arctanError n q : ℝ) := by
  let x : ℝ := q
  let f := fun k : ℕ => (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (2 * k + 1 : ℕ)
  have hx : |x| < 1 := by
    dsimp [x]
    exact_mod_cast hq
  have hsq : ‖|x| ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg x]
  have hf : HasSum f (Real.arctan x) := Real.hasSum_arctan (by simpa using hx)
  have hg := (hasSum_geometric_of_norm_lt_one hsq).mul_left (|x| ^ (2 * n + 1))
  have hterm (k : ℕ) : |f (k + n)| ≤ |x| ^ (2 * n + 1) * (|x| ^ 2) ^ k := by
    dsimp [f]
    simp only [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      Nat.abs_cast]
    have hden : (1 : ℝ) ≤ (2 * (k + n) + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ 2 * (k + n) + 1 by omega)
    calc
      _ ≤ |x| ^ (2 * (k + n) + 1) := div_le_self (by positivity) hden
      _ = |x| ^ (2 * n + 1) * (|x| ^ 2) ^ k := by
        rw [show 2 * (k + n) + 1 = (2 * n + 1) + 2 * k by omega, pow_add, pow_mul]
  have hnorm : Summable (fun k => ‖f (k + n)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hg.summable
    intro k
    simpa only [Real.norm_eq_abs] using hterm k
  have htail : Real.arctan x - ∑ k ∈ Finset.range n, f k = ∑' k, f (k + n) := by
    have he := Summable.sum_add_tsum_nat_add n hf.summable
    rw [hf.tsum_eq] at he
    linarith
  have hb := (norm_tsum_le_tsum_norm hnorm).trans
    (hnorm.tsum_le_tsum (fun k => by simpa only [Real.norm_eq_abs] using hterm k) hg.summable)
  rw [hg.tsum_eq, Real.norm_eq_abs] at hb
  have hsum : (arctanTaylor n q : ℝ) = ∑ k ∈ Finset.range n, f k := by
    rw [arctanTaylor, list_sum_range]
    simp [f, x]
  rw [hsum, htail]
  simpa [arctanError, x, div_eq_mul_inv] using hb

def piError (n : ℕ) : ℚ :=
  16 * arctanError n (1 / 5) + 4 * arctanError n (1 / 239)

theorem pi_taylor_error (n : ℕ) : |Real.pi - (piTaylor n : ℝ)| ≤ (piError n : ℝ) := by
  have ha := arctan_taylor_error (q := 1 / 5) (by norm_num) n
  have hb := arctan_taylor_error (q := 1 / 239) (by norm_num) n
  have hp := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hpi : Real.pi = 16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) := by
    norm_num [inv_eq_one_div] at hp
    linarith
  rw [hpi]
  simp only [piTaylor, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
  have he : 16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) -
      (16 * (arctanTaylor n (1 / 5) : ℝ) - 4 * (arctanTaylor n (1 / 239) : ℝ)) =
      16 * (Real.arctan (1 / 5) - (arctanTaylor n (1 / 5) : ℝ)) -
        4 * (Real.arctan (1 / 239) - (arctanTaylor n (1 / 239) : ℝ)) := by ring
  rw [he]
  apply (abs_sub _ _).trans
  simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16),
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have ha' := mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 16)
  have hb' := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 4)
  simpa [piError] using add_le_add ha' hb'

end FlatFrontend
end Power2ModuleSVP
