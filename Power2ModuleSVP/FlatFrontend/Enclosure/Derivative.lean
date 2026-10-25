import Power2ModuleSVP.FlatFrontend.Preparation

/-!
# Derivative

Entrywise derivative enclosures, reduced to scalar rational remainders.
The normalization factor never amplifies the Taylor/Machin error.

Paper: `paper/power2svp.pdf`, Appendix A.3 (rational enclosures and the two rounding steps).
-/
namespace Power2ModuleSVP
namespace FlatFrontend

/-- The rational multiple of pi used by an actual derivative entry. -/
def derivativePhase (N k j : ℕ) : ℚ :=
  (((2 * j + 1) * (2 * k + 1) : ℕ) : ℚ) / (64 * (N : ℚ))

theorem derivativePhase_nonnegative (N k j : ℕ) : 0 ≤ derivativePhase N k j := by
  unfold derivativePhase
  positivity

theorem derivativePhase_le {N : ℕ} (k : Fin (16 * N)) (j : Fin N) :
    derivativePhase N k j ≤ N := by
  have hn : (0 : ℚ) < N := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hj : (j.val : ℚ) + 1 ≤ N := by exact_mod_cast j.isLt
  have hk : (k.val : ℚ) + 1 ≤ 16 * N := by exact_mod_cast k.isLt
  unfold derivativePhase
  push_cast
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 64 * N)).mpr
  nlinarith [mul_nonneg (by positivity : (0 : ℚ) ≤ 2 * j.val + 1)
    (by linarith : (0 : ℚ) ≤ 32 * N - (2 * k.val + 1))]

/-- Exact identification with the phase-shifted Taylor routine. -/
theorem derivativeEntry_eq_phaseTaylor (N k ell j : ℕ) :
    derivativeEntry N k ell j =
      (((2 * j + 1 : ℕ) : ℚ) / (2 * N : ℕ)) ^ ell *
        phaseTaylor ell (taylorOrder N) (derivativePhase N k j * piTaylor (precision N)) := by
  unfold derivativeEntry phaseTaylor derivativePhase sinTaylor cosTaylor
  push_cast
  ring

/-- This bound holds for every order, including orders above the frontend's
row range. The only side condition is the rational Taylor ratio test. -/
theorem derivativeEntry_error {N : ℕ} (k : Fin (16 * N)) (ell : ℕ) (j : Fin N)
    (h : |derivativePhase N k j * piTaylor (precision N)| /
      (taylorOrder N + 1 : ℚ) ≤ 1 / 2) :
    |derivativeRow N k ell j - (derivativeEntry N k ell j : ℝ)| ≤
      (derivativePhase N k j * piError (precision N) +
        taylorError (taylorOrder N) (derivativePhase N k j * piTaylor (precision N)) : ℚ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hj : (j.val : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
  have ha : 0 ≤ (2 * (j : ℝ) + 1) / (2 * N : ℝ) := by positivity
  have hb : (2 * (j : ℝ) + 1) / (2 * N : ℝ) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have hp := phaseTaylor_pi_error ell (taylorOrder N) (precision N)
    (derivativePhase N k j) h
  rw [abs_of_nonneg (derivativePhase_nonnegative _ _ _)] at hp
  have he : (2 * (j : ℝ) + 1) * seedDerivativeAngle N k =
      (derivativePhase N k j : ℝ) * Real.pi := by
    simp only [seedDerivativeAngle, derivativePhase, Rat.cast_div,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    push_cast
    ring
  rw [derivativeEntry_eq_phaseTaylor]
  unfold derivativeRow
  push_cast
  rw [he, ← mul_sub, abs_mul, abs_pow, abs_of_nonneg ha]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ha hb) (abs_nonneg _)).trans
    (by simpa only [one_mul, Rat.cast_add, Rat.cast_mul] using hp)

/-- A scalar, rational-only precision obligation. No real derivative or
coloring conclusion is included in this contract. -/
structure DerivativeRemainderBound (N : ℕ) : Prop where
  ratio : ∀ k : Fin (16 * N), ∀ j : Fin N,
    |derivativePhase N k j * piTaylor (precision N)| /
      (taylorOrder N + 1 : ℚ) ≤ 1 / 2
  remainder : ∀ k : Fin (16 * N), ∀ j : Fin N,
    derivativePhase N k j * piError (precision N) +
      taylorError (taylorOrder N) (derivativePhase N k j * piTaylor (precision N)) ≤
        seedRoundingError N

theorem derivative_error_of_remainder {N : ℕ} (h : DerivativeRemainderBound N)
    (k : Fin (16 * N)) (ell : ℕ) (j : Fin N) :
    |derivativeRow N k ell j - (derivativeEntry N k ell j : ℝ)| ≤
      (seedRoundingError N : ℝ) := by
  exact (derivativeEntry_error k ell j (h.ratio k j)).trans
    (by exact_mod_cast h.remainder k j)

end FlatFrontend
end Power2ModuleSVP
