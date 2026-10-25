import Power2ModuleSVP.FlatFrontend.Coefficients
import Power2ModuleSVP.FlatFrontend.Program
import Power2ModuleSVP.Seed.Chebyshev.Trig
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Derivatives

Exact odd sine jets and normalized derivative rows. No rational
enclosure is inferred from a real-valued choice in this module.

Paper: `paper/power2svp.pdf`, Appendix A.3 (rational enclosures and the two rounding steps).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators
noncomputable section

theorem phase_cases (ell : ℕ) : phase ell = (1, 0) ∨ phase ell = (0, 1) ∨
    phase ell = (-1, 0) ∨ phase ell = (0, -1) := by
  induction ell with
  | zero => exact Or.inl rfl
  | succ ell ih =>
    rcases ih with h | h | h | h <;> simp [phase, h]

/-- The derivative phase of sine, cycling through sine, cosine, and their negatives. -/
def jetSin (ell : ℕ) (x : ℝ) : ℝ :=
  ((phase ell).1 : ℝ) * Real.sin x + ((phase ell).2 : ℝ) * Real.cos x

theorem jetSin_bound (ell : ℕ) (x : ℝ) : |jetSin ell x| ≤ 1 := by
  rcases phase_cases ell with h | h | h | h <;>
    first
    | simpa [jetSin, h] using Real.abs_sin_le_one x
    | simpa [jetSin, h] using Real.abs_cos_le_one x

/-- A sine sum supported on the first `N` positive odd frequencies. -/
def oddSineSum {N : ℕ} (a : Fin N → ℝ) (θ : ℝ) : ℝ :=
  ∑ j, a j * Real.sin ((2 * (j : ℝ) + 1) * θ)

/-- The explicit derivative of order `ell` of the odd sine sum. -/
def oddSineJet {N : ℕ} (a : Fin N → ℝ) (ell : ℕ) (θ : ℝ) : ℝ :=
  ∑ j, a j * (2 * (j : ℝ) + 1) ^ ell * jetSin ell ((2 * (j : ℝ) + 1) * θ)

theorem oddPart_eq {N : ℕ} (y : Fin N → ℚ) :
    oddPart y = oddSineSum (fun j => (y j : ℝ)) := by
  funext θ
  unfold oddPart oddSineSum
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [List.getD_eq_getElem?_getD]

theorem oddSineJet_zero {N : ℕ} (a : Fin N → ℝ) : oddSineJet a 0 = oddSineSum a := by
  funext θ
  simp [oddSineJet, oddSineSum, jetSin, phase]

theorem oddSineJet_hasDerivAt {N : ℕ} (a : Fin N → ℝ) (ell : ℕ) (θ : ℝ) :
    HasDerivAt (oddSineJet a ell) (oddSineJet a (ell + 1) θ) θ := by
  have hterm (j : Fin N) : HasDerivAt
      (fun x => a j * (2 * (j : ℝ) + 1) ^ ell * jetSin ell ((2 * (j : ℝ) + 1) * x))
      (a j * (2 * (j : ℝ) + 1) ^ (ell + 1) * jetSin (ell + 1)
        ((2 * (j : ℝ) + 1) * θ)) θ := by
    let m : ℝ := 2 * (j : ℝ) + 1
    have hs := (Real.hasDerivAt_sin (m * θ)).comp θ ((hasDerivAt_id θ).const_mul m)
    have hc := (Real.hasDerivAt_cos (m * θ)).comp θ ((hasDerivAt_id θ).const_mul m)
    have hh := ((hs.const_mul ((phase ell).1 : ℝ)).add
      (hc.const_mul ((phase ell).2 : ℝ))).const_mul (a j * m ^ ell)
    convert hh using 1
    · rfl
    · change a j * m ^ (ell + 1) * jetSin (ell + 1) (m * θ) = _
      simp only [jetSin, phase, Rat.cast_neg, pow_succ]
      ring
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j)

theorem oddSineJet_eq_iterate {N : ℕ} (a : Fin N → ℝ) (ell : ℕ) :
    oddSineJet a ell = deriv^[ell] (oddSineSum a) := by
  induction ell with
  | zero => exact oddSineJet_zero a
  | succ ell ih =>
    rw [Function.iterate_succ_apply', ← ih]
    exact funext fun θ => (oddSineJet_hasDerivAt a ell θ).deriv.symm

theorem oddSineSum_sub {N : ℕ} (a b : Fin N → ℝ) :
    (fun θ => oddSineSum a θ - oddSineSum b θ) = oddSineSum (fun j => a j - b j) := by
  funext θ
  simp [oddSineSum, sub_mul, Finset.sum_sub_distrib]

/-- A normalized row of odd sine derivatives at a seed sampling angle. -/
def derivativeRow (N k ell : ℕ) (j : Fin N) : ℝ :=
  ((2 * (j : ℝ) + 1) / (2 * N : ℝ)) ^ ell *
    jetSin ell ((2 * (j : ℝ) + 1) * seedDerivativeAngle N k)

theorem derivativeRow_bound {N : ℕ} (hN : 0 < N) (k ell : ℕ) (j : Fin N) :
    |derivativeRow N k ell j| ≤ 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hj : (j : ℝ) < N := by exact_mod_cast j.isLt
  have hratio : (2 * (j : ℝ) + 1) / (2 * N : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have hj' : (j.val : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
    linarith
  unfold derivativeRow
  rw [abs_mul, abs_pow, abs_of_nonneg (by positivity :
    0 ≤ (2 * (j : ℝ) + 1) / (2 * N : ℝ))]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (by positivity) hratio)
    (abs_nonneg _)).trans (by simpa using (jetSin_bound ell
      ((2 * (j : ℝ) + 1) * seedDerivativeAngle N k)))

theorem derivativeRow_identity {N : ℕ} (hN : 0 < N)
    (a b : Fin N → ℝ) (k ell : ℕ) :
    (deriv^[ell] (fun θ => oddSineSum a θ - oddSineSum b θ)) (seedDerivativeAngle N k) =
      (2 * (N : ℝ)) ^ ell * ∑ j, derivativeRow N k ell j * (a j - b j) := by
  rw [oddSineSum_sub, ← oddSineJet_eq_iterate]
  unfold oddSineJet derivativeRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hn : (2 * (N : ℝ)) ^ ell ≠ 0 := by positivity
  rw [div_pow]
  field_simp

theorem oddSineSum_bound {N : ℕ} {a : Fin N → ℝ} {M : ℝ}
    (ha : ∀ j, |a j| ≤ M) (θ : ℝ) : |oddSineSum a θ| ≤ N * M := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _j : Fin N, M := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans
        (by simpa using ha j)
    _ = _ := by simp

theorem oddSineSum_degree {N : ℕ} (a : Fin N → ℝ) :
    HasTrigDegree (2 * N) (oddSineSum a) := by
  let P : Polynomial ℂ := ∑ j : Fin N, centeredTrigMode (2 * N) (2 * j + 1) 0 (a j)
  have hdeg : P.degree ≤ (2 * (2 * N) : ℕ) := by
    apply (Polynomial.degree_sum_le _ _).trans
    exact Finset.sup_le fun j _ => centeredTrigMode_degree (2 * N) (2 * j + 1) 0 (a j)
      (by omega)
  refine ⟨P, hdeg, ?_⟩
  intro θ
  have he : laurentTrig (2 * N) P θ =
      ∑ j : Fin N, ((a j * Real.sin ((2 * (j : ℝ) + 1) * θ) : ℝ) : ℂ) := by
    simp only [P, laurentTrig, Polynomial.eval_finsetSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simpa [laurentTrig] using centeredTrigMode_eval (2 * N) (2 * j + 1) 0 (a j) θ
      (by omega)
  simpa only [oddSineSum, Complex.ofReal_sum] using he.symm

@[simp] theorem oddSineSum_neg {N : ℕ} (a : Fin N → ℝ) (θ : ℝ) :
    oddSineSum a (-θ) = -oddSineSum a θ := by
  simp [oddSineSum, mul_neg, Real.sin_neg, Finset.sum_neg_distrib]

@[simp] theorem oddSineSum_add_pi {N : ℕ} (a : Fin N → ℝ) (θ : ℝ) :
    oddSineSum a (θ + Real.pi) = -oddSineSum a θ := by
  simp only [oddSineSum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he : (2 * (j : ℝ) + 1) * (θ + Real.pi) =
      (2 * (j : ℝ) + 1) * θ + (2 * j.val + 1 : ℕ) * Real.pi := by push_cast; ring
  rw [he, Real.sin_add_nat_mul_pi]
  simp [pow_add, pow_mul]

@[simp] theorem oddSineSum_pi_sub {N : ℕ} (a : Fin N → ℝ) (θ : ℝ) :
    oddSineSum a (Real.pi - θ) = oddSineSum a θ := by
  rw [show Real.pi - θ = -θ + Real.pi by ring, oddSineSum_add_pi, oddSineSum_neg, neg_neg]

theorem oddSineSum_abs_periodic {N : ℕ} (a : Fin N → ℝ) :
    Function.Periodic (fun θ => |oddSineSum a θ|) Real.pi := by intro θ; simp

/-- Proof-side reduction to the closed first quadrant. It is never called
by the rational frontend. -/
def foldAngle (θ : ℝ) : ℝ :=
  let r := toIcoMod Real.pi_pos 0 θ
  if r ≤ Real.pi / 2 then r else Real.pi - r

theorem foldAngle_mem (θ : ℝ) : foldAngle θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  have hr := toIcoMod_mem_Ico' Real.pi_pos θ
  dsimp only [foldAngle]
  split_ifs <;> constructor <;> linarith [hr.1, hr.2]

theorem foldAngle_preserves {f : ℝ → ℝ}
    (hp : Function.Periodic (fun θ => |f θ|) Real.pi)
    (hr : ∀ θ, f (Real.pi - θ) = f θ) (θ : ℝ) : |f θ| = |f (foldAngle θ)| := by
  have he : |f (toIcoMod Real.pi_pos 0 θ)| = |f θ| :=
    hp.sub_zsmul_eq (toIcoDiv Real.pi_pos 0 θ)
  dsimp only [foldAngle]
  split_ifs
  · exact he.symm
  · rw [hr]
    exact he.symm

theorem oddSineSum_fold {N : ℕ} (a : Fin N → ℝ) (θ : ℝ) :
    |oddSineSum a θ| = |oddSineSum a (foldAngle θ)| :=
  foldAngle_preserves (oddSineSum_abs_periodic a) (oddSineSum_pi_sub a) θ

end
end FlatFrontend
end Power2ModuleSVP
