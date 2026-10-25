import Power2ModuleSVP.Seed.Specification
import Power2ModuleSVP.Coset.ParityBlock
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Screen

Spectral screening of integral negacyclic multipliers, using the existing
canonical Parseval identity. The estimates concern coefficient squared length.

Paper: `paper/power2svp.pdf`, Section 5 (Theorems 3–4 and deterministic anchor repair).
-/
namespace Power2ModuleSVP
open IdealCVP.Canonical IdealCVP.Cyclotomic

theorem coeffEval_odd_root {d : ℕ} (f : Coeff d) (k : Fin d) :
    coeffEval f (zeta d ^ (2 * k.val + 1)) =
      sigma (fun i => (f i : ℝ)) k := by
  simp [coeffEval, sigma, ← pow_mul]

/-- A convolution row as a single sum, with its wraparound sign explicit. -/
theorem mul_row_formula {d : ℕ} (hd : 0 < d) (f v : Coeff d) (i : Fin d) :
    mul f v i = ∑ j : Fin d,
      (if j.val ≤ i.val then (1 : ℤ) else -1) *
        f ⟨(i.val + d - j.val) % d, Nat.mod_lt _ hd⟩ * v j := by
  classical
  let : NeZero d := ⟨hd.ne'⟩
  unfold mul
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  let k : Fin d := ⟨(i.val + d - j.val) % d, Nat.mod_lt _ hd⟩
  have hkval : k.val = if j.val ≤ i.val then i.val - j.val else i.val + d - j.val := by
    dsimp [k]
    split_ifs with h
    · rw [show i.val + d - j.val = (i.val - j.val) + d by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have hkadd : k + j = i := by
    apply Fin.ext
    simp only [Fin.val_add, hkval]
    split_ifs with h
    · rw [Nat.sub_add_cancel h, Nat.mod_eq_of_lt i.isLt]
    · rw [show i.val + d - j.val + j.val = i.val + d by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  have hc (a : Fin d) : (a.val + j.val) % d = i.val ↔ a = k := by
    constructor
    · intro h
      apply add_right_cancel (b := j)
      exact (Fin.ext h).trans hkadd.symm
    · intro h
      subst a
      exact congrArg Fin.val hkadd
  simp only [hc, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hw : k.val + j.val < d ↔ j.val ≤ i.val := by
    rw [hkval]
    split_ifs <;> omega
  simp only [hw]
  rfl

/-- Parseval turns a rootwise spectral bound into a lower bound on the
coefficient squared norm of every product. -/
theorem spectral_product_sqNorm {d : ℕ} (hd : 0 < d) (f v : Coeff d)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hf : ∀ z : ℂ, z ^ d = -1 → γ * Real.sqrt d ≤ ‖coeffEval f z‖) :
    γ ^ 2 * (d : ℝ) * (IdealCVP.sqNorm v : ℝ) ≤
      (IdealCVP.sqNorm (mul f v) : ℝ) := by
  have hs (k : Fin d) : γ ^ 2 * (d : ℝ) ≤
      ‖sigma (fun i => (f i : ℝ)) k‖ ^ 2 := by
    have hh := hf _ (odd_root hd k)
    rw [coeffEval_odd_root] at hh
    have hh2 := (sq_le_sq₀ (by positivity : 0 ≤ γ * Real.sqrt (d : ℝ))
      (norm_nonneg _)).mpr hh
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)] using hh2
  have hn (a : Coeff d) :
      (∑ k, ‖sigma (fun i => (a i : ℝ)) k‖ ^ 2) =
        (d : ℝ) * (IdealCVP.sqNorm a : ℝ) := by
    simpa only [IdealCVP.sqNorm, Int.cast_sum, Int.cast_pow] using
      norm_identity hd (fun i => (a i : ℝ))
  have hsum : γ ^ 2 * (d : ℝ) * ((d : ℝ) * (IdealCVP.sqNorm v : ℝ)) ≤
      (d : ℝ) * (IdealCVP.sqNorm (mul f v) : ℝ) := by
    rw [← hn v, ← hn (mul f v), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [sigma_mul hd, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (hs k) (sq_nonneg _)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (mul_le_mul_iff_right₀ hdR).mp
  nlinarith only [hsum]

/-- `lem:spectral-screen`: a cube product has a bounded multiplier. -/
theorem spectral_screen {d : ℕ} (hd : 0 < d) (f v : Coeff d)
    {γ : ℝ} (hγ : 0 < γ)
    (hf : ∀ z : ℂ, z ^ d = -1 → γ * Real.sqrt d ≤ ‖coeffEval f z‖)
    (hv : Cube (mul f v)) :
    (IdealCVP.sqNorm v : ℝ) ≤ 1 / γ ^ 2 := by
  have hh := spectral_product_sqNorm hd f v hγ.le hf
  have hc : (IdealCVP.sqNorm (mul f v) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hv.sqNorm_le
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
  apply (mul_le_mul_iff_right₀ hdR).mp
  nlinarith only [hh, hc]

theorem Signs.sub_even {d : ℕ} {f g : Coeff d} (hf : Signs f) (hg : Signs g) :
    EvenCoeffs (f - g) := by
  intro i
  rcases hf i with hf | hf <;> rcases hg i with hg | hg <;>
    simp [Pi.sub_apply, hf, hg]

theorem Signs.shift {d : ℕ} (hd : 0 < d) {f : Coeff d} (hf : Signs f) :
    Signs (shift hd f) := by
  intro i
  by_cases hi : i.val = 0
  · rcases hf ⟨d - 1, by omega⟩ with h | h
    · right; simp [IdealCVP.Cyclotomic.shift, hi, h]
    · left; simp [IdealCVP.Cyclotomic.shift, hi, h]
  · simpa [IdealCVP.Cyclotomic.shift, hi] using hf ⟨i.val - 1, by omega⟩

/-- All product coefficients have the same parity. This statement does not
require a dyadic degree or any nonvanishing assumption. -/
theorem signs_mul_uniform_parity {d : ℕ} (hd : 0 < d) {f : Coeff d}
    (hf : Signs f) (v : Coeff d) (i : Fin d) :
    Even (mul f v i - mul f v ⟨0, hd⟩) := by
  by_cases hd1 : d = 1
  · have hi : i = ⟨0, hd⟩ := Fin.ext (by omega)
    simp [hi]
  have htwo : 1 < d := by omega
  have hshift : mul (shift hd f) v = shift hd (mul f v) := by
    have he (a : Coeff d) : shift hd a = mul (monomial ⟨1, htwo⟩ 1) a := by
      simp [mul_y]
    rw [he f, coeff_mul_assoc hd, ← he]
  have he := even_mul_left (hf.sub_even (hf.shift hd)) v
  rw [coeff_mul_sub_left, hshift] at he
  have hchain : ∀ n (hn : n < d),
      Even (mul f v ⟨n, hn⟩ - mul f v ⟨0, hd⟩) := by
    intro n
    induction n with
    | zero => intro hn; simp
    | succ n ih =>
      intro hn
      have hp := he ⟨n + 1, hn⟩
      change Even (mul f v ⟨n + 1, hn⟩ - shift hd (mul f v) ⟨n + 1, hn⟩) at hp
      simp only [shift, show n + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel] at hp
      convert hp.add (ih (by omega)) using 1
      ring
  exact hchain i.val i.isLt

/-- The parity part of `lem:spectral-screen`, before excluding a zero product. -/
theorem signs_mul_cube_zero_or_signs {d : ℕ} (hd : 0 < d) {f v : Coeff d}
    (hf : Signs f) (hv : Cube (mul f v)) :
    mul f v = 0 ∨ Signs (mul f v) := by
  by_cases hz : mul f v ⟨0, hd⟩ = 0
  · left
    apply even_cube_eq_zero _ hv
    intro i
    simpa [hz] using signs_mul_uniform_parity hd hf v i
  · right
    have hb0 := abs_le.mp (hv ⟨0, hd⟩)
    intro i
    have hb := abs_le.mp (hv i)
    obtain ⟨z, hz'⟩ := signs_mul_uniform_parity hd hf v i
    omega

/-- A nonzero multiplier of a sign word in dyadic degree has a sign product
whenever its product lies in the coefficient cube. -/
theorem signs_mul_cube {d : ℕ} (hd : Dyadic d) {f v : Coeff d}
    (hf : Signs f) (hne : v ≠ 0) (hv : Cube (mul f v)) : Signs (mul f v) := by
  rcases signs_mul_cube_zero_or_signs hd.pos hf hv with hz | hs
  · apply False.elim
    apply hne
    apply mul_injective hd (hf.ne_zero hd.pos)
    simpa using hz
  · exact hs

/-- The finite support used in the bounded multiplier screen. -/
def multiplierSupport {d : ℕ} (v : Coeff d) : Finset (Fin d) :=
  Finset.univ.filter fun i => v i ≠ 0

@[simp] theorem mem_multiplierSupport {d : ℕ} (v : Coeff d) (i : Fin d) :
    i ∈ multiplierSupport v ↔ v i ≠ 0 := by simp [multiplierSupport]

/-- Integral squared length bounds support size. -/
theorem support_card_le_sqNorm {d : ℕ} (v : Coeff d) :
    ((multiplierSupport v).card : ℤ) ≤ IdealCVP.sqNorm v := by
  classical
  calc
    ((multiplierSupport v).card : ℤ) = ∑ _i ∈ multiplierSupport v, (1 : ℤ) := by simp
    _ ≤ ∑ i ∈ multiplierSupport v, v i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hn := (mem_multiplierSupport v i).mp hi
      have hcases : v i ≤ -1 ∨ 1 ≤ v i := by omega
      rcases hcases with h | h <;> nlinarith [sq_nonneg (v i)]
    _ ≤ ∑ i : Fin d, v i ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)

/-- The signed-index-word encoding has length at most squared length. -/
theorem sum_natAbs_le_sqNorm {d : ℕ} (v : Coeff d) :
    ((∑ i, (v i).natAbs : ℕ) : ℤ) ≤ IdealCVP.sqNorm v := by
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Int.natCast_natAbs]
  by_cases hz : v i = 0
  · simp [hz]
  rcases le_total 0 (v i) with hp | hn
  · rw [abs_of_nonneg hp]
    have hh : 1 ≤ v i := by omega
    nlinarith
  · rw [abs_of_nonpos hn]
    have hh : v i ≤ -1 := by omega
    nlinarith

/-- A nonzero multiplier with at most one coefficient, giving a bounded
product by a sign word, must be a signed monomial. -/
theorem signedMonomial_of_support_le_one {d : ℕ} (hd : Dyadic d)
    {f v : Coeff d} (hf : Signs f) (hv : Cube (mul f v))
    (hs : (multiplierSupport v).card ≤ 1) : v = 0 ∨ SignedMonomial v := by
  classical
  by_cases hz : v = 0
  · exact Or.inl hz
  right
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hz (funext h)
  have he : v = (v j) • monomial j 1 := by
    funext i
    by_cases hi : i = j
    · subst i; simp
    have hzi : v i = 0 := by
      by_contra hne
      exact hi ((Finset.card_le_one.mp hs) i (by simpa using hne)
        j (by simpa using hj))
    simp [monomial, hi, hzi]
  have hunit : Signs (mul f (monomial j 1)) := by
    apply signs_mul_cube hd hf
    · intro h
      have hh := congrFun h j
      simp at hh
    · rw [mul_comm]
      exact (cube_monomial_mul_iff j f).mpr hf.cube
  have hb := abs_le.mp (hv ⟨0, hd.pos⟩)
  rw [he, mul_smul_right] at hb
  simp only [Pi.smul_apply, smul_eq_mul] at hb
  have hval : v j = -1 ∨ v j = 1 := by
    rcases hunit ⟨0, hd.pos⟩ with h | h <;> rw [h] at hb <;> omega
  refine ⟨j, ?_⟩
  rcases hval with h | h
  · right; simpa [h] using he
  · left; simpa [h] using he

/-- Spectral screening reduces rigidity to excluding the finitely supported,
bounded squared-length multipliers with at least two nonzero coefficients. -/
theorem rigid_of_candidate_exclusion {d C : ℕ} (hd : Dyadic d)
    {f : Coeff d} (hf : Signs f)
    (hscreen : ∀ v : Coeff d, Cube (mul f v) → IdealCVP.sqNorm v ≤ (C : ℤ))
    (hexclude : ∀ v : Coeff d, 2 ≤ (multiplierSupport v).card →
      IdealCVP.sqNorm v ≤ (C : ℤ) → ¬ Signs (mul f v)) : Rigid f := by
  intro v hv
  by_cases hs : (multiplierSupport v).card ≤ 1
  · exact signedMonomial_of_support_le_one hd hf hv hs
  have htwo : 2 ≤ (multiplierSupport v).card := by omega
  by_cases hz : v = 0
  · exact Or.inl hz
  exact False.elim (hexclude v htwo (hscreen v hv) (signs_mul_cube hd hf hz hv))

/-- Every negacyclic root has unit complex norm. -/
theorem norm_negacyclic_root {d : ℕ} (hd : 0 < d) {z : ℂ}
    (hz : z ^ d = -1) : ‖z‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg z) hd.ne').mp
  rw [← norm_pow, hz]
  simp

/-- Changing sign coefficients only on a finite set loses at most twice its
cardinality at every point of the unit circle. -/
theorem coeffEval_perturbation {d : ℕ} {f g : Coeff d}
    (hf : Signs f) (hg : Signs g) (H : Finset (Fin d))
    (hagree : ∀ i, i ∉ H → f i = g i) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖coeffEval f z - coeffEval g z‖ ≤ 2 * (H.card : ℝ) := by
  classical
  have he : coeffEval f z - coeffEval g z =
      ∑ i ∈ H, ((f i : ℂ) - (g i : ℂ)) * z ^ i.val := by
    rw [coeffEval, coeffEval, ← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    symm
    apply Finset.sum_subset (Finset.subset_univ H)
    intro i _ hi
    simp [hagree i hi]
  rw [he]
  calc
    _ ≤ ∑ i ∈ H, ‖((f i : ℂ) - (g i : ℂ)) * z ^ i.val‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ H, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, norm_pow, hz, one_pow, mul_one]
      rcases hf i with hf | hf <;> rcases hg i with hg | hg <;>
        norm_num [hf, hg]
    _ = 2 * (H.card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The flip budget required by repair preserves half the seed's spectral
lower bound. -/
theorem SpectralSeed.perturbation {d : ℕ} (hd : 0 < d) {f g : Coeff d}
    (hf : SpectralSeed d f) (hg : Signs g) (H : Finset (Fin d))
    (hagree : ∀ i, i ∉ H → f i = g i)
    (hsize : 4 * (H.card : ℝ) ≤ (seedConstant : ℝ) * Real.sqrt d) :
    ∀ z : ℂ, z ^ d = -1 →
      ((seedConstant : ℝ) / 2) * Real.sqrt d ≤ ‖coeffEval g z‖ := by
  intro z hz
  have hb := coeffEval_perturbation hf.signs hg H hagree (norm_negacyclic_root hd hz)
  have hs := hf.2 z hz
  have hr := norm_sub_norm_le (coeffEval f z) (coeffEval g z)
  nlinarith only [hb, hs, hr, hsize]

set_option maxRecDepth 4096 in
set_option exponentiation.threshold 1024 in
/-- The fixed screening constant for a repaired seed is exactly `2^506`. -/
theorem half_seed_screen {d : ℕ} (hd : 0 < d) {f v : Coeff d}
    (hf : ∀ z : ℂ, z ^ d = -1 →
      ((seedConstant : ℝ) / 2) * Real.sqrt d ≤ ‖coeffEval f z‖)
    (hv : Cube (mul f v)) : IdealCVP.sqNorm v ≤ (2 ^ 506 : ℕ) := by
  have hγ : 0 < (seedConstant : ℝ) / 2 := by
    exact div_pos (by exact_mod_cast seedConstant_pos) (by norm_num)
  have hh := spectral_screen hd f v hγ hf hv
  have he : 1 / ((seedConstant : ℝ) / 2) ^ 2 = (2 ^ 506 : ℕ) := by
    norm_num [seedConstant]
  rw [he] at hh
  exact_mod_cast hh

/-- The row packing bound converts independent row survival into the repair
exponential estimate. Probabilities here are real casts of the exact rational
probabilities used by the executable construction. -/
theorem repair_event_exp_bound {d C m r : ℕ} (hC : 0 < C) (hm : m ≤ C)
    (hrows : d ≤ r * m ^ 2) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p / 2) ^ r ≤ Real.exp (-(p * d) / (2 * (C : ℝ) ^ 2)) := by
  have hcard : (d : ℝ) ≤ (r : ℝ) * (C : ℝ) ^ 2 := by
    exact_mod_cast hrows.trans (Nat.mul_le_mul_left r (Nat.pow_le_pow_left hm 2))
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  calc
    (1 - p / 2) ^ r ≤ (Real.exp (-(p / 2))) ^ r :=
      pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg (p / 2)) r
    _ = Real.exp ((r : ℝ) * (-(p / 2))) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-(p * d) / (2 * (C : ℝ) ^ 2)) := by
      apply Real.exp_le_exp.mpr
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (C : ℝ) ^ 2)).mpr
      have hh := mul_le_mul_of_nonneg_left hcard hp
      nlinarith only [hh]

/-- The candidate union term is bounded by the reciprocal candidate bound in
dyadic degree. The natural logarithm is at most the dyadic exponent. -/
theorem repair_union_exp_bound {d ℓ C : ℕ} (hd : d = 2 ^ ℓ) (hdpos : 0 < d) :
    (d : ℝ) ^ (2 * C) * Real.exp (-4 * (C : ℝ) * ℓ) ≤
      1 / (d : ℝ) ^ (2 * C) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogd : Real.log (d : ℝ) ≤ ℓ := by
    rw [hd, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hℓ : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
    nlinarith only [hℓ, hlog2]
  have hpow : (d : ℝ) ^ (2 * C) =
      Real.exp (((2 * C : ℕ) : ℝ) * Real.log d) := by
    rw [Real.exp_nat_mul, Real.exp_log hdR]
  have hprod : ((d : ℝ) ^ (2 * C) * Real.exp (-4 * (C : ℝ) * ℓ)) *
      (d : ℝ) ^ (2 * C) ≤ 1 := by
    rw [hpow, ← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    push_cast
    have hh := mul_le_mul_of_nonneg_left hlogd (by positivity : (0 : ℝ) ≤ 4 * C)
    nlinarith only [hh]
  exact (le_div_iff₀ (pow_pos hdR _)).mpr hprod

/-- The initial candidate-union contribution is at most one half. -/
theorem repair_union_exp_le_half {d ℓ C : ℕ} (hd : d = 2 ^ ℓ)
    (hd2 : 2 ≤ d) (hC : 1 ≤ C) :
    (d : ℝ) ^ (2 * C) * Real.exp (-4 * (C : ℝ) * ℓ) ≤ 1 / 2 := by
  have hdpos : 0 < d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hpow : (2 : ℝ) ≤ (d : ℝ) ^ (2 * C) :=
    hdR.trans (le_self_pow₀ (by linarith) (by omega))
  exact (repair_union_exp_bound hd hdpos).trans
    (one_div_le_one_div_of_le (by norm_num) hpow)

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 4096 in
/-- Natural-number cutoff estimates. Squaring the spectral budget avoids
separate treatment of odd and even dyadic exponents. -/
theorem repair_cutoff_nat (k : ℕ) (hk : 3600 ≤ k) :
    2 ^ 506 ≤ 2 ^ k ∧
      16 * (2 ^ 506) ^ 4 * k ≤ 2 ^ k ∧
      (64 * (2 ^ 506) ^ 3 * k * 2 ^ 252) ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨pow_le_pow_right₀ (by decide) (by decide), ?_, ?_⟩
    · calc
        16 * (2 ^ 506) ^ 4 * 3600 ≤ 16 * (2 ^ 506) ^ 4 * 2 ^ 12 :=
          Nat.mul_le_mul_left _ (by decide)
        _ = 2 ^ 2040 := by
          change (2 ^ 4 * (2 ^ 506) ^ 4 * 2 ^ 12 : ℕ) = _
          rw [← pow_mul, ← pow_add, ← pow_add]
        _ ≤ 2 ^ 3600 := pow_le_pow_right₀ (by decide) (by decide)
    · have hb : 64 * (2 ^ 506) ^ 3 * 3600 * 2 ^ 252 ≤
          64 * (2 ^ 506) ^ 3 * 2 ^ 12 * 2 ^ 252 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by decide))
      have he : (64 * (2 ^ 506) ^ 3 * 2 ^ 12 * 2 ^ 252 : ℕ) = 2 ^ 1788 := by
        change (2 ^ 6 * (2 ^ 506) ^ 3 * 2 ^ 12 * 2 ^ 252 : ℕ) = _
        rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      calc
        (64 * (2 ^ 506) ^ 3 * 3600 * 2 ^ 252) ^ 2 ≤ (2 ^ 1788) ^ 2 :=
          Nat.pow_le_pow_left (hb.trans_eq he) 2
        _ = 2 ^ 3576 := by rw [← pow_mul]
        _ ≤ 2 ^ 3600 := pow_le_pow_right₀ (by decide) (by decide)
  | succ k hk ih =>
    refine ⟨ih.1.trans (pow_le_pow_right₀ (by decide) (by omega)), ?_, ?_⟩
    · calc
        16 * (2 ^ 506) ^ 4 * (k + 1) ≤ 16 * (2 ^ 506) ^ 4 * (2 * k) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = (16 * (2 ^ 506) ^ 4 * k) * 2 := by ring
        _ ≤ 2 ^ k * 2 := Nat.mul_le_mul_right 2 ih.2.1
        _ = 2 ^ (k + 1) := (pow_succ _ _).symm
    · have hquad : (k + 1) ^ 2 ≤ 2 * k ^ 2 := by
        have hh := Nat.mul_le_mul_right k (show 3 ≤ k by omega)
        nlinarith only [hh, hk]
      calc
        (64 * (2 ^ 506) ^ 3 * (k + 1) * 2 ^ 252) ^ 2 =
            (64 * (2 ^ 506) ^ 3 * 2 ^ 252) ^ 2 * (k + 1) ^ 2 := by ring
        _ ≤ (64 * (2 ^ 506) ^ 3 * 2 ^ 252) ^ 2 * (2 * k ^ 2) :=
          Nat.mul_le_mul_left _ hquad
        _ = (64 * (2 ^ 506) ^ 3 * k * 2 ^ 252) ^ 2 * 2 := by ring
        _ ≤ 2 ^ k * 2 := Nat.mul_le_mul_right 2 ih.2.2
        _ = 2 ^ (k + 1) := (pow_succ _ _).symm

set_option maxRecDepth 4096 in
/-- Every dyadic exponent above the manuscript cutoff satisfies both repair
dimension inequalities with `C = 2^506` and `c = 2^-252`. -/
theorem repair_cutoff (k : ℕ) (hk : 3600 ≤ k) :
    2 ^ 506 ≤ 2 ^ k ∧
      16 * (2 ^ 506) ^ 4 * k ≤ 2 ^ k ∧
      ((64 * (2 ^ 506) ^ 3 * k : ℕ) : ℝ) ≤
        (seedConstant : ℝ) * Real.sqrt ((2 ^ k : ℕ) : ℝ) := by
  obtain ⟨hC, hdim, hsq⟩ := repair_cutoff_nat k hk
  refine ⟨hC, hdim, ?_⟩
  have hroot : ((64 * (2 ^ 506) ^ 3 * k * 2 ^ 252 : ℕ) : ℝ) ≤
      Real.sqrt ((2 ^ k : ℕ) : ℝ) :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast hsq)
  have hden : (0 : ℝ) < ((2 ^ 252 : ℕ) : ℝ) := by positivity
  have hconst : (seedConstant : ℝ) * ((2 ^ 252 : ℕ) : ℝ) = 1 := by
    norm_num [seedConstant]
  apply (mul_le_mul_iff_left₀ hden).mp
  calc
    _ ≤ Real.sqrt ((2 ^ k : ℕ) : ℝ) := by
      simpa only [Nat.cast_mul] using hroot
    _ = ((seedConstant : ℝ) * Real.sqrt ((2 ^ k : ℕ) : ℝ)) *
        ((2 ^ 252 : ℕ) : ℝ) := by
      rw [mul_right_comm, hconst, one_mul]

end Power2ModuleSVP
