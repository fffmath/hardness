import IdealCVP.SizeBounds
import Mathlib.Data.Nat.Size

/-! # Polynomial binary and unary output sizes

The common bound is deliberately generous: `262144 * (q+n+1)^12`.
These are encoding-size statements, without a claim about machine runtime.
-/
namespace IdealCVP

/-- A closed polynomial bounding all numerical output fields. -/
def valueBound (q n : ℕ) : ℕ := 262144 * (q+n+1)^12

private theorem penalty_le_radius {q n r : ℕ} (hq : q ≤ r) (hn : n ≤ r)
    (hr : 1 ≤ r) : penaltyBound (3*q) n ≤ 256*r^5 := by
  have hmono : penaltyBound (3*q) n ≤ penaltyBound (3*r) r := by
    unfold penaltyBound
    gcongr
  have h1 := Nat.pow_le_pow_right hr (show 1 ≤ 5 by omega)
  have h2 := Nat.pow_le_pow_right hr (show 2 ≤ 5 by omega)
  have h3 := Nat.pow_le_pow_right hr (show 3 ≤ 5 by omega)
  have h4 := Nat.pow_le_pow_right hr (show 4 ≤ 5 by omega)
  have h0 := Nat.one_le_pow 5 r hr
  apply hmono.trans
  unfold penaltyBound
  nlinarith only [h0, h1, h2, h3, h4]

theorem penaltyBound_le_valueBound (q n : ℕ) :
    penaltyBound (3*q) n ≤ valueBound q n := by
  have h := penalty_le_radius (q := q) (n := n) (r := q+n+1) (by omega) (by omega) (by omega)
  have hp := Nat.pow_le_pow_right (show 1 ≤ q+n+1 by omega) (show 5 ≤ 12 by omega)
  unfold valueBound
  omega

private theorem numerical_bounds (I : X3CInstance) :
    2 * penaltyBound (3*I.q) I.n ≤ valueBound I.q I.n ∧
    (penaltyBound (3*I.q) I.n)^2*I.n + (3*I.q)*I.n^2 ≤ valueBound I.q I.n ∧
    4*(3*I.q)*(8*I.n^2+1) ≤ valueBound I.q I.n := by
  let r := I.q+I.n+1
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hq : I.q ≤ r := by dsimp [r]; omega
  have hn : I.n ≤ r := by dsimp [r]; omega
  have hb := penalty_le_radius hq hn hr
  have hp5 := Nat.pow_le_pow_right hr (show 5 ≤ 12 by omega)
  have hp3 := Nat.pow_le_pow_right hr (show 3 ≤ 12 by omega)
  have hp1 := Nat.pow_le_pow_right hr (show 1 ≤ 12 by omega)
  have hp11 := Nat.pow_le_pow_right hr (show 11 ≤ 12 by omega)
  change _ ≤ 262144*r^12 ∧ _ ≤ 262144*r^12 ∧ _ ≤ 262144*r^12
  refine ⟨by omega, ?_, ?_⟩
  · calc
      _ ≤ (256*r^5)^2*r + (3*r)*r^2 := by gcongr
      _ = 65536*r^11 + 3*r^3 := by ring
      _ ≤ _ := by omega
  · calc
      _ ≤ 4*(3*r)*(8*r^2+1) := by gcongr
      _ = 96*r^3 + 12*r := by ring
      _ ≤ _ := by simp only [pow_one] at hp1; omega

theorem compileX3C_coeff_le (I : X3CInstance) (i : Fin (compileX3C I).d) :
    |(compileX3C I).generator i| ≤ (valueBound I.q I.n : ℤ) := by
  exact (compileX3C_size I).2.1 i |>.trans (by exact_mod_cast (numerical_bounds I).1)

theorem compileX3C_target_le (I : X3CInstance) (i : Fin (compileX3C I).d) :
    |(compileX3C I).target i| ≤ (valueBound I.q I.n : ℤ) := by
  exact (compileX3C_size I).2.2.1 i |>.trans (by exact_mod_cast (numerical_bounds I).1)

theorem compileX3C_threshold_le (I : X3CInstance) :
    (compileX3C I).threshold ≤ (valueBound I.q I.n : ℤ) := by
  exact (compileX3C_size I).2.2.2.trans (by exact_mod_cast (numerical_bounds I).2.1)

theorem compileX3C_dim_le (I : X3CInstance) :
    (compileX3C I).d ≤ valueBound I.q I.n :=
  (compileX3C_size I).1.trans (numerical_bounds I).2.2

private theorem natAbs_le_of_abs_le {c : ℤ} {b : ℕ} (h : |c| ≤ (b : ℤ)) :
    c.natAbs ≤ b := by
  exact_mod_cast (show (c.natAbs : ℤ) ≤ b by simpa only [Int.natCast_natAbs] using h)

/-- Explicit logarithmic bit bound; `Nat.size r` is the binary length of r. -/
theorem size_le_log_bound {q n c : ℕ} (hc : c ≤ valueBound q n) :
    Nat.size c ≤ 19 + 12 * Nat.size (q+n+1) := by
  apply Nat.size_le.mpr
  have hp : (q+n+1)^12 < (2 ^ Nat.size (q+n+1))^12 :=
    Nat.pow_lt_pow_left (Nat.lt_size_self _) (by omega)
  have hv : valueBound q n < 2^(18 + 12 * Nat.size (q+n+1)) := by
    calc
      _ = 2^18 * (q+n+1)^12 := by norm_num [valueBound]
      _ < 2^18 * (2^Nat.size (q+n+1))^12 := Nat.mul_lt_mul_of_pos_left hp (by positivity)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  exact hc.trans_lt (hv.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))

theorem compileX3C_coeff_bits (I : X3CInstance) (i : Fin (compileX3C I).d) :
    Nat.size ((compileX3C I).generator i).natAbs ≤ 19+12*Nat.size (I.q+I.n+1) :=
  size_le_log_bound (natAbs_le_of_abs_le (compileX3C_coeff_le I i))

theorem compileX3C_target_bits (I : X3CInstance) (i : Fin (compileX3C I).d) :
    Nat.size ((compileX3C I).target i).natAbs ≤ 19+12*Nat.size (I.q+I.n+1) :=
  size_le_log_bound (natAbs_le_of_abs_le (compileX3C_target_le I i))

theorem compileX3C_threshold_bits (I : X3CInstance) :
    Nat.size (compileX3C I).threshold.natAbs ≤ 19+12*Nat.size (I.q+I.n+1) := by
  apply size_le_log_bound
  apply natAbs_le_of_abs_le
  rw [abs_of_nonneg (show 0 ≤ (compileX3C I).threshold from (x3cToCVP I).Δ_nonneg)]
  exact compileX3C_threshold_le I

/-- Coefficient signs and separators cost two bits per entry. -/
def outputLength (D : CompiledCVPData) : ℕ :=
  (∑ i, (Nat.size (D.generator i).natAbs + 2)) +
  (∑ i, (Nat.size (D.target i).natAbs + 2)) +
  Nat.size D.threshold.natAbs + Nat.size D.d

/-- An encoding of the parameters and n indexed triples, each with three entries. -/
def inputLength (I : X3CInstance) : ℕ :=
  I.q + I.n + 3*I.n*(Nat.size (3*I.q)+1)

/-- Unary coefficients, with the nonnegative threshold and dimension. -/
def unaryLength (D : CompiledCVPData) : ℕ :=
  (∑ i, (D.generator i).natAbs) + (∑ i, (D.target i).natAbs) +
  D.threshold.natAbs + D.d

/-- One explicit polynomial for both encodings. -/
def encodingBound (s : ℕ) : ℕ := 8 * (262144*(s+1)^12 + 1)^2

private theorem size_le_self (k : ℕ) : Nat.size k ≤ k :=
  Nat.size_le.mpr (Nat.lt_two_pow_self (n := k))

private theorem common_encoding_bounds (I : X3CInstance) :
    unaryLength (compileX3C I) ≤ encodingBound (inputLength I) ∧
    outputLength (compileX3C I) ≤ encodingBound (inputLength I) := by
  let v := valueBound I.q I.n
  have hg (i) : ((compileX3C I).generator i).natAbs ≤ v :=
    natAbs_le_of_abs_le (compileX3C_coeff_le I i)
  have ht (i) : ((compileX3C I).target i).natAbs ≤ v :=
    natAbs_le_of_abs_le (compileX3C_target_le I i)
  have hΔ : (compileX3C I).threshold.natAbs ≤ v := by
    apply natAbs_le_of_abs_le
    rw [abs_of_nonneg (show 0 ≤ (compileX3C I).threshold from (x3cToCVP I).Δ_nonneg)]
    exact compileX3C_threshold_le I
  have hd := compileX3C_dim_le I
  change (compileX3C I).d ≤ v at hd
  have hsumg : (∑ i, ((compileX3C I).generator i).natAbs) ≤ (compileX3C I).d*v := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hg i)
  have hsumt : (∑ i, ((compileX3C I).target i).natAbs) ≤ (compileX3C I).d*v := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => ht i)
  have hbg : (∑ i, (Nat.size ((compileX3C I).generator i).natAbs+2)) ≤
      (compileX3C I).d*(v+2) := by
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => Nat.add_le_add_right ((size_le_self _).trans (hg i)) 2)
  have hbt : (∑ i, (Nat.size ((compileX3C I).target i).natAbs+2)) ≤
      (compileX3C I).d*(v+2) := by
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => Nat.add_le_add_right ((size_le_self _).trans (ht i)) 2)
  have hszΔ := (size_le_self _).trans hΔ
  have hszd := (size_le_self _).trans hd
  have hv : v ≤ 262144*(inputLength I+1)^12 := by
    dsimp [v, valueBound, inputLength]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega
  have hpoly : 8*(v+1)^2 ≤ encodingBound (inputLength I) := by
    unfold encodingBound
    gcongr
  have hmul := Nat.mul_le_mul_right v hd
  have hmul2 := Nat.mul_le_mul_right (v+2) hd
  constructor
  · apply le_trans (b := 8*(v+1)^2) ?_ hpoly
    unfold unaryLength
    nlinarith only [hsumg, hsumt, hΔ, hd, hmul]
  · apply le_trans (b := 8*(v+1)^2) ?_ hpoly
    unfold outputLength
    nlinarith only [hbg, hbt, hszΔ, hszd, hmul2]

theorem compileX3C_outputLength_le (I : X3CInstance) :
    outputLength (compileX3C I) ≤ encodingBound (inputLength I) :=
  (common_encoding_bounds I).2

/-- Polynomial unary size is the numerical content of strong hardness here. -/
theorem compileX3C_unaryLength_le (I : X3CInstance) :
    unaryLength (compileX3C I) ≤ encodingBound (inputLength I) :=
  (common_encoding_bounds I).1

end IdealCVP
