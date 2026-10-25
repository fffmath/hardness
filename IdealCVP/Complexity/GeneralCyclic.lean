import IdealCVP.IntegerPreimage
import IdealCVP.Complexity.SeparatedCyclic

/-! # NP membership for arbitrary principal cyclic generators

A coefficient-list verifier and bounded integer preimages establish membership and
NP-completeness without a nonsingularity promise. This extends the cyclic language
of `principal-ideal.tex`, Section `sec:cyclic-cvp`, to arbitrary generators.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace IdealCVP

open Turing.MultiTapeTM Cslib.Complexity IdealCVP.Cyclotomic
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace Cyclic

/-- Ordinary cyclic convolution, including zero and singular generators. -/
def convolution {n : ℕ} (g q : Coeff n) : Coeff n := fun r =>
  ∑ i, ∑ j, if (i.val + j.val) % n = r.val then g i * q j else 0

/-- Cyclic multiplication by a fixed generator as an additive homomorphism. -/
def convolutionHom {n : ℕ} (g : Coeff n) : Coeff n →+ Coeff n where
  toFun := convolution g
  map_zero' := by ext; simp [convolution]
  map_add' a b := by
    ext r
    simp only [convolution, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp [_root_.mul_add]

/-- The integer coefficient matrix of cyclic multiplication by a generator. -/
noncomputable def generalMultiplicationMatrix {n : ℕ} (g : Coeff n) :
    Matrix (Fin n) (Fin n) ℤ := LinearMap.toMatrix' (convolutionHom g).toIntLinearMap

@[simp] theorem generalMultiplicationMatrix_mulVec {n : ℕ} (g q : Coeff n) :
    (generalMultiplicationMatrix g).mulVec q = convolution g q :=
  LinearMap.toMatrix'_mulVec _ _

theorem convolution_bound {n : ℕ} (g q : Coeff n) (A B : ℤ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hg : ∀ i, |g i| ≤ A) (hq : ∀ i, |q i| ≤ B)
    (r : Fin n) : |convolution g q r| ≤ (n : ℤ) ^ 2 * A * B := by
  unfold convolution
  calc
    _ ≤ ∑ i, ∑ j, |if (i.val + j.val) % n = r.val then g i * q j else 0| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, A * B := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · rw [abs_mul]; exact mul_le_mul (hg i) (hq j) (abs_nonneg _) hA
      · exact mul_nonneg hA hB
    _ = _ := by simp; ring

theorem generalMultiplicationMatrix_entry_bound {n : ℕ} (g : Coeff n) (A : ℤ)
    (hA : 0 ≤ A) (hg : ∀ i, |g i| ≤ A) (i j : Fin n) :
    |generalMultiplicationMatrix g i j| ≤ (n : ℤ) ^ 2 * A := by
  rw [generalMultiplicationMatrix, LinearMap.toMatrix'_apply]
  change |convolution g (Pi.single j 1) i| ≤ _
  simpa using convolution_bound g (Pi.single j 1) A 1 hA (by omega) hg
    (fun k => by by_cases h : k = j <;> simp [h]) i

/-- Cyclic convolution is multiplication in the actual polynomial quotient. -/
theorem toRing_convolution {d : ℕ} (hd : 0 < d) (g q : Coeff (2 * d)) :
    toRing (convolution g q) = toRing g * toRing q := by
  have hn : 0 < 2 * d := by omega
  have fold (i j : Fin (2 * d)) : x d ^ (i.val + j.val) = x d ^ ((i.val + j.val) % (2 * d)) := by
    calc
      _ = x d ^ ((i.val + j.val) % (2 * d) + (2 * d) * ((i.val + j.val)/(2 * d))) := by
        rw [Nat.mod_add_div]
      _ = _ := by rw [pow_add, pow_mul, x_pow_twice, one_pow, mul_one]
  have step (i j : Fin (2 * d)) :
      (∑ r : Fin (2 * d),
        (if (i.val + j.val) % (2 * d) = r.val then g i * q j else 0) • x d ^ r.val) =
        (g i * q j) • x d ^ (i.val + j.val) := by
    let r₀ : Fin (2 * d) := ⟨(i.val + j.val) % (2 * d), Nat.mod_lt _ hn⟩
    rw [Finset.sum_eq_single r₀]
    · simp only [r₀, ite_true, fold]
    · intro r _ hr
      have hne : (i.val + j.val) % (2 * d) ≠ r.val := fun h => hr (Fin.ext h.symm)
      simp [hne]
    · simp
  calc
    toRing (convolution g q) = ∑ i : Fin (2 * d), ∑ j : Fin (2 * d), ∑ r : Fin (2 * d),
        (if (i.val + j.val) % (2 * d) = r.val then g i * q j else 0) • x d ^ r.val := by
      simp only [toRing_sum, convolution, Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin (2 * d), ∑ j : Fin (2 * d), (g i * q j) • x d ^ (i.val + j.val) := by
      simp only [step]
    _ = toRing g * toRing q := by
      simp only [toRing_sum, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, ← pow_add]
      rw [Finset.sum_comm]

end Cyclic

/-- Cyclic list multiplication uses the same finite loops as negacyclic multiplication. -/
def cyclicCoeff (n : ℕ) (g q : List ℤ) (r : ℕ) : ℤ :=
  ((List.range n).map fun i => ((List.range n).map fun j =>
    if (i + j) % n = r then g.getD i 0 * q.getD j 0 else 0).sum).sum

/-- List representation of ordinary cyclic convolution in dimension `n`. -/
def cyclicMul (n : ℕ) (g q : List ℤ) : List ℤ :=
  (List.range n).map (cyclicCoeff n g q)

@[simp] theorem length_cyclicMul (n : ℕ) (g q : List ℤ) : (cyclicMul n g q).length = n := by
  simp [cyclicMul]

theorem ofList_cyclicMul (n : ℕ) (g q : List ℤ) :
    ofList (d := n) (cyclicMul n g q) = Cyclic.convolution (ofList g) (ofList q) := by
  ext r
  simp only [ofList, cyclicMul, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range, r.isLt, Option.map_some, Option.getD_some]
  simp only [cyclicCoeff, Cyclic.convolution, list_sum_range, Finset.sum_range, ofList]

/-- Recognize power-of-two half-dimension and the two required list lengths. -/
def cyclicGeneralCheck (x : CVPInput) : Bool :=
  cvpWellFormedCheck (x.1, List.replicate x.1 0, List.replicate x.1 0, x.2.2.2) &&
    decide (x.2.1.length = 2 * x.1) && decide (x.2.2.1.length = 2 * x.1)

theorem cyclicGeneralCheck_spec (x : CVPInput) : cyclicGeneralCheck x = true ↔
    (∃ k, x.1 = 2 ^ k) ∧ x.2.1.length = 2 * x.1 ∧ x.2.2.1.length = 2 * x.1 := by
  simp [cyclicGeneralCheck, cvpWellFormedCheck_eq, CVPInput.WellFormed, and_assoc]

/-- Verify a cyclic multiplier certificate by its length and squared distance. -/
def cyclicGeneralVerifier (p : CVPInput × List ℤ) : Bool :=
  cyclicGeneralCheck p.1 && decide (p.2.length = 2 * p.1.1) &&
    decide (listSqDistance (2 * p.1.1) (cyclicMul (2 * p.1.1) p.1.2.1 p.2) p.1.2.2.1 ≤ p.1.2.2.2)

theorem cyclicGeneralVerifier_spec (x : CVPInput) (q : List ℤ) :
    cyclicGeneralVerifier (x, q) = true ↔ cyclicGeneralCheck x = true ∧ q.length = 2 * x.1 ∧
      sqNorm (Cyclic.convolution (ofList (d :=
        2 * x.1) x.2.1) (ofList q) - ofList x.2.2.1) ≤ x.2.2.2 := by
  simp only [cyclicGeneralVerifier, Bool.and_eq_true, decide_eq_true_eq, listSqDistance_eq,
    ofList_cyclicMul, and_assoc]

/-- An arbitrary principal cyclic CVP instance is YES exactly when its list verifier accepts a
multiplier. -/
theorem principalCyclicCVP_iff_exists_check (x : CVPInput) :
    x ∈ PrincipalCyclicCVP ↔ ∃ q, cyclicGeneralVerifier (x, q) = true := by
  constructor
  · rintro ⟨hd, hg, ht, w, hw, hnorm⟩
    have hp := Cyclotomic.power_two_pos hd
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hw
    obtain ⟨q, rfl⟩ := (Cyclic.toRing_bijective hp).surjective a
    have he : w = Cyclic.convolution (ofList x.2.1) q := by
      apply (Cyclic.toRing_bijective hp).injective
      rw [Cyclic.toRing_convolution hp]
      simpa [_root_.mul_comm] using ha
    refine ⟨toList q, (cyclicGeneralVerifier_spec x _).mpr
      ⟨(cyclicGeneralCheck_spec x).mpr ⟨hd, hg, ht⟩, length_toList _, ?_⟩⟩
    simpa only [ofList_toList, ← he] using hnorm
  · rintro ⟨q, hq⟩
    obtain ⟨hw, _, hnorm⟩ := (cyclicGeneralVerifier_spec x q).mp hq
    obtain ⟨hd, hg, ht⟩ := (cyclicGeneralCheck_spec x).mp hw
    refine ⟨hd, hg, ht, Cyclic.convolution (ofList x.2.1) (ofList q), ?_, hnorm⟩
    rw [Cyclic.toRing_convolution (Cyclotomic.power_two_pos hd)]
    exact Ideal.mem_span_singleton.mpr ⟨Cyclic.toRing (ofList q), by ring⟩

attribute [local irreducible] List.getD

@[fun_prop] theorem poly_cyclicCoeff : ComputableTidilyInPolyTime
    (fun p : RingArgs × ℕ => cyclicCoeff p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair encRingArgs encUnary) encIntBin := by
  let encT := encPair (encPair (encPair encRingArgs encUnary) encUnary) encUnary
  have hb : ComputableTidilyInPolyTime
      (fun p : ((RingArgs × ℕ) × ℕ) × ℕ => p.1.1.1) encT encRingArgs :=
    (fst _ _).fst'.fst'
  have hi : ComputableTidilyInPolyTime
      (fun p : ((RingArgs × ℕ) × ℕ) × ℕ => p.1.2) encT encUnary := (fst _ _).snd'
  have hj : ComputableTidilyInPolyTime
      (fun p : ((RingArgs × ℕ) × ℕ) × ℕ => p.2) encT encUnary := snd _ _
  have hr : ComputableTidilyInPolyTime
      (fun p : ((RingArgs × ℕ) × ℕ) × ℕ => p.1.1.2) encT encUnary := (fst _ _).fst'.snd'
  have hd := (fst encUnary (encPair (encList encIntBin) (encList encIntBin))).comp hb
  have hg := ((snd encUnary (encPair (encList encIntBin) (encList encIntBin))).fst').comp hb
  have hq := ((snd encUnary (encPair (encList encIntBin) (encList encIntBin))).snd').comp hb
  have hguard := (decide_eq encUnary).comp
    ((unary_mod.comp ((unary_add.comp (hi.prod hj)).prod hd)).prod hr)
  have hprod := intBin_mul.comp
    (((listGetD (encA := encIntBin) 0).comp (hg.prod hi)).prod
      ((listGetD (encA := encIntBin) 0).comp (hq.prod hj)))
  have hterm := ite_decide hguard hprod
    (const (encIn := encT) (encMid := encIntBin) 0)
  unfold cyclicCoeff
  apply intBin_sum.comp
  apply mapWithInput (encA := encUnary)
  · unfold encRingArgs; fun_prop
  apply intBin_sum.comp
  apply mapWithInput (encA := encUnary)
  · unfold encRingArgs; fun_prop
  exact hterm

@[fun_prop] theorem poly_cyclicMul : ComputableTidilyInPolyTime
    (fun p : RingArgs => cyclicMul p.1 p.2.1 p.2.2) encRingArgs (encList encIntBin) := by
  unfold cyclicMul
  apply mapWithInput (encA := encUnary)
  · unfold encRingArgs; fun_prop
  · exact poly_cyclicCoeff

@[fun_prop] theorem poly_cyclicGeneralCheck : ComputableTidilyInPolyTime
    cyclicGeneralCheck encCVP encBool := by
  unfold cyclicGeneralCheck encCVP
  fun_prop

/-- Checking an arbitrary cyclic multiplier and its distance takes native polynomial time. -/
@[fun_prop] theorem poly_cyclicGeneralVerifier : ComputableTidilyInPolyTime
    cyclicGeneralVerifier (encPair encCVP (encList encIntBin)) encBool := by
  unfold cyclicGeneralVerifier encCVP
  fun_prop

/-- A quartic encoded witness bound, including signs and list framing. -/
noncomputable def cyclicGeneralWitnessPolynomial : Polynomial ℕ :=
  2 * Polynomial.X * (2 * (64 * (Polynomial.X + 1) * (2 * Polynomial.X + 1) ^ 2 + 2) + 1)

/-- Uniform entry and short-vector bounds suitable for the arbitrary-rank theorem. -/
theorem cyclicGeneral_preimage_bounds (x : CVPInput) (w : Coeff (2 * x.1))
    (hw : sqNorm (w - ofList x.2.2.1) ≤ x.2.2.2) :
    let L := 4 * ((encCVP x).length + 1)
    ((2 * x.1 : ℕ) : ℤ) ≤ 2 ^ L ∧
    (∀ i j, |Cyclic.generalMultiplicationMatrix (ofList (d := 2 * x.1) x.2.1) i j| ≤ 2 ^ L) ∧
    ∀ i, |w i| ≤ 2 ^ L := by
  let N := (encCVP x).length
  let A : ℤ := 2 ^ N
  have hA : 1 ≤ A := one_le_pow₀ (by omega)
  obtain ⟨hdN, hglen, htlen, hΔlen⟩ := cvp_input_length_bounds x
  have hdA : (x.1 : ℤ) ≤ A := by
    dsimp [A]
    exact_mod_cast hdN.trans (Nat.lt_two_pow_self (n := N)).le
  have hnA : ((2 * x.1 : ℕ) : ℤ) ≤ 2 * A := by push_cast; omega
  have hg (i : Fin (2 * x.1)) : |ofList x.2.1 i| ≤ A := getD_abs_le_two_pow _ N hglen i.val
  have ht (i : Fin (2 * x.1)) : |ofList x.2.2.1 i| ≤ A := getD_abs_le_two_pow _ N htlen i.val
  have hΔ : |x.2.2.2| ≤ A := by
    rw [length_encIntBin] at hΔlen
    have hs : x.2.2.2.natAbs.size ≤ N := by omega
    dsimp [A]
    rw [← Int.natCast_natAbs]
    exact_mod_cast (Nat.size_le.mp hs).le
  have hp : (2 : ℤ) ^ (4 * (N + 1)) = 16 * A ^ 4 := by
    rw [show 4 * (N + 1) = N * 4 + 4 by omega, pow_add, pow_mul]
    norm_num
    dsimp [A]
    ring
  change _ ≤ (2 : ℤ) ^ (4 * (N + 1)) ∧ _ ∧ _
  rw [hp]
  have hA34 : A ^ 3 ≤ A ^ 4 := pow_le_pow_right₀ hA (by omega)
  have hA14 : A ≤ A ^ 4 := by simpa using pow_le_pow_right₀ hA (show 1 ≤ 4 by omega)
  refine ⟨hnA.trans (by nlinarith), ?_, ?_⟩
  · intro i j
    apply (Cyclic.generalMultiplicationMatrix_entry_bound _ A (by omega) hg i j).trans
    calc
      _ ≤ (2 * A) ^ 2 * A := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hnA 2) (by omega)
      _ = 4 * A ^ 3 := by ring
      _ ≤ 16 * A ^ 4 := by nlinarith [pow_nonneg (by omega : 0 ≤ A) 4]
  · intro i
    have hr := (residual_coordinate_le (w - ofList x.2.2.1) i).trans hw
    have he : w i = ofList (d :=
      2 * x.1) x.2.2.1 i + (w - ofList (d := 2 * x.1) x.2.2.1) i := by simp
    calc
      _ = |ofList (d :=
        2 * x.1) x.2.2.1 i + (w - ofList (d := 2 * x.1) x.2.2.1) i| := congrArg abs he
      _ ≤ |ofList (d :=
        2 * x.1) x.2.2.1 i| + |(w - ofList (d := 2 * x.1) x.2.2.1) i| := abs_add_le _ _
      _ ≤ A + A := add_le_add (ht i) (hr.trans (le_abs_self _ ) |>.trans hΔ)
      _ ≤ _ := by nlinarith

/-- Arbitrary singular or zero generators have polynomial-bit integer multipliers. -/
theorem principalCyclicCVPGeneral_bounded_certificate (x : CVPInput) (hx : x ∈ PrincipalCyclicCVP) :
    ∃ q : List ℤ, cyclicGeneralVerifier (x, q) = true ∧
      (encList encIntBin q).length ≤ cyclicGeneralWitnessPolynomial.eval (encCVP x).length := by
  obtain ⟨q, hq⟩ := (principalCyclicCVP_iff_exists_check x).mp hx
  obtain ⟨hw, hql, hnorm⟩ := (cyclicGeneralVerifier_spec x q).mp hq
  let M := Cyclic.generalMultiplicationMatrix (ofList (d := 2 * x.1) x.2.1)
  let w := M.mulVec (ofList q)
  have hn : sqNorm (w - ofList x.2.2.1) ≤ x.2.2.2 := by simpa [w, M] using hnorm
  obtain ⟨hd, hM, hv⟩ := cyclicGeneral_preimage_bounds x w hn
  let N := (encCVP x).length
  let L := 4 * (N + 1)
  obtain ⟨q', heq, hbits⟩ := exists_integer_preimage_bits M w L (by dsimp [L]; omega)
    hd hd hM hv ⟨ofList q, rfl⟩
  have hdN := (cvp_input_length_bounds x).1
  have hbits' (i : Fin (2 * x.1)) : (q' i).natAbs.size ≤ 64 * (N + 1) * (2 * N + 1) ^ 2 + 1 := by
    apply (hbits i).trans
    dsimp [L]
    calc
      _ = 64 * (N + 1) * (2 * x.1 + 1) ^ 2 + 1 := by ring
      _ ≤ _ := by gcongr
  refine ⟨toList q', (cyclicGeneralVerifier_spec x _).mpr ⟨hw, length_toList _, ?_⟩, ?_⟩
  · rw [ofList_toList, ← Cyclic.generalMultiplicationMatrix_mulVec, heq]
    exact hn
  · have hl : (encList encIntBin (toList q')).length ≤
        (toList q').length * (2 * (64 * (N + 1) * (2 * N + 1) ^ 2 + 2) + 1) := by
      apply length_encList_le
      intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      rw [length_encIntBin]
      have hh := hbits' i
      omega
    rw [length_toList] at hl
    apply hl.trans
    simp only [cyclicGeneralWitnessPolynomial, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]
    exact Nat.mul_le_mul_right _ (by omega : 2 * x.1 ≤ 2 * N)

/-- NP membership for the original arbitrary-generator principal cyclic language. -/
theorem principalCyclicCVPGeneral_mem_NP : PrincipalCyclicCVP ∈ NP encCVP := by
  have he : PrincipalCyclicCVP = {x | ∃ q, cyclicGeneralVerifier (x, q) = true} := by
    ext x; exact principalCyclicCVP_iff_exists_check x
  rw [he]
  apply mem_NP_of_witness (p := cyclicGeneralWitnessPolynomial) intBinDecoder.list
    poly_cyclicGeneralVerifier (fun _ _ => Iff.rfl)
  intro x q hq
  exact principalCyclicCVPGeneral_bounded_certificate x
    ((principalCyclicCVP_iff_exists_check x).mpr ⟨q, hq⟩)

/-- Unconditional completeness, including all singular cyclic multiplication lattices. -/
theorem principalCyclicCVPGeneral_npComplete : NPComplete encCVP PrincipalCyclicCVP :=
  ⟨principalCyclicCVPGeneral_mem_NP, principalCyclicCVP_npHard⟩

end IdealCVP
