import Power2ModuleSVP.Coset.ParityBlock
import Power2ModuleSVP.Coset.Norm.Separation
import Power2ModuleSVP.Source.Boolean.Reduction

/-!
# Packing

Semantic affine-to-coset packing. Raw inputs and output arrays are total finite
data; root promises are used only in proofs. Runtime certification is separate.

Paper: `paper/power2svp.pdf`, Sections 2–3.1 (coefficient arithmetic and Theorem 2).
-/

namespace Power2ModuleSVP
open Polynomial
open IdealCVP.Cyclotomic

/-- `(L,T,P,c)`, with explicit coefficient lists. -/
abbrev AffineInput := ℕ × (ℕ × (List ℤ × List ℤ))

/-- The standard representative, reusing the existing coefficient model. -/
noncomputable abbrev coefficientPolynomial {d : ℕ} (a : Coeff d) : ℤ[X] := IdealCVP.Cyclic.poly a

theorem coefficientPolynomial_coeff {d : ℕ} (a : Coeff d) (n : ℕ) :
    (coefficientPolynomial a).coeff n = if hn : n < d then a ⟨n, hn⟩ else 0 := by
  classical
  simp only [coefficientPolynomial, IdealCVP.Cyclic.poly, finsetSum_coeff,
    coeff_C_mul, coeff_X_pow, mul_ite, _root_.mul_one, MulZeroClass.mul_zero]
  by_cases hn : n < d
  · rw [dite_eq_left hn, Finset.sum_eq_single (⟨n, hn⟩ : Fin d)]
    · simp
    · intro i _ hi
      have hne : n ≠ i.val := fun he => hi (Fin.ext he.symm)
      simp [hne]
    · simp
  · have hne : ∀ i : Fin d, (i : ℕ) ≠ n := fun i h => hn (h ▸ i.isLt)
    simp [hn, fun i => (hne i).symm]

theorem coefficientPolynomial_degree {d : ℕ} (a : Coeff d) :
    (coefficientPolynomial a).degree < d := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro n hn
  simp [coefficientPolynomial_coeff, not_lt.mpr hn]

/-- Total list interpretation; shape is separately checked. -/
noncomputable def listPolynomial (a : List ℤ) : ℤ[X] :=
  coefficientPolynomial (IdealCVP.ofList (d := a.length) a)

theorem listPolynomial_coeff (a : List ℤ) (n : ℕ) :
    (listPolynomial a).coeff n = a.getD n 0 := by
  rw [listPolynomial, coefficientPolynomial_coeff]
  split_ifs with h
  · rfl
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : a.length ≤ n)]

theorem listPolynomial_degree (a : List ℤ) : (listPolynomial a).degree < a.length :=
  coefficientPolynomial_degree _

/-- The affine modulus obtained from the stored degree and polynomial. -/
noncomputable def affineW (q : AffineInput) : ℤ[X] := X^q.1 + listPolynomial q.2.2.1

/-- Internal source promises, never decided by the packing program. -/
structure AffineInput.WellFormed (q : AffineInput) : Prop where
  P_length : q.2.2.1.length = q.2.1 + 1
  c_length : q.2.2.2.length = q.1
  T_pos : 0 < q.2.1
  L_large : 64 ≤ q.1
  scale : 4*q.2.1 < q.1
  P_bit : ∀ n, (listPolynomial q.2.2.1).coeff n = 0 ∨
    (listPolynomial q.2.2.1).coeff n = 1
  P_zero : (listPolynomial q.2.2.1).coeff 0 = 1
  P_top : (listPolynomial q.2.2.1).coeff q.2.1 = 1
  reciprocal : (listPolynomial q.2.2.1).reflect q.2.1 = listPolynomial q.2.2.1
  c_ternary : ∀ n, (listPolynomial q.2.2.2).coeff n = -1 ∨
    (listPolynomial q.2.2.2).coeff n = 0 ∨ (listPolynomial q.2.2.2).coeff n = 1
  root : NoCommonReciprocalRoot (affineW q)

/-- Polynomial form of the affine bit-vector equation. -/
def AffineYes (q : AffineInput) : Prop := ∃ x y : ℤ[X],
  SparseEncoding.BitPolynomial q.1 x ∧ SparseEncoding.BitPolynomial q.1 y ∧
  y = (listPolynomial q.2.2.1*x) %ₘ affineW q + listPolynomial q.2.2.2

/-- Least dyadic majorant, with value one at zero. -/
def dyadicCeil (n : ℕ) : ℕ := 2 ^ Nat.clog 2 n

theorem dyadicCeil_dyadic (n : ℕ) : Dyadic (dyadicCeil n) := ⟨_, rfl⟩
theorem le_dyadicCeil (n : ℕ) : n ≤ dyadicCeil n := Nat.le_pow_clog (by decide) n

theorem dyadicCeil_lt_twice {n : ℕ} (hn : 0 < n) : dyadicCeil n < 2*n := by
  by_cases h : n ≤ 1
  · have : n = 1 := by omega
    subst n
    norm_num [dyadicCeil]
  · have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < n)
    have hc : 0 < Nat.clog 2 n := by
      rw [Nat.lt_clog_iff_pow_lt (by decide)]
      simpa using (show 1 < n by omega)
    have he : Nat.clog 2 n = (Nat.clog 2 n - 1) + 1 := by omega
    unfold dyadicCeil
    rw [he, pow_succ]
    simp only [Nat.pred_eq_sub_one] at hp
    omega

/-- The small block degree and the cubic separation degree. -/
def packingBlockSize (L : ℕ) : ℕ := dyadicCeil (2*L)
/-- The dyadic degree used for cubic norm separation. -/
def packingDegree (L : ℕ) : ℕ := dyadicCeil (16*L^3)
/-- The packing degree enlarged to meet the module reduction cutoff. -/
def modulePackingDegree (k0 L : ℕ) : ℕ := max (2^k0) (packingDegree L)

theorem packing_degrees {L D : ℕ} (hL : 64 ≤ L) (hDy : Dyadic D)
    (hD : 16 * L ^ 3 ≤ D) :
    2*L ≤ packingBlockSize L ∧ packingBlockSize L < 4*L ∧
    packingBlockSize L ∣ D := by
  have hm := le_dyadicCeil (2*L)
  have hmhi := dyadicCeil_lt_twice (by omega : 0 < 2*L)
  have hLD : 4*L ≤ D := by nlinarith [sq_nonneg (L-1 : ℤ)]
  have hmhi' : packingBlockSize L < 4*L := by
    dsimp [packingBlockSize]
    omega
  refine ⟨hm, hmhi', ?_⟩
  obtain ⟨k, hk⟩ := hDy
  have hpow : 2 ^ Nat.clog 2 (2*L) ≤ 2^k := by
    change packingBlockSize L ≤ 2^k
    rw [← hk]
    exact (Nat.le_of_lt hmhi').trans hLD
  exact hk ▸ (pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow))

/-- Read a polynomial into a coefficient vector. Used only in semantic proofs. -/
def polynomialCoeffs (d : ℕ) (p : ℤ[X]) : Coeff d := fun i => p.coeff i.val

theorem coefficientPolynomial_polynomialCoeffs {d : ℕ} {p : ℤ[X]}
    (hp : p.degree < d) : coefficientPolynomial (polynomialCoeffs d p) = p := by
  ext n
  rw [coefficientPolynomial_coeff]
  split_ifs with h
  · rfl
  · exact ((degree_lt_iff_coeff_zero _ _).mp hp n (by omega)).symm

theorem toQuot_polynomialCoeffs {d : ℕ} {p : ℤ[X]} (hp : p.degree < d) :
    toQuot (polynomialCoeffs d p) = AdjoinRoot.mk (modulus d) p := by
  rw [toQuot_eq_mk]
  change AdjoinRoot.mk (modulus d) (coefficientPolynomial (polynomialCoeffs d p)) = _
  rw [coefficientPolynomial_polynomialCoeffs hp]

theorem affineW_monic {q : AffineInput} (hq : q.WellFormed) : (affineW q).Monic := by
  apply monic_X_pow_add
  have hp := listPolynomial_degree q.2.2.1
  rw [hq.P_length] at hp
  exact hp.trans_le (by exact_mod_cast (show q.2.1+1 ≤ q.1 by have := hq.scale; omega))

theorem affineW_natDegree {q : AffineInput} (hq : q.WellFormed) :
    (affineW q).natDegree = q.1 := by
  have hp := listPolynomial_degree q.2.2.1
  rw [hq.P_length] at hp
  have hlt : (listPolynomial q.2.2.1).degree < q.1 :=
    hp.trans_le (by exact_mod_cast (show q.2.1+1 ≤ q.1 by have := hq.scale; omega))
  unfold affineW
  rw [natDegree_add_eq_left_of_degree_lt (by simpa using hlt)]
  simp

theorem affineW_unit {q : AffineInput} (hq : q.WellFormed) : HasUnitConstant (affineW q) := by
  left
  have hL : q.1 ≠ 0 := by have := hq.L_large; omega
  simp [affineW, Ne.symm hL, hq.P_zero]

/-- Convolution by a bit polynomial of degree at most `T` increases height
by at most `T+1`. This estimate does not depend on the other factor's degree. -/
theorem bitPolynomial_mul_height {P a : ℤ[X]} {T H : ℕ}
    (hdeg : P.natDegree ≤ T) (hP : ∀ n, P.coeff n = 0 ∨ P.coeff n = 1)
    (ha : CoefficientBound a H) : CoefficientBound (P*a) ((T+1)*H) := by
  intro n
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow' (show P.natDegree < T+1 by omega)]
  rw [Finset.sum_mul, finsetSum_coeff]
  calc
    _ ≤ ∑ i ∈ Finset.range (T+1), |((C (P.coeff i)*X^i)*a).coeff n| :=
      Finset.abs_sum_le_sum_abs (fun i : ℕ => ((C (P.coeff i)*X^i)*a).coeff n) (Finset.range (T+1))
    _ ≤ ∑ _i ∈ Finset.range (T+1), (H : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [_root_.mul_assoc, coeff_C_mul, coeff_X_pow_mul']
      rcases hP i with hi | hi
      · simp [hi]
      · simp only [hi, one_mul]
        split_ifs
        · exact ha _
        · simp
    _ = _ := by simp [Nat.cast_mul]

/-- One monic substitution suffices for the auxiliary remainder. -/
theorem affine_remainder_height {q : AffineInput} (hq : q.WellFormed)
    {x : ℤ[X]} (hx : SparseEncoding.BitPolynomial q.1 x) :
    CoefficientBound ((listPolynomial q.2.2.1*x) %ₘ affineW q)
      ((q.2.1+1)+(q.2.1+1)^2) := by
  let P := listPolynomial q.2.2.1
  let w := affineW q
  let a := (P*x) /ₘ w
  have hT : 0 < q.2.1 := hq.T_pos
  have hTL : 4*q.2.1 < q.1 := hq.scale
  have hPdeg : P.natDegree ≤ q.2.1 := by
    have hh := listPolynomial_degree q.2.2.1
    rw [hq.P_length] at hh
    have hpos : 0 < q.2.1+1 := by omega
    exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt (by
      intro hz
      have hc := hq.P_zero
      change P.coeff 0 = 1 at hc
      rw [hz] at hc
      norm_num at hc)).mpr hh)
  have hxnd : x.natDegree < q.1 := by
    by_cases hx0 : x = 0
    · simp [hx0]; have := hq.L_large; omega
    · exact (natDegree_lt_iff_degree_lt hx0).mpr hx.1
  have hadeg : a.natDegree < q.2.1 := by
    dsimp [a, w]
    rw [natDegree_divByMonic _ (affineW_monic hq), affineW_natDegree hq]
    have hm := natDegree_mul_le (p := P) (q := x)
    omega
  have hPa : (P*a).natDegree < q.1 := by
    have hm := natDegree_mul_le (p := P) (q := a)
    omega
  have hPbit := hq.P_bit
  have hxH : CoefficientBound x 1 := by
    intro n
    rcases hx.2 n with h | h <;> simp [h]
  have hprod := bitPolynomial_mul_height hPdeg hPbit hxH
  have haH : CoefficientBound a (q.2.1+1) := by
    intro n
    have he := congrArg (fun p : ℤ[X] => p.coeff (q.1+n))
      (modByMonic_eq_sub_mul_div (P*x) w)
    have hr : ((P*x) %ₘ w).coeff (q.1+n) = 0 := by
      apply (degree_lt_iff_coeff_zero _ q.1).mp
        (by simpa only [degree_eq_natDegree (affineW_monic hq).ne_zero,
          affineW_natDegree hq] using degree_modByMonic_lt (P*x) (affineW_monic hq))
      omega
    have hp0 : (P*a).coeff (q.1+n) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    change _ = ((P*x) - (X^q.1+P)*a).coeff (q.1+n) at he
    rw [hr, add_mul, coeff_sub, coeff_add, coeff_X_pow_mul',
      ite_eq_left (by omega : q.1 ≤ q.1+n), Nat.add_sub_cancel_left, hp0, add_zero] at he
    have hh := hprod (q.1+n)
    simp only [Nat.mul_one] at hh
    have he' : a.coeff n = (P*x).coeff (q.1+n) := by omega
    rwa [he']
  have hPaH := bitPolynomial_mul_height hPdeg hPbit haH
  intro n
  by_cases hn : n < q.1
  · have he := congrArg (fun p : ℤ[X] => p.coeff n)
      (modByMonic_eq_sub_mul_div (P*x) w)
    change _ = ((P*x) - (X^q.1+P)*a).coeff n at he
    rw [add_mul, coeff_sub, coeff_add, coeff_X_pow_mul',
      ite_eq_right (by omega : ¬q.1 ≤ n), zero_add] at he
    rw [he]
    calc
      _ ≤ |(P*x).coeff n| + |(P*a).coeff n| := abs_sub _ _
      _ ≤ _ := by have h1 := hprod n; have h2 := hPaH n; push_cast at *; nlinarith
  · have hz : ((P*x) %ₘ w).coeff n = 0 := by
      apply (degree_lt_iff_coeff_zero _ q.1).mp
        (by simpa only [degree_eq_natDegree (affineW_monic hq).ne_zero,
          affineW_natDegree hq] using degree_modByMonic_lt (P*x) (affineW_monic hq))
      omega
    change |((P*x) %ₘ w).coeff n| ≤ _
    rw [hz, abs_zero]
    positivity

/-- Initial run of ones, followed by implicit zero padding. -/
noncomputable def signWord (n : ℕ) : ℤ[X] := SparseEncoding.vectorPolynomial n (fun _ => 1)

@[simp] theorem signWord_coeff (n i : ℕ) :
    (signWord n).coeff i = if i < n then 1 else 0 :=
  SparseEncoding.vectorPolynomial_coeff _ _ _

theorem signWord_degree (n : ℕ) : (signWord n).degree < n := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro i hi
  simp [not_lt.mpr hi]

/-- The sign-word translation encoding the affine offset. -/
noncomputable def packingTranslation (q : AffineInput) : ℤ[X] :=
  signWord (2*q.1) - C 2 * listPolynomial q.2.2.2

/-- Zero-padded specialization of principal-coset packing. Zero coordinates
are allowed in the language, so geometric repetition is unnecessary here.
The construction uses only bounded list loops and integer operations. -/
def packCoset (D : ℕ) (q : AffineInput) : CosetInput :=
  (D, ((List.range D).map (fun i => 2*((if i = q.1 then 1 else 0) + q.2.2.1.getD i 0)),
    (List.range D).map (fun i => (if i < 2*q.1 then 1 else 0) - 2*q.2.2.2.getD i 0)))

theorem packCoset_coefficients (D : ℕ) (q : AffineInput) :
    IdealCVP.ofList (d := D) (packCoset D q).2.1 =
      (2 : ℤ) • polynomialCoeffs D (affineW q) ∧
    IdealCVP.ofList (d := D) (packCoset D q).2.2 =
      polynomialCoeffs D (packingTranslation q) := by
  constructor <;> ext i
  · simp [packCoset, IdealCVP.ofList, List.getD_eq_getElem?_getD, i.isLt,
      polynomialCoeffs, affineW, listPolynomial_coeff, coeff_X_pow, eq_comm]
  · simp [packCoset, IdealCVP.ofList, List.getD_eq_getElem?_getD, i.isLt,
      polynomialCoeffs, packingTranslation, listPolynomial_coeff]

theorem packCoset_alphabet (q : AffineInput) (hq : q.WellFormed) (D : ℕ) :
    (∀ i : Fin D, IdealCVP.ofList (packCoset D q).2.1 i = 0 ∨
      IdealCVP.ofList (packCoset D q).2.1 i = 2) ∧
    (∀ i : Fin D, IdealCVP.ofList (packCoset D q).2.2 i = -1 ∨
      IdealCVP.ofList (packCoset D q).2.2 i = 0 ∨
      IdealCVP.ofList (packCoset D q).2.2 i = 1 ∨
      IdealCVP.ofList (packCoset D q).2.2 i = 3) := by
  rw [(packCoset_coefficients D q).1, (packCoset_coefficients D q).2]
  have hPL : (listPolynomial q.2.2.1).coeff q.1 = 0 := by
    apply (degree_lt_iff_coeff_zero _ (q.2.1+1)).mp
      (by simpa [hq.P_length] using listPolynomial_degree q.2.2.1)
    have := hq.scale
    omega
  constructor
  · intro i
    simp only [Pi.smul_apply, smul_eq_mul, polynomialCoeffs, affineW, coeff_add, coeff_X_pow]
    by_cases hi : i.val = q.1
    · simp [hi, hPL]
    · rcases hq.P_bit i.val with hp | hp <;> simp [hi, hp]
  · intro i
    simp only [polynomialCoeffs, packingTranslation, coeff_sub, signWord_coeff, coeff_C_mul]
    by_cases hi : i.val < 2*q.1
    · rcases hq.c_ternary i.val with hc | hc | hc <;> simp [hi, hc]
    · have hc : (listPolynomial q.2.2.2).coeff i.val = 0 := by
        apply (degree_lt_iff_coeff_zero _ q.1).mp
          (by simpa [hq.c_length] using listPolynomial_degree q.2.2.2)
        omega
      simp [hi, hc]

theorem packCoset_wellFormed (q : AffineInput) (hq : q.WellFormed)
    (D : ℕ) (hDy : Dyadic D) (_hD : 16 * q.1 ^ 3 ≤ D) :
    (packCoset D q).WellFormed := by
  refine ⟨hDy, by simp [packCoset], by simp [packCoset], ?_, ?_⟩
  · change IdealCVP.ofList (d := D) (packCoset D q).2.1 ≠ 0
    rw [(packCoset_coefficients D q).1]
    intro hz
    have hh := congrFun hz ⟨0,hDy.pos⟩
    have hw0 : (affineW q).coeff 0 = 1 := by
      have hL : q.1 ≠ 0 := by have := hq.L_large; omega
      simp [affineW, Ne.symm hL, hq.P_zero]
    simp [polynomialCoeffs, hw0] at hh
  · change EvenCoeffs (IdealCVP.ofList (d := D) (packCoset D q).2.1)
    rw [(packCoset_coefficients D q).1]
    intro i
    exact ⟨(affineW q).coeff i.val, by simp [polynomialCoeffs, two_mul]⟩

/-- Bounded polynomial remainders decoded from bits lie within the separation
height budget, including the translation and the output bit. -/
theorem affine_error_bound {q : AffineInput} (hq : q.WellFormed)
    {x y : ℤ[X]} (hx : SparseEncoding.BitPolynomial q.1 x)
    (hy : SparseEncoding.BitPolynomial q.1 y) :
    CoefficientBound ((listPolynomial q.2.2.1*x) %ₘ affineW q +
      listPolynomial q.2.2.2 - y) (q.1^2) := by
  have hb := affine_remainder_height hq hx
  intro n
  have hc : |(listPolynomial q.2.2.2).coeff n| ≤ 1 := by
    rcases hq.c_ternary n with h | h | h <;> simp [h]
  have hyb : |y.coeff n| ≤ 1 := by rcases hy.2 n with h | h <;> simp [h]
  simp only [coeff_sub, coeff_add]
  calc
    _ ≤ |((listPolynomial q.2.2.1*x) %ₘ affineW q).coeff n| +
        |(listPolynomial q.2.2.2).coeff n| + |y.coeff n| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      have h := hb n
      have hT := hq.T_pos
      have hL := hq.scale
      have h64 := hq.L_large
      push_cast at *
      nlinarith

/-- A polynomial with two consecutive sign words decodes into two bit words. -/
noncomputable def decodedWord (L offset : ℕ) (p : ℤ[X]) : ℤ[X] :=
  SparseEncoding.vectorPolynomial L (fun n => (1-p.coeff (offset+n))/2)

theorem decodedWord_bit {L offset : ℕ} {p : ℤ[X]}
    (hp : ∀ n < L, p.coeff (offset + n) = -1 ∨ p.coeff (offset + n) = 1) :
    SparseEncoding.BitPolynomial L (decodedWord L offset p) := by
  apply SparseEncoding.vectorPolynomial_bit
  intro n hn
  rcases hp n hn with h | h <;> simp [h]

theorem decode_two_words {L : ℕ} {p : ℤ[X]} (hp : p.degree < ((2 * L : ℕ) : WithBot ℕ))
    (hs : ∀ n < 2 * L, p.coeff n = -1 ∨ p.coeff n = 1) :
    p = signWord (2*L) - C 2 * (decodedWord L 0 p + X^L * decodedWord L L p) := by
  ext n
  simp only [coeff_sub, signWord_coeff, coeff_C_mul, coeff_add, coeff_X_pow_mul',
    decodedWord, SparseEncoding.vectorPolynomial_coeff, zero_add]
  by_cases hn : n < L
  · have hs' := hs n (by omega)
    rcases hs' with h | h <;> simp [hn, show n < 2*L by omega,
      show ¬L ≤ n by omega, h]
  · by_cases hn2 : n < 2*L
    · have hs' := hs n hn2
      have he : L+(n-L) = n := by omega
      rcases hs' with h | h <;> simp [hn,hn2,show L ≤ n by omega,
        show n-L < L by omega, he, h]
    · have hz := (degree_lt_iff_coeff_zero _ (2*L)).mp hp n (by omega)
      simp [hn,hn2,show L ≤ n by omega,show ¬n-L < L by omega,hz]

/-- The error has a lift in the separation ideal whenever the decoded
pre-remainder equation holds in the negacyclic ring. -/
theorem affine_error_congruence {q : AffineInput} {D : ℕ}
    (x y : ℤ[X]) (u : Coeff D)
    (heq : AdjoinRoot.mk (modulus D) (listPolynomial q.2.2.2 - y - X ^ q.1 * x) =
      AdjoinRoot.mk (modulus D) (affineW q) * toQuot u) :
    SeparationCongruence (affineW q)
      ((listPolynomial q.2.2.1*x) %ₘ affineW q + listPolynomial q.2.2.2-y) D := by
  have heq' : AdjoinRoot.mk (modulus D) (listPolynomial q.2.2.2-y-X^q.1*x) =
      AdjoinRoot.mk (modulus D) (affineW q * coefficientPolynomial u) := by
    have hu : toQuot u = AdjoinRoot.mk (modulus D) (coefficientPolynomial u) :=
      toQuot_eq_mk u
    simpa only [map_mul, ← hu] using heq
  obtain ⟨b,hb⟩ := AdjoinRoot.mk_eq_mk.mp heq'
  refine ⟨b, coefficientPolynomial u + x -
    (listPolynomial q.2.2.1*x) /ₘ affineW q, ?_⟩
  change _ = (1+X^D)*b + affineW q * _
  rw [modByMonic_eq_sub_mul_div]
  dsimp [modulus, affineW] at hb ⊢
  linear_combination hb

theorem packing_large_degree {L D : ℕ} (hL : 64 ≤ L) (hD : 16 * L ^ 3 ≤ D) :
    2*L < D := by nlinarith [sq_nonneg (L-1 : ℤ)]

theorem affineRaw_degree {q : AffineInput} (hq : q.WellFormed)
    {x y : ℤ[X]} (hx : x.degree < q.1) (hy : y.degree < q.1) :
    (listPolynomial q.2.2.2-y-X^q.1*x).degree < ((2*q.1 : ℕ) : WithBot ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro n hn
  have hc := (degree_lt_iff_coeff_zero _ q.1).mp
    (by simpa [hq.c_length] using listPolynomial_degree q.2.2.2) n (by omega)
  have hy0 := (degree_lt_iff_coeff_zero _ q.1).mp hy n (by omega)
  have hx0 := (degree_lt_iff_coeff_zero _ q.1).mp hx (n-q.1) (by omega)
  simp [coeff_X_pow_mul', show q.1 ≤ n by omega, hc, hy0, hx0]

theorem packingTranslation_degree {q : AffineInput} (hq : q.WellFormed) :
    (packingTranslation q).degree < ((2*q.1 : ℕ) : WithBot ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro n hn
  have hc := (degree_lt_iff_coeff_zero _ q.1).mp
    (by simpa [hq.c_length] using listPolynomial_degree q.2.2.2) n (by omega)
  simp [packingTranslation, not_lt.mpr hn, hc]

theorem packingW_degree {q : AffineInput} (hq : q.WellFormed) {D : ℕ}
    (hD : 2 * q.1 < D) : (affineW q).degree < D := by
  rw [degree_eq_natDegree (affineW_monic hq).ne_zero, affineW_natDegree hq]
  exact_mod_cast (show q.1 < D by omega)

theorem toQuot_two_polynomialCoeffs {d : ℕ} {p : ℤ[X]} (hp : p.degree < d) :
    toQuot ((2 : ℤ) • polynomialCoeffs d p) =
      AdjoinRoot.mk (modulus d) (C 2*p) := by
  have he : (2 : ℤ) • polynomialCoeffs d p = polynomialCoeffs d (C 2*p) := by
    ext i
    simp [polynomialCoeffs]
  rw [he, toQuot_polynomialCoeffs (by
    apply (degree_lt_iff_coeff_zero _ _).mpr
    intro n hn
    simp [(degree_lt_iff_coeff_zero _ _).mp hp n hn])]

/-- Completeness uses only integral monic division, not separation. -/
theorem packCoset_complete (q : AffineInput) (hq : q.WellFormed)
    (D : ℕ) (hDy : Dyadic D) (hD : 16 * q.1 ^ 3 ≤ D) :
    AffineYes q → packCoset D q ∈ CosetLang := by
  intro hs
  refine ⟨packCoset_wellFormed q hq D hDy hD, ?_⟩
  change CosetYes (IdealCVP.ofList (d := D) (packCoset D q).2.1)
    (IdealCVP.ofList (d := D) (packCoset D q).2.2)
  obtain ⟨x,y,hx,hy,he⟩ := hs
  have hLD := packing_large_degree hq.L_large hD
  let V := signWord (2*q.1)-C 2*(y+X^q.1*x)
  have hVdeg : V.degree < ((2*q.1 : ℕ) : WithBot ℕ) := by
    apply (degree_lt_iff_coeff_zero _ _).mpr
    intro n hn
    have hy0 := (degree_lt_iff_coeff_zero _ q.1).mp hy.1 n (by omega)
    have hx0 := (degree_lt_iff_coeff_zero _ q.1).mp hx.1 (n-q.1) (by omega)
    simp [V,coeff_X_pow_mul',show q.1 ≤ n by omega,not_lt.mpr hn,hy0,hx0]
  have hVcube : Cube (polynomialCoeffs D V) := by
    intro i
    simp only [polynomialCoeffs, V, coeff_sub, signWord_coeff, coeff_C_mul,
      coeff_add, coeff_X_pow_mul']
    by_cases hi : i.val < q.1
    · have hx0 : ¬q.1 ≤ i.val := by omega
      rcases hy.2 i.val with h | h <;> simp [hx0, show i.val < 2 * q.1 by omega, h]
    · by_cases hi2 : i.val < 2*q.1
      · have hy0 := (degree_lt_iff_coeff_zero _ q.1).mp hy.1 i.val (by omega)
        rcases hx.2 (i.val-q.1) with h | h <;>
          simp [hi2,show q.1 ≤ i.val by omega,hy0,h]
      · have hy0 := (degree_lt_iff_coeff_zero _ q.1).mp hy.1 i.val (by omega)
        have hx0 := (degree_lt_iff_coeff_zero _ q.1).mp hx.1 (i.val-q.1) (by omega)
        simp [hi2,show q.1 ≤ i.val by omega,hy0,hx0]
  let U := (listPolynomial q.2.2.1*x) /ₘ affineW q - x
  have hraw : listPolynomial q.2.2.2-y-X^q.1*x = affineW q * U := by
    rw [he, modByMonic_eq_sub_mul_div]
    dsimp [U,affineW]
    ring
  obtain ⟨u,hu⟩ := (toQuot_bijective hDy.pos).surjective
    (AdjoinRoot.mk (modulus D) U)
  refine ⟨u, ?_⟩
  have hv : IdealCVP.ofList (d := D) (packCoset D q).2.2 +
      IdealCVP.Cyclotomic.mul (IdealCVP.ofList (d := D) (packCoset D q).2.1) u =
      polynomialCoeffs D V := by
    apply (toQuot_bijective hDy.pos).injective
    rw [toQuot_add, toQuot_mul hDy.pos,
      (packCoset_coefficients D q).1, (packCoset_coefficients D q).2,
      toQuot_polynomialCoeffs ((packingTranslation_degree hq).trans (by exact_mod_cast hLD)),
      toQuot_two_polynomialCoeffs (packingW_degree hq hLD), hu,
      toQuot_polynomialCoeffs (hVdeg.trans (by exact_mod_cast hLD)), ← map_mul, ← map_add]
    congr 1
    calc
      packingTranslation q + C 2*affineW q*U =
          packingTranslation q + C 2*(listPolynomial q.2.2.2-y-X^q.1*x) := by
        rw [_root_.mul_assoc, ← hraw]
      _ = V := by dsimp [V,packingTranslation]; ring
  rwa [hv]

/-- Soundness exposes exactly the existing norm-separation hypothesis. -/
theorem packCoset_sound (hSep : NormSeparationHypothesis)
    (q : AffineInput) (hq : q.WellFormed)
    (D : ℕ) (hDy : Dyadic D) (hD : 16 * q.1 ^ 3 ≤ D) :
    packCoset D q ∈ CosetLang → AffineYes q := by
  intro hmem
  change (packCoset D q).WellFormed ∧
    CosetYes (IdealCVP.ofList (d := D) (packCoset D q).2.1)
      (IdealCVP.ofList (d := D) (packCoset D q).2.2) at hmem
  obtain ⟨_,u,hcube⟩ := hmem
  have hLD := packing_large_degree hq.L_large hD
  let W := polynomialCoeffs D (affineW q)
  let H := polynomialCoeffs D (packingTranslation q)
  let E := H + (2 : ℤ) • IdealCVP.Cyclotomic.mul W u
  have hE : Cube E := by
    dsimp [E,H,W]
    simpa only [(packCoset_coefficients D q).1,
      (packCoset_coefficients D q).2, mul_smul_left] using hcube
  let p := coefficientPolynomial E
  have hpcoeff (n : ℕ) (hn : n < D) :
      p.coeff n = (if n < 2*q.1 then 1 else 0) -
        2*(listPolynomial q.2.2.2).coeff n +
        2*IdealCVP.Cyclotomic.mul W u ⟨n,hn⟩ := by
    simp [p, coefficientPolynomial_coeff, hn, E, H, polynomialCoeffs,packingTranslation]
  have hs : ∀ n < 2*q.1, p.coeff n = -1 ∨ p.coeff n = 1 := by
    intro n hn
    have hnD : n < D := by omega
    have hb := abs_le.mp (hE ⟨n,hnD⟩)
    have hc := hpcoeff n hnD
    have hpc : p.coeff n = E ⟨n,hnD⟩ := by simp [p,coefficientPolynomial_coeff,hnD]
    rw [ite_eq_left hn] at hc
    omega
  have hpdeg : p.degree < ((2*q.1 : ℕ) : WithBot ℕ) := by
    apply (degree_lt_iff_coeff_zero _ _).mpr
    intro n hn
    by_cases hnD : n < D
    · have hb := abs_le.mp (hE ⟨n,hnD⟩)
      have hc := hpcoeff n hnD
      have hpc : p.coeff n = E ⟨n,hnD⟩ := by simp [p,coefficientPolynomial_coeff,hnD]
      have hc0 := (degree_lt_iff_coeff_zero _ q.1).mp
        (by simpa [hq.c_length] using listPolynomial_degree q.2.2.2) n (by omega)
      rw [ite_eq_right (by omega),hc0] at hc
      omega
    · simp [p,coefficientPolynomial_coeff,hnD]
  let x := decodedWord q.1 q.1 p
  let y := decodedWord q.1 0 p
  have hx : SparseEncoding.BitPolynomial q.1 x :=
    decodedWord_bit (fun n hn => hs _ (by omega))
  have hy : SparseEncoding.BitPolynomial q.1 y :=
    decodedWord_bit (fun n hn => by simpa using hs n (by omega))
  have hdecode := decode_two_words hpdeg hs
  change p = signWord (2*q.1)-C 2*(y+X^q.1*x) at hdecode
  let r := listPolynomial q.2.2.2-y-X^q.1*x
  have hr : r.degree < D :=
    (affineRaw_degree hq hx.1 hy.1).trans (by exact_mod_cast hLD)
  have hid : C 2*r = p-packingTranslation q := by
    rw [hdecode]
    dsimp [r,packingTranslation]
    ring
  have hc : polynomialCoeffs D r = IdealCVP.Cyclotomic.mul W u := by
    ext i
    have he := congrArg (fun a : ℤ[X] => a.coeff i.val) hid
    have hp := hpcoeff i.val i.isLt
    simp only [coeff_C_mul, coeff_sub] at he
    change r.coeff i.val = _
    simp only [packingTranslation,coeff_sub,signWord_coeff,coeff_C_mul] at he
    change p.coeff i.val = (if i.val < 2*q.1 then 1 else 0) -
      2*(listPolynomial q.2.2.2).coeff i.val + 2*IdealCVP.Cyclotomic.mul W u i at hp
    linarith only [he,hp]
  have hquot : AdjoinRoot.mk (modulus D) r =
      AdjoinRoot.mk (modulus D) (affineW q) * toQuot u := by
    rw [← toQuot_polynomialCoeffs hr, hc, toQuot_mul hDy.pos,
      toQuot_polynomialCoeffs (packingW_degree hq hLD)]
  have herrdeg : ((listPolynomial q.2.2.1*x) %ₘ affineW q +
      listPolynomial q.2.2.2-y).degree < q.1 := by
    apply (degree_lt_iff_coeff_zero _ _).mpr
    intro n hn
    have hc0 := (degree_lt_iff_coeff_zero _ q.1).mp
      (by simpa [hq.c_length] using listPolynomial_degree q.2.2.2) n hn
    have hy0 := (degree_lt_iff_coeff_zero _ q.1).mp hy.1 n hn
    have hr0 := (degree_lt_iff_coeff_zero _ q.1).mp
      (by simpa only [degree_eq_natDegree (affineW_monic hq).ne_zero,
        affineW_natDegree hq] using
          degree_modByMonic_lt (listPolynomial q.2.2.1*x) (affineW_monic hq)) n hn
    simp [hr0,hc0,hy0]
  have hzero := elementary_separation hSep (affineW_monic hq) (affineW_natDegree hq)
    (affineW_unit hq) hq.root hq.L_large hD herrdeg (affine_error_bound hq hx hy)
    (affine_error_congruence x y u hquot)
  exact ⟨x,y,hx,hy,(sub_eq_zero.mp hzero).symm⟩

/-- Semantic principal-coset reduction, with coefficient promises and validity
proved independently of separation. -/
theorem packCoset_correct (hSep : NormSeparationHypothesis)
    (q : AffineInput) (hq : q.WellFormed)
    (D : ℕ) (hDy : Dyadic D) (hD : 16 * q.1 ^ 3 ≤ D) :
    AffineYes q ↔ packCoset D q ∈ CosetLang :=
  ⟨packCoset_complete q hq D hDy hD, packCoset_sound hSep q hq D hDy hD⟩

/-- Finite-data adapter from the existing source. It reads the exponent set,
not the noncomputable polynomial interpretation. -/
def sourceToAffine (s : SparseEncoding.EncodedSource) : AffineInput :=
  (s.dimension, (s.degreeBound,
    ((List.range (s.degreeBound+1)).map (fun n => if n ∈ s.exponents then 1 else 0),s.offset)))

theorem sourceToAffine_P {v r : ℕ} (C : SparseEncoding.Clauses v r) :
    listPolynomial (sourceToAffine (SparseEncoding.encode C)).2.2.1 =
      SparseEncoding.P C (SparseEncoding.positionPrime v) := by
  ext n
  have hp := SparseEncoding.positionPrime_spec v
  rw [listPolynomial_coeff, SparseEncoding.coeff_P]
  by_cases hn : n < SparseEncoding.T (SparseEncoding.positionPrime v) v r+1
  · simp [sourceToAffine,SparseEncoding.encode,List.getD_eq_getElem?_getD,hn]
  · have hout : n ∉ SparseEncoding.support C (SparseEncoding.positionPrime v) := by
      intro hm
      have hb := SparseEncoding.support_bounds C hp.1.pos hm
      omega
    simp [sourceToAffine,SparseEncoding.encode,List.getD_eq_getElem?_getD,hn,hout]

theorem sourceToAffine_c_coeff {v r : ℕ} (C : SparseEncoding.Clauses v r) (n : ℕ) :
    (listPolynomial (sourceToAffine (SparseEncoding.encode C)).2.2.2).coeff n =
      if n < SparseEncoding.L (SparseEncoding.positionPrime v) v r then
        SparseEncoding.translation C (SparseEncoding.positionPrime v) n else 0 := by
  rw [listPolynomial_coeff]
  by_cases hn : n < SparseEncoding.L (SparseEncoding.positionPrime v) v r
  · simp [sourceToAffine,SparseEncoding.encode,List.getD_eq_getElem?_getD,hn]
  · simp [sourceToAffine,SparseEncoding.encode,List.getD_eq_getElem?_getD,hn]

/-- Bridge from the source's rational reciprocal statement to the norm API. -/
theorem source_modulus_noCommonRoot {v r : ℕ} (C : SparseEncoding.Clauses v r)
    {ell : ℕ} (hell : 0 < ell) :
    NoCommonReciprocalRoot (X^(SparseEncoding.L ell v r)+SparseEncoding.P C ell) := by
  let w : ℤ[X] := X^(SparseEncoding.L ell v r)+SparseEncoding.P C ell
  have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ :=
    Subsingleton.elim _ _
  have hev (a : ℤ[X]) (z : ℂ) :
      aeval z (a.map (Int.castRingHom ℚ)) = (complexPolynomial a).eval z := by
    simp only [aeval_def,eval₂_map,hcomp,complexPolynomial,eval_map]
  have hmap : Sidon.modulus (SparseEncoding.rationalP C ell)
      (SparseEncoding.L ell v r) = w.map (Int.castRingHom ℚ) := by
    simp [w,Sidon.modulus,SparseEncoding.rationalP]
  have hd : (w.map (Int.castRingHom ℚ)).natDegree = w.natDegree :=
    natDegree_map_eq_of_injective (Int.cast_injective) w
  have hreverse : (w.map (Int.castRingHom ℚ)).reverse =
      w.reverse.map (Int.castRingHom ℚ) := by
    simp only [reverse,hd,reflect_map]
  intro z hz hr
  apply SparseEncoding.encoding_no_common_root C hell z
  rw [hmap,hreverse,hev,hev]
  exact ⟨hz,hr⟩

theorem sourceToAffine_wellFormed {v r : ℕ} (C : SparseEncoding.Clauses v r)
    (hL : 64 ≤ SparseEncoding.L (SparseEncoding.positionPrime v) v r) :
    (sourceToAffine (SparseEncoding.encode C)).WellFormed := by
  have hp := SparseEncoding.positionPrime_spec v
  refine ⟨by simp [sourceToAffine,SparseEncoding.encode],
    by simp [sourceToAffine,SparseEncoding.encode],
    SparseEncoding.T_pos _ _ _, hL, (SparseEncoding.L_spec _ _ _).1,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sourceToAffine_P]
    exact SparseEncoding.coeff_P_bit _ _
  · rw [sourceToAffine_P]
    exact SparseEncoding.constant_coeff _ _
  · rw [sourceToAffine_P]
    exact SparseEncoding.leading_coeff _ _
  · rw [sourceToAffine_P]
    exact SparseEncoding.P_reciprocal _ hp.1.pos
  · intro n
    rw [sourceToAffine_c_coeff]
    split_ifs
    · exact SparseEncoding.translation_alphabet _ _ _
    · simp
  · unfold affineW
    rw [sourceToAffine_P]
    exact source_modulus_noCommonRoot C hp.1.pos

theorem sourceToAffine_correct {v r : ℕ} (C : SparseEncoding.Clauses v r) :
    (∃ x y, SparseEncoding.AffineSolution C (SparseEncoding.positionPrime v) x y) ↔
      AffineYes (sourceToAffine (SparseEncoding.encode C)) := by
  have hp := SparseEncoding.positionPrime_spec v
  have hdim : (sourceToAffine (SparseEncoding.encode C)).1 =
      SparseEncoding.L (SparseEncoding.positionPrime v) v r := rfl
  have hmon : (X^SparseEncoding.L (SparseEncoding.positionPrime v) v r+
      SparseEncoding.P C (SparseEncoding.positionPrime v)).Monic := by
    apply monic_X_pow_add
    apply degree_le_natDegree.trans_lt
    rw [SparseEncoding.degree_P C hp.1.pos]
    exact_mod_cast (show SparseEncoding.T (SparseEncoding.positionPrime v) v r <
      SparseEncoding.L (SparseEncoding.positionPrime v) v r by
        have := (SparseEncoding.L_spec (SparseEncoding.positionPrime v) v r).1; omega)
  have hwdeg : (X^SparseEncoding.L (SparseEncoding.positionPrime v) v r+
      SparseEncoding.P C (SparseEncoding.positionPrime v)).natDegree =
      SparseEncoding.L (SparseEncoding.positionPrime v) v r := by
    rw [natDegree_add_eq_left_of_natDegree_lt (by
      rw [SparseEncoding.degree_P C hp.1.pos, natDegree_X_pow]
      have := (SparseEncoding.L_spec (SparseEncoding.positionPrime v) v r).1; omega),
      natDegree_X_pow]
  constructor
  · rintro ⟨x,y,hx,hy,he⟩
    refine ⟨x,y,hx,hy,?_⟩
    rw [sourceToAffine_P]
    unfold affineW
    rw [sourceToAffine_P]
    ext n
    by_cases hn : n < SparseEncoding.L (SparseEncoding.positionPrime v) v r
    · simpa [coeff_add,sourceToAffine_c_coeff,hn,hdim] using he n hn
    · have hy0 := (degree_lt_iff_coeff_zero _ _).mp hy.1 n (by omega)
      have hr0 := (degree_lt_iff_coeff_zero _ _).mp
        (by simpa only [degree_eq_natDegree hmon.ne_zero,hwdeg] using
          degree_modByMonic_lt (SparseEncoding.P C (SparseEncoding.positionPrime v)*x) hmon)
          n (by omega : SparseEncoding.L (SparseEncoding.positionPrime v) v r ≤ n)
      simp only [coeff_add,sourceToAffine_c_coeff,ite_eq_right hn,add_zero]
      exact hy0.trans hr0.symm
  · rintro ⟨x,y,hx,hy,he⟩
    refine ⟨x,y,hx,hy,fun n hn => ?_⟩
    have hc := congrArg (fun p : ℤ[X] => p.coeff n) he
    simpa [affineW,sourceToAffine_P,coeff_add,sourceToAffine_c_coeff,hn,hdim] using hc

/-- The original total 3SAT normalization and Sidon source are imported. -/
def threeSATToAffine (f : Cslib.Logic.PL.CNF ℕ) : AffineInput :=
  sourceToAffine (BooleanSource.threeSATEncode f)

theorem threeSATToAffine_wellFormed (f : Cslib.Logic.PL.CNF ℕ) :
    (threeSATToAffine f).WellFormed :=
  sourceToAffine_wellFormed _ (BooleanSource.boolean_source_dimension
    (BooleanSource.fromThreeSAT f).formula)

theorem threeSATToAffine_correct (f : Cslib.Logic.PL.CNF ℕ) :
    f ∈ Cslib.Complexity.ThreeSAT ↔ AffineYes (threeSATToAffine f) :=
  (BooleanSource.threeSAT_affine_correct f).trans (sourceToAffine_correct _)

/-- A total explicit coset map at the least dyadic cubic degree. -/
def threeSATToCoset (f : Cslib.Logic.PL.CNF ℕ) : CosetInput :=
  let q := threeSATToAffine f
  packCoset (packingDegree q.1) q

theorem threeSATToCoset_correct (hSep : NormSeparationHypothesis)
    (f : Cslib.Logic.PL.CNF ℕ) :
    f ∈ Cslib.Complexity.ThreeSAT ↔ threeSATToCoset f ∈ CosetLang :=
  (threeSATToAffine_correct f).trans
    (packCoset_correct hSep _ (threeSATToAffine_wellFormed f) _
      (dyadicCeil_dyadic _) (le_dyadicCeil _))

theorem packingDegree_lt {L : ℕ} (hL : 0 < L) : packingDegree L < 32*L^3 := by
  have h := dyadicCeil_lt_twice (by positivity : 0 < 16*L^3)
  dsimp [packingDegree]
  omega

theorem modulePackingDegree_dyadic (k0 L : ℕ) : Dyadic (modulePackingDegree k0 L) := by
  unfold modulePackingDegree
  rcases le_total (2^k0) (packingDegree L) with h | h
  · rw [max_eq_right h]
    exact dyadicCeil_dyadic _
  · rw [max_eq_left h]
    exact ⟨k0,rfl⟩

theorem modulePackingDegree_large (k0 L : ℕ) :
    16*L^3 ≤ modulePackingDegree k0 L :=
  (le_dyadicCeil _).trans (Nat.le_max_right _ _)

theorem modulePackingDegree_cutoff (k0 L : ℕ) : 2^k0 ≤ modulePackingDegree k0 L :=
  Nat.le_max_left _ _

theorem modulePackingDegree_lt {L : ℕ} (k0 : ℕ) (hL : 0 < L) :
    modulePackingDegree k0 L < 2^k0+32*L^3 := by
  apply max_lt
  · have : 0 < 32*L^3 := by positivity
    omega
  · exact (packingDegree_lt hL).trans_le (Nat.le_add_left _ _)

/-- Compatibility with the shared coefficient-vector bit predicate. -/
theorem bits_coefficientPolynomial {L : ℕ} {x : Coeff L} (hx : Bits x) :
    SparseEncoding.BitPolynomial L (coefficientPolynomial x) := by
  refine ⟨coefficientPolynomial_degree x, fun n => ?_⟩
  rw [coefficientPolynomial_coeff]
  split_ifs with hn
  · exact hx ⟨n,hn⟩
  · exact Or.inl rfl

/-- The polynomial source contract is exactly the coefficient-vector contract
from PLAN section 4. No assumption on the raw data is needed for this bridge. -/
theorem affineYes_iff_coefficients (q : AffineInput) :
    AffineYes q ↔ ∃ x y : Coeff q.1, Bits x ∧ Bits y ∧
      coefficientPolynomial y =
        (listPolynomial q.2.2.1 * coefficientPolynomial x) %ₘ affineW q +
          listPolynomial q.2.2.2 := by
  constructor
  · rintro ⟨x,y,hx,hy,he⟩
    refine ⟨polynomialCoeffs q.1 x,polynomialCoeffs q.1 y,
      (fun i => hx.2 i.val),(fun i => hy.2 i.val),?_⟩
    rwa [coefficientPolynomial_polynomialCoeffs hx.1,
      coefficientPolynomial_polynomialCoeffs hy.1]
  · rintro ⟨x,y,hx,hy,he⟩
    exact ⟨coefficientPolynomial x,coefficientPolynomial y,
      bits_coefficientPolynomial hx,bits_coefficientPolynomial hy,he⟩

end Power2ModuleSVP
