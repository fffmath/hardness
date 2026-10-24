import Rank2ModuleSVP.MembershipCert
import Rank2ModuleSVP.Checker
import Rank2ModuleSVP.RobustCenter

/-! Executable power-basis arithmetic and the fixed outputs of v2 §5.3. -/
namespace Rank2ModuleSVP
namespace ReductionMap
open scoped BigOperators
open Rank2ModuleSVP.Membership
attribute [local irreducible] List.getD
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A cyclic single coefficient, converted by subtracting coefficient `q-1`. -/
def atom {q : ℕ} [NeZero q] (e : ZMod q) (c : ℤ) : List ℤ :=
  Rank2ModuleSVP.Membership.repr (fun a => if a = e then c else 0)

def scalar {q : ℕ} [NeZero q] (c : ℤ) : List ℤ := atom (q := q) 0 c

@[simp] theorem length_atom {q : ℕ} [NeZero q] (e : ZMod q) (c : ℤ) :
    (atom e c).length = q-1 := length_repr _

@[simp] theorem powerElement_scalar {q : ℕ} [NeZero q] (c : ℤ) :
    powerElement (scalar (q := q) c) = (c : IntegerRing q) := by
  rw [scalar, atom, powerElement_repr, classOf_single_zero]

@[simp] theorem powerElement_atom {q : ℕ} [NeZero q] (e : ZMod q) :
    powerElement (atom e 1) = (monomial e : IntegerRing q) := by
  rw [atom, powerElement_repr]
  unfold classOf monomial
  congr 1
  ext a
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm]

/-- Total natural-index implementation of a cyclic single coefficient. -/
def singleList (q r : ℕ) (c : ℤ) : List ℤ :=
  (List.range (q-1)).map fun i =>
    (if i = r%q then c else 0) - (if q-1 = r%q then c else 0)

/-- The natural-index implementation is precisely cyclic-to-power-basis conversion. -/
theorem singleList_eq_atom {q : ℕ} [NeZero q] (e : ZMod q) (c : ℤ) :
    singleList q e.val c = atom e c := by
  unfold singleList atom Rank2ModuleSVP.Membership.repr
  apply List.map_congr_left
  intro i hi
  have hq := NeZero.pos q
  have hiq : i < q := by have := List.mem_range.mp hi; omega
  have hlast : q-1 < q := by omega
  have he (j : ℕ) (hj : j < q) : ((j : ZMod q) = e) ↔ j = e.val := by
    constructor
    · intro h
      simpa only [ZMod.val_natCast_of_lt hj] using congrArg ZMod.val h
    · intro h
      rw [h, ZMod.natCast_zmod_val]
  simp only [Nat.mod_eq_of_lt e.val_lt, he i hiq, he (q-1) hlast]

/-- Repeated squaring is unnecessary here: the exponent is polynomial in the input length. -/
def ringPow (q : ℕ) [NeZero q] (a : List ℤ) : ℕ → List ℤ
  | 0 => scalar (q := q) 1
  | n+1 => mul q (ringPow q a n) a

@[simp] theorem length_ringPow (q : ℕ) [NeZero q] (a : List ℤ) (n : ℕ) :
    (ringPow q a n).length = q-1 := by cases n <;> simp [ringPow, scalar]

@[simp] theorem powerElement_ringPow (q : ℕ) [NeZero q] (a : List ℤ) (n : ℕ) :
    powerElement (q := q) (ringPow q a n) = powerElement (q := q) a ^ n := by
  induction n with
  | zero => simp [ringPow]
  | succ n ih => simp [ringPow, powerElement_mul, ih, pow_succ]

/-- Coordinatewise list summation, with a normalized zero for the empty list. -/
def sumLists (q : ℕ) (as : List (List ℤ)) : List ℤ :=
  (List.range (q-1)).map fun i => (as.map fun a => coeff q a i).sum

@[simp] theorem length_sumLists (q : ℕ) (as : List (List ℤ)) :
    (sumLists q as).length = q-1 := by simp [sumLists]

private theorem sumLists_cons (q : ℕ) (a : List ℤ) (as : List (List ℤ)) :
    sumLists q (a::as) = add q a (sumLists q as) := by
  unfold sumLists add IdealCVP.listAdd
  apply List.map_congr_left
  intro i hi
  have hi' : i < q-1 := List.mem_range.mp hi
  simp only [List.map_cons, List.sum_cons, coeff,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
    hi', ite_true, Option.map_some, Option.getD_some]

@[simp] theorem powerElement_sumLists (q : ℕ) [NeZero q] (as : List (List ℤ)) :
    powerElement (q := q) (sumLists q as) = (as.map (powerElement (q := q))).sum := by
  induction as with
  | nil =>
    have he : sumLists q [] = scalar (q := q) 0 := by
      simp [sumLists, scalar, atom, Rank2ModuleSVP.Membership.repr]
    simp [he]
  | cons a as ih => rw [sumLists_cons, powerElement_add, ih]; rfl

/-- Padded coefficient lookup preserves any nonnegative absolute coefficient bound. -/
theorem coeff_abs_bound (q : ℕ) (a : List ℤ) (A : ℤ) (hA : 0 ≤ A)
    (ha : ∀ z ∈ a, |z| ≤ A) (i : ℕ) : |coeff q a i| ≤ A := by
  unfold coeff
  split_ifs
  · rw [List.getD_eq_getElem?_getD]
    cases he : a[i]? with
    | none => simpa using hA
    | some z => simpa using ha z (List.mem_of_getElem? he)
  · simpa using hA

/-- One cyclic convolution increases magnitude by at most a factor `q`. -/
theorem cyclicCoeff_abs_bound (q : ℕ) (a b : List ℤ) (A B : ℤ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : ∀ z ∈ a, |z| ≤ A)
    (hb : ∀ z ∈ b, |z| ≤ B) (r : ℕ) : |cyclicCoeff q a b r| ≤ (q : ℤ)*A*B := by
  rw [cyclicCoeff, IdealCVP.list_sum_range]
  calc
    _ ≤ ∑ i ∈ Finset.range q, |coeff q a i * coeff q b ((r+q-i)%q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range q, A*B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (coeff_abs_bound q a A hA ha i)
        (coeff_abs_bound q b B hB hb _) (abs_nonneg _) hA
    _ = _ := by simp; ring

/-- Conversion to the power basis costs one additional magnitude bit. -/
theorem mul_abs_bound (q : ℕ) (a b : List ℤ) (A B : ℤ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : ∀ z ∈ a, |z| ≤ A)
    (hb : ∀ z ∈ b, |z| ≤ B) :
    ∀ z ∈ mul q a b, |z| ≤ 2*(q : ℤ)*A*B := by
  intro z hz
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hz
  calc
    _ ≤ |cyclicCoeff q a b r| + |cyclicCoeff q a b (q-1)| := by
      simpa using abs_sub_le (cyclicCoeff q a b r) 0 (cyclicCoeff q a b (q-1))
    _ ≤ (q : ℤ)*A*B + (q : ℤ)*A*B := add_le_add
      (cyclicCoeff_abs_bound q a b A B hA hB ha hb r)
      (cyclicCoeff_abs_bound q a b A B hA hB ha hb (q-1))
    _ = _ := by ring

theorem atom_abs_bound {q : ℕ} [NeZero q] (e : ZMod q) (c : ℤ) :
    ∀ z ∈ atom e c, |z| ≤ 2*|c| := by
  intro z hz
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
  dsimp only
  split_ifs <;> simp <;> nlinarith [abs_nonneg c]

/-- Iterated multiplication has exponential magnitude and hence polynomial magnitude bits.
This is an arithmetic bound; it does not assert a Turing-machine compilation theorem. -/
theorem ringPow_abs_bound (q : ℕ) [NeZero q] (a : List ℤ) (A : ℤ)
    (hA : 0 ≤ A) (ha : ∀ z ∈ a, |z| ≤ A) (n : ℕ) :
    ∀ z ∈ ringPow q a n, |z| ≤ 2*(2*(q : ℤ)*(A+1))^n := by
  induction n with
  | zero => simpa [ringPow, scalar] using atom_abs_bound (q := q) 0 1
  | succ n ih =>
    intro z hz
    have hpow : 0 ≤ (2*(q : ℤ)*(A+1))^n := by positivity
    have hm := mul_abs_bound q (ringPow q a n) a
      (2*(2*(q : ℤ)*(A+1))^n) A (by positivity) hA ih ha z hz
    calc
      |z| ≤ 2*(q : ℤ)*(2*(2*(q : ℤ)*(A+1))^n)*A := hm
      _ = (2*(2*(q : ℤ)*(A+1))^n)*(2*(q : ℤ)*A) := by ring
      _ ≤ (2*(2*(q : ℤ)*(A+1))^n)*(2*(q : ℤ)*(A+1)) := by
        gcongr
        omega
      _ = 2*(2*(q : ℤ)*(A+1))^(n+1) := by rw [pow_succ]; ring

/-- The fixed full-rank module of squared minimum eight. -/
def fixedInput (S : ℤ) : SVPInput := (3, (([2,0], [0,0]), (([0,0], [2,0]), S)))
def fixedYes : SVPInput := fixedInput 8
def fixedNo : SVPInput := fixedInput 1

private theorem fixed_power (a b : ℤ) :
    powerElement (q := 3) [a,b] = classOf (fun i : ZMod 3 =>
      if i = 0 then a else if i = 1 then b else 0) := by
  unfold powerElement
  congr 1
  funext i
  fin_cases i <;> norm_num [powerCoeffs, List.getD, ZMod.val]
  all_goals simp only [show (2 : ZMod 3) ≠ 0 by decide +kernel,
    show (2 : ZMod 3) ≠ 1 by decide +kernel ]
  all_goals simp

private theorem fixed_two : powerElement (q := 3) [2,0] = 2 := by
  rw [fixed_power]
  simpa using classOf_single_zero (q := 3) 2

private theorem fixed_zero : powerElement (q := 3) [0,0] = 0 := by
  rw [fixed_power]
  simp only [ite_self]
  change classOf (0 : Coeff ℤ 3) = 0
  exact classOf_zero

private theorem fixed_pairs :
    powerPair (q := 3) (fixedInput 0).m₁ = (2,0) ∧
    powerPair (q := 3) (fixedInput 0).m₂ = (0,2) := by
  simp [fixedInput, powerPair, fixed_two, fixed_zero]

/-- In the Eisenstein model every nonzero integral element has norm at least two. -/
theorem eisenstein_norm_ge_two (z : IntegerRing 3) (hz : z ≠ 0) : 2 ≤ normSq z := by
  obtain ⟨a, rfl⟩ := powerElement_surjective z
  rw [powerElement, normSq_classOf, coeffNormSq_eq]
  have he : (∑ i : ZMod 3, powerCoeffs a i ^ 2) =
      (a.getD 0 0)^2 + (a.getD 1 0)^2 := by
    change (∑ i : Fin 3, _) = _
    norm_num [Fin.sum_univ_succ, powerCoeffs, ZMod.val]
  have hs : (∑ i : ZMod 3, powerCoeffs a i) = a.getD 0 0 + a.getD 1 0 := by
    change (∑ i : Fin 3, _) = _
    norm_num [Fin.sum_univ_succ, powerCoeffs, ZMod.val]
  have hn : (a.getD 0 0) ≠ 0 ∨ (a.getD 1 0) ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    have hh : powerCoeffs (q := 3) a = 0 := by
      funext i
      fin_cases i
      · change a.getD 0 0 = 0; exact h.1
      · change a.getD 1 0 = 0; exact h.2
      · rfl
    simp [powerElement, hh]
  rw [he, hs]
  have hp : 1 ≤ (a.getD 0 0)^2 + (a.getD 1 0)^2 := by
    rcases hn with hn | hn
    · have := IdealCVP.int_abs_le_sq (a.getD 0 0)
      have : 1 ≤ |a.getD 0 0| := Int.one_le_abs hn
      nlinarith [sq_nonneg (a.getD 1 0)]
    · have := IdealCVP.int_abs_le_sq (a.getD 1 0)
      have : 1 ≤ |a.getD 1 0| := Int.one_le_abs hn
      nlinarith [sq_nonneg (a.getD 0 0)]
  have ht : 1 ≤ (a.getD 0 0)^2 + (a.getD 1 0)^2 - a.getD 0 0*a.getD 1 0 := by
    nlinarith [sq_nonneg (a.getD 0 0-a.getD 1 0)]
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- Scalar multiplication on the quotient scales its canonical norm quadratically. -/
theorem normSq_integer_mul {q : ℕ} [NeZero q] (a : ℤ) (v : IntegerRing q) :
    normSq ((a : IntegerRing q)*v) = a^2*normSq v := by
  have h := Checker.normSq_smul (q := q) (a : ℚ) (Checker.rationalize v)
  have he : (a : ℚ) • Checker.rationalize v = Checker.rationalize ((a : IntegerRing q)*v) := by
    simp only [map_mul, map_intCast]
    rw [Int.cast_smul_eq_zsmul ℚ, zsmul_eq_mul]
  rw [he, Checker.normSq_rationalize, Checker.normSq_rationalize] at h
  exact_mod_cast h

/-- The fixed module has no nonzero vector shorter than squared norm eight. -/
theorem fixed_minimum (z w : IntegerRing 3)
    (hv : moduleVector (q := 3) (2,0) (0,2) z w ≠ 0) :
    8 ≤ pairNormSq (moduleVector (q := 3) (2,0) (0,2) z w) := by
  have hn : z ≠ 0 ∨ w ≠ 0 := by
    by_contra h
    push Not at h
    simp [moduleVector, h.1, h.2] at hv
  have he : pairNormSq (moduleVector (q := 3) (2,0) (0,2) z w) =
      4*normSq z+4*normSq w := by
    simp only [moduleVector, mul_zero, zero_add, add_zero, pairNormSq]
    rw [mul_comm z, mul_comm w]
    simpa using congrArg₂ (· + ·) (normSq_integer_mul 2 z) (normSq_integer_mul 2 w)
  rw [he]
  rcases hn with hz | hw
  · have := eisenstein_norm_ge_two z hz
    have := normSq_nonneg w
    omega
  · have := eisenstein_norm_ge_two w hw
    have := normSq_nonneg z
    omega

/-- The lower bound eight is attained by the first fixed generator. -/
theorem fixed_minimum_attained :
    ∃ z w : IntegerRing 3, moduleVector (q := 3) (2,0) (0,2) z w ≠ 0 ∧
      pairNormSq (moduleVector (q := 3) (2,0) (0,2) z w) = 8 := by
  have ht : normSq (2 : IntegerRing 3) = 8 := by
    rw [← fixed_two, ← norm_eq]
    decide +kernel
  have hn : pairNormSq (moduleVector (q := 3) (2,0) (0,2) 1 0) = 8 := by
    simpa only [moduleVector, one_mul, zero_mul, zero_add, add_zero,
      pairNormSq, Checker.normSq_zero] using ht
  refine ⟨1,0,?_,hn⟩
  intro he
  rw [he] at hn
  norm_num [pairNormSq, Checker.normSq_zero] at hn

theorem fixedInput_wellFormed (S : ℤ) (hS : 0 ≤ S) : (fixedInput S).WellFormed := by
  apply (wellFormedCheck_eq _).mp
  have hc : wellFormedCheck (fixedInput 0) = true := by decide +kernel
  simp only [wellFormedCheck] at hc ⊢
  exact (Bool.and_eq_true_iff).mpr ⟨(Bool.and_eq_true_iff.mp hc).1, by change decide (0 ≤ S) = true; simpa using hS⟩

theorem fixedYes_mem : fixedYes ∈ ModuleSVPLang := by
  apply (moduleSVP_iff_exists_check _).mpr
  exact ⟨([1,0], [0,0]), by decide +kernel⟩

theorem fixedNo_not_mem : fixedNo ∉ ModuleSVPLang := by
  rintro ⟨_, z, w, hv, hn⟩
  have he₁ : powerPair (q := 3) fixedNo.m₁ = (2,0) := fixed_pairs.1
  have he₂ : powerPair (q := 3) fixedNo.m₂ = (0,2) := fixed_pairs.2
  rw [he₁, he₂] at hv hn
  have := fixed_minimum z w hv
  change _ ≤ (1 : ℤ) at hn
  omega

/-- Integer square root of `9k/10`, the paper's Γ. -/
def mapGamma (k : ℕ) : ℕ := Nat.sqrt (9*k/10)

def qScale (n h : ℕ) : ℕ := 128*(3*n)^4*h

/-- Completely integral form of Equation (23). -/
def threshold (q M n k : ℕ) : ℤ :=
  let h : ℤ := ((21*k/20 : ℕ) : ℤ)
  let W : ℤ := 3*n
  let Q : ℤ := qScale n (21*k/20)
  Q^2*h*((q : ℤ)-h) + 2*q*Q*(2*W*h-2*(3*M)) +
    2*Q*(2*h*W-4*h^2*W^2) + Q^2*((mapGamma k : ℤ)^2*((q : ℤ)-1)) + 2*q*Q

section Core
variable (q : ℕ) [NeZero q] (I : IdealCVP.X3CInstance)
  (s : IdealCVP.SidonPositions I.n)

/-- Each incidence contributes both signed offset monomials. -/
def gList : List ℤ :=
  sumLists q (List.ofFn fun j : Fin I.n =>
    sumLists q (List.ofFn fun i : Fin (3*I.q) =>
      if i ∈ I.triples j then
        let e : ZMod q := (((2*s.α ⟨I.n-1, by have := I.n_pos; omega⟩+1 : ℕ) : ℤ)*
          (i.val+1) - s.α j : ℤ)
        add q (atom e 1) (atom (-e) 1)
      else scalar (q := q) 0))

def vList : List ℤ := mul q (scalar (q := q) 6)
  (sumLists q (List.ofFn fun j : Fin I.n => atom (q := q) (s.α j) 1))

def uList (k : ℕ) : List ℤ :=
  add q (scalar (q := q) ((qScale I.n (21*k/20) : ℕ) : ℤ)) (mul q (gList q I s) (gList q I s))

def piList : List ℤ := sub q (scalar (q := q) 1) (atom (q := q) 1 1)

def centerList (k : ℕ) : List ℤ :=
  add q (scalar (q := q) ((21*k/20 : ℕ) : ℤ)) (ringPow q (piList q) (k/2))

/-- The four integral power-basis coordinate lists of paper v2 §5.3. -/
def coreInput (k : ℕ) : SVPInput :=
  (q, ((mul q (uList q I s k) (ringPow q (piList q) k), scalar (q := q) 0),
    ((sub q (mul q (uList q I s k) (centerList q k)) (vList q I s),
      scalar (q := q) (-((qScale I.n (21*k/20) : ℤ)*mapGamma k))),
      threshold q I.q I.n k)))

@[simp] theorem powerElement_gList :
    powerElement (q := q) (gList q I s) = Checker.g (q := q) I s := by
  classical
  simp only [gList, powerElement_sumLists, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  simp only [Checker.g, Checker.Incidence, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [Checker.d, Checker.offsetInt, Checker.beta]
  let f : Fin (3*I.q) → IntegerRing q := fun i =>
    monomial (((Checker.tau I s : ℤ)*(i.val+1)-s.α j : ℤ) : ZMod q) +
      monomial (-(((Checker.tau I s : ℤ)*(i.val+1)-s.α j : ℤ) : ZMod q))
  change _ = ∑ y : {i : Fin (3*I.q) // i ∈ I.triples j}, f y.val
  rw [← Finset.sum_subtype (I.triples j) (fun _ => Iff.rfl) f]
  simp only [apply_ite (powerElement (q := q)), powerElement_add,
    powerElement_atom, powerElement_scalar, Int.cast_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr (by ext i; simp)
  intro i _
  rfl

@[simp] theorem powerElement_vList :
    powerElement (q := q) (vList q I s) = Checker.V (q := q) I s := by
  simp [vList, powerElement_mul, List.map_ofFn, List.sum_ofFn, Checker.V]

@[simp] theorem powerElement_uList (k : ℕ) :
    powerElement (q := q) (uList q I s k) = Checker.U (q := q) I s (sepWeight k) := by
  simp only [uList, powerElement_add, powerElement_scalar, powerElement_mul,
    powerElement_gList, Int.cast_natCast, Checker.U, Checker.Q,
    Checker.incidence_count, qScale, sepWeight, pow_two]

@[simp] theorem powerElement_piList :
    powerElement (q := q) (piList q) = (pi : IntegerRing q) := by
  simp [piList, powerElement_sub, pi]

@[simp] theorem powerElement_centerList (k : ℕ) :
    powerElement (q := q) (centerList q k) = (sepCenter k : IntegerRing q) := by
  simp only [centerList, powerElement_add, powerElement_scalar, powerElement_ringPow,
    powerElement_piList, Int.cast_natCast, sepCenter, robustCenter, sepWeight]

/-- Every stored coordinate has exactly the power-basis dimension. -/
theorem coreInput_lengths (k : ℕ) :
    (coreInput q I s k).m₁.1.length = q-1 ∧
    (coreInput q I s k).m₁.2.length = q-1 ∧
    (coreInput q I s k).m₂.1.length = q-1 ∧
    (coreInput q I s k).m₂.2.length = q-1 := by
  simp [coreInput, scalar]

/-- The first output generator has the specified ring meaning. -/
theorem coreInput_m₁ (k : ℕ) :
    powerPair (q := q) (coreInput q I s k).m₁ =
      (Checker.U (q := q) I s (sepWeight k)*(pi : IntegerRing q)^k, 0) := by
  simp [coreInput, powerPair, powerElement_mul]

/-- The second output generator has the specified ring meaning. -/
theorem coreInput_m₂ (k : ℕ) :
    powerPair (q := q) (coreInput q I s k).m₂ =
      (Checker.U (q := q) I s (sepWeight k)*sepCenter k-Checker.V I s,
        -((Checker.Q I (sepWeight k) : IntegerRing q)*(mapGamma k : IntegerRing q))) := by
  simp only [coreInput, powerPair, powerElement_sub, powerElement_mul,
    powerElement_uList, powerElement_centerList, powerElement_vList,
    powerElement_scalar, Int.cast_neg, Int.cast_mul, Int.cast_natCast,
    Checker.Q, Checker.incidence_count, qScale, sepWeight]

/-- The output threshold is the explicit witness used by `threshold_integral`. -/
theorem coreInput_S (k : ℕ) :
    (coreInput q I s k).threshold = Checker.thresholdNumerator (q := q) I (sepWeight k)
      ((mapGamma k : ℤ)^2*((q : ℤ)-1)) := by
  simp [coreInput, threshold, Checker.thresholdNumerator, Checker.baselineNumerator,
    Checker.Q, Checker.incidence_count, qScale, sepWeight]

end Core

end ReductionMap
end Rank2ModuleSVP
