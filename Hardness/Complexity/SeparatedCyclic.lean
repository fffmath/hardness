import Hardness.Complexity.CyclicProblem
import Hardness.Complexity.ModuleProblem
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-! # Certificates for separated cyclic generators

The block multiplication formula is valid for arbitrary targets. Injectivity
uses the proved power-of-two cyclotomic domain theorem, without an unproved CRT premise.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Hardness
open Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace Cyclic

noncomputable def multiplicationMatrix {d : ℕ} (hd : 0 < d) (g : Coeff d) (B : ℤ) :
    Matrix (Fin (2*d)) (Fin (2*d)) ℤ :=
  LinearMap.toMatrix' (mulHom hd g B).toIntLinearMap

@[simp] theorem multiplicationMatrix_mulVec {d : ℕ} (hd : 0 < d)
    (g : Coeff d) (B : ℤ) (q : Coeff (2*d)) :
    (multiplicationMatrix hd g B).mulVec q = mulHom hd g B q :=
  LinearMap.toMatrix'_mulVec _ _

theorem multiplicationMatrix_det_ne_zero {d : ℕ} (hd : ∃ k, d = 2^k)
    (g : Coeff d) (hg : g ≠ 0) (B : ℤ) (hB : B ≠ 0) :
    (multiplicationMatrix (Cyclotomic.power_two_pos hd) g B).det ≠ 0 := by
  intro hz
  obtain ⟨q, hq, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  apply hq
  apply mulHom_injective _ _ _ (Cyclotomic.mul_injective hd hg) hB
  simpa using hzero

theorem mul_bound {d : ℕ} (g q : Coeff d) (A C : ℤ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hg : ∀ i, |g i| ≤ A) (hq : ∀ i, |q i| ≤ C)
    (r : Fin d) : |Cyclotomic.mul g q r| ≤ (d : ℤ)^2 * A * C := by
  unfold Cyclotomic.mul
  calc
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, |if (i.val+j.val)%d = r.val then
        (if i.val+j.val < d then 1 else -1)*g i*q j else 0| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, A*C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> simp only [one_mul, neg_mul, abs_neg, abs_mul, abs_zero]
      · exact mul_le_mul (hg i) (hq j) (abs_nonneg _) hA
      · exact mul_le_mul (hg i) (hq j) (abs_nonneg _) hA
      · exact mul_nonneg hA hC
    _ = _ := by simp; ring

theorem mulHom_bound {d : ℕ} (hd : 0 < d) (g : Coeff d) (B A : ℤ)
    (hA : 0 ≤ A) (hg : ∀ i, |g i| ≤ A) (hB : |B| ≤ A)
    (v : Coeff (2*d)) (hv : ∀ i, |v i| ≤ 1) (r : Fin (2*d)) :
    |mulHom hd g B v r| ≤ 2*A + 2*(d : ℤ)^2*A := by
  obtain ⟨p, q, rfl⟩ := exists_concat v
  have hp (i : Fin d) : |p i| ≤ 1 := by simpa using hv (blockEquiv d (.inl i))
  have hq (i : Fin d) : |q i| ≤ 1 := by simpa using hv (blockEquiv d (.inr i))
  have ha (i : Fin d) : |(p+q) i| ≤ 2 :=
    (abs_add_le _ _).trans (by have := hp i; have := hq i; omega)
  have hb (i : Fin d) : |(p-q) i| ≤ 2 :=
    (abs_sub _ _).trans (by have := hp i; have := hq i; omega)
  have hm := mul_bound g (p-q) A 2 hA (by norm_num) hg hb
  rw [mulHom_concat]
  obtain ⟨i, rfl⟩ := (blockEquiv d).surjective r
  cases i with
  | inl i =>
    simp only [product, concat_left, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      _ ≤ |B| * |(p+q) i| + |Cyclotomic.mul g (p-q) i| := by
        simpa only [abs_mul, Pi.add_apply] using abs_add_le (B*(p+q) i) (Cyclotomic.mul g (p-q) i)
      _ ≤ A*2 + (d : ℤ)^2*A*2 := add_le_add
        (mul_le_mul hB (ha i) (abs_nonneg _) hA) (hm i)
      _ = _ := by ring
  | inr i =>
    simp only [product, concat_right, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    calc
      _ ≤ |B| * |(p+q) i| + |Cyclotomic.mul g (p-q) i| := by
        simpa only [abs_mul, Pi.add_apply] using abs_sub (B*(p+q) i) (Cyclotomic.mul g (p-q) i)
      _ ≤ A*2 + (d : ℤ)^2*A*2 := add_le_add
        (mul_le_mul hB (ha i) (abs_nonneg _) hA) (hm i)
      _ = _ := by ring

theorem multiplicationMatrix_entry_bound {d : ℕ} (hd : 0 < d)
    (g : Coeff d) (B A : ℤ) (hA : 0 ≤ A)
    (hg : ∀ i, |g i| ≤ A) (hB : |B| ≤ A) (i j : Fin (2*d)) :
    |multiplicationMatrix hd g B i j| ≤ 2*A + 2*(d : ℤ)^2*A := by
  rw [multiplicationMatrix, LinearMap.toMatrix'_apply]
  apply mulHom_bound hd g B A hA hg hB
  intro k
  by_cases h : k = j <;> simp [h]

end Cyclic
end Hardness

namespace Hardness
open Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Explicit integral separated generator, with contiguous coefficient blocks. -/
def separatedGenerator (d : ℕ) (g : List ℤ) (B : ℤ) : List ℤ :=
  (List.range (2*d)).map fun r =>
    if r < d then g.getD r 0 + (if r = 0 then B else 0)
    else -g.getD (r-d) 0 + (if r-d = 0 then B else 0)

/-- Floor division by two, implemented with binary natural arithmetic. -/
def binaryHalf (z : ℤ) : ℤ :=
  if z < 0 then -(((z.natAbs+1)/2 : ℕ) : ℤ) else ((z.natAbs/2 : ℕ) : ℤ)

theorem binaryHalf_eq (z : ℤ) : binaryHalf z = z/2 := by
  have ha := Int.natCast_natAbs z
  unfold binaryHalf
  split_ifs with h
  · rw [abs_of_neg h] at ha
    omega
  · rw [abs_of_nonneg (by omega)] at ha
    omega

@[fun_prop] theorem poly_binaryHalf : ComputableTidilyInPolyTime binaryHalf encIntBin encIntBin := by
  have h0 : ComputableTidilyInPolyTime (fun z : ℤ => z.natAbs/2) encIntBin encNat :=
    binary_div' intBin_natAbs (const 2)
  have h1 : ComputableTidilyInPolyTime (fun z : ℤ => (z.natAbs+1)/2) encIntBin encNat :=
    binary_div' (binary_add.comp (intBin_natAbs.prod (const 1))) (const 2)
  have hs : ComputableTidilyInPolyTime (fun z : ℤ => decide (z < 0)) encIntBin encBool := by
    fun_prop
  unfold binaryHalf
  simpa only [Function.comp_def, decide_eq_true_eq] using
    hs.ite' (intBin_neg.comp (intBin_natCast.comp h1)) (intBin_natCast.comp h0)

def separatedB (x : CVPInput) : ℤ := binaryHalf (x.2.1.getD 0 0 + x.2.1.getD x.1 0)

def separatedG (x : CVPInput) : List ℤ :=
  (List.range x.1).map fun i => x.2.1.getD i 0 - (if i = 0 then separatedB x else 0)

/-- Exactly the integral separated class `G=(g+B e₀, -g+B e₀)`,
with power-of-two half-dimension and both `g` and `B` nonzero.
The target is an arbitrary coefficient list of length `2d`. -/
def separatedCyclicCheck (x : CVPInput) : Bool :=
  cvpWellFormedCheck (x.1, separatedG x, (List.range x.1).map (fun _ => (0 : ℤ)), 0) &&
    decide (x.2.2.1.length = 2*x.1) &&
    decide (x.2.1 = separatedGenerator x.1 (separatedG x) (separatedB x)) &&
    decide (separatedB x ≠ 0) && (separatedG x).any (fun z => decide (z ≠ 0))

def SeparatedPrincipalCyclicCVP : Set CVPInput :=
  {x | separatedCyclicCheck x = true ∧ x ∈ PrincipalCyclicCVP}

@[simp] theorem separatedGenerator_eq {d : ℕ} (hd : 0 < d) (g : List ℤ) (B : ℤ) :
    separatedGenerator d g B = toList (Cyclic.generator hd (ofList g) B) := by
  apply Fast.map_range_eq_toList
  intro r
  rw [Cyclic.generator, CyclicFast.concat_apply]
  have hone (i : Fin d) : B * Cyclic.one hd i = if i.val = 0 then B else 0 := by
    by_cases h : i.val = 0 <;> simp [Cyclic.one, Cyclotomic.monomial, Fin.ext_iff, h]
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hone, ofList]
  split_ifs <;> rfl

theorem separatedCyclicCheck_spec (x : CVPInput) : separatedCyclicCheck x = true ↔
    (∃ k, x.1 = 2^k) ∧ x.2.2.1.length = 2*x.1 ∧
      x.2.1 = separatedGenerator x.1 (separatedG x) (separatedB x) ∧
      separatedB x ≠ 0 ∧ ofList (d := x.1) (separatedG x) ≠ 0 := by
  have hlen : (separatedG x).length = x.1 := by simp [separatedG]
  have hn : (∃ z ∈ separatedG x, z ≠ 0) ↔ ofList (d := x.1) (separatedG x) ≠ 0 := by
    constructor
    · rintro ⟨z, hz, hne⟩ hh
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hz
      have hi' : i < x.1 := by omega
      have hc := congrFun hh ⟨i, hi'⟩
      exact hne (by simpa only [ofList, List.getD_eq_getElem _ _ hi, he, Pi.zero_apply] using hc)
    · contrapose!
      intro h
      funext i
      simp only [ofList, List.getD_eq_getElem _ _ (by omega : i.val < (separatedG x).length), Pi.zero_apply]
      exact h _ (List.getElem_mem _)
  simp only [separatedCyclicCheck, Bool.and_eq_true, cvpWellFormedCheck_eq,
    CVPInput.WellFormed, hlen, List.length_map, List.length_range, and_true,
    decide_eq_true_eq, List.any_eq_true, hn, and_assoc]

/-- Coefficientwise difference of the two contiguous blocks of a multiplier. -/
def cyclicDifference (d : ℕ) (q : List ℤ) : List ℤ :=
  (List.range d).map fun i => q.getD i 0 - q.getD (d+i) 0

def cyclicAssembleCoeff (d : ℕ) (B : ℤ) (q v : List ℤ) (r : ℕ) : ℤ :=
  let i := if r < d then r else r-d
  B * (q.getD i 0 + q.getD (d+i) 0) +
    (if r < d then v.getD i 0 else -v.getD i 0)

def cyclicAssemble (d : ℕ) (B : ℤ) (q v : List ℤ) : List ℤ :=
  (List.range (2*d)).map (cyclicAssembleCoeff d B q v)

def separatedProduct (d : ℕ) (g : List ℤ) (B : ℤ) (q : List ℤ) : List ℤ :=
  cyclicAssemble d B q (negacyclicMul d g (cyclicDifference d q))

theorem ofList_separatedProduct {d : ℕ} (hd : 0 < d) (g : List ℤ) (B : ℤ) (q : List ℤ) :
    ofList (d := 2*d) (separatedProduct d g B q) = Cyclic.mulHom hd (ofList g) B (ofList q) := by
  let p : Coeff d := fun i => q.getD i.val 0
  let s : Coeff d := fun i => q.getD (d+i.val) 0
  have he : ofList (d := 2*d) q = Cyclic.concat p s := by
    funext r
    rw [CyclicFast.concat_apply]
    dsimp [ofList, p, s]
    split_ifs <;> congr 1; omega
  have hdiff : ofList (d := d) (cyclicDifference d q) = p-s := by
    funext i
    simp [ofList, cyclicDifference, List.getD_eq_getElem?_getD, i.isLt, p, s]
  have hv := ofList_negacyclicMul d g (cyclicDifference d q)
  rw [hdiff] at hv
  rw [he, Cyclic.mulHom_concat]
  funext r
  simp only [ofList, separatedProduct, cyclicAssemble, cyclicAssembleCoeff, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range, r.isLt, Option.map_some, Option.getD_some]
  rw [Cyclic.product, CyclicFast.concat_apply]
  have hvi (i : Fin d) : (negacyclicMul d g (cyclicDifference d q)).getD i.val 0 =
      Cyclotomic.mul (ofList g) (p-s) i := congrFun hv i
  split_ifs with h
  · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, p, s, List.getD_eq_getElem?_getD] using
      congrArg (fun z => B*(q.getD r.val 0 + q.getD (d+r.val) 0)+z) (hvi ⟨r.val, h⟩)
  · have hi : r.val-d < d := by have := r.isLt; omega
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, p, s, sub_eq_add_neg, List.getD_eq_getElem?_getD] using
      congrArg (fun z => B*(q.getD (r.val-d) 0 + q.getD (d+(r.val-d)) 0)-z) (hvi ⟨r.val-d, hi⟩)

/-- A certificate is the unique integral cyclic multiplier, of length `2d`. -/
def separatedCyclicVerifier (p : CVPInput × List ℤ) : Bool :=
  separatedCyclicCheck p.1 && decide (p.2.length = 2*p.1.1) &&
    decide (listSqDistance (2*p.1.1)
      (separatedProduct p.1.1 (separatedG p.1) (separatedB p.1) p.2)
        p.1.2.2.1 ≤ p.1.2.2.2)

end Hardness

namespace Hardness
open Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

theorem separatedCyclicVerifier_spec (x : CVPInput) (q : List ℤ)
    (hw : separatedCyclicCheck x = true) :
    separatedCyclicVerifier (x, q) = true ↔ q.length = 2*x.1 ∧
      sqNorm (Cyclic.mulHom (Cyclotomic.power_two_pos ((separatedCyclicCheck_spec x).mp hw).1)
        (ofList (separatedG x)) (separatedB x) (ofList q) - ofList x.2.2.1) ≤ x.2.2.2 := by
  simp only [separatedCyclicVerifier, Bool.and_eq_true, hw, true_and,
    decide_eq_true_eq, listSqDistance_eq,
    ofList_separatedProduct (Cyclotomic.power_two_pos ((separatedCyclicCheck_spec x).mp hw).1)]

theorem separatedCyclic_iff_exists_check (x : CVPInput) :
    x ∈ SeparatedPrincipalCyclicCVP ↔ ∃ q, separatedCyclicVerifier (x, q) = true := by
  constructor
  · rintro ⟨hw, hx⟩
    obtain ⟨hd, ht, hg, hB, hne⟩ := (separatedCyclicCheck_spec x).mp hw
    have he : ofList (d := 2*x.1) x.2.1 =
        Cyclic.generator (Cyclotomic.power_two_pos hd) (ofList (separatedG x)) (separatedB x) := by
      rw [hg, separatedGenerator_eq (Cyclotomic.power_two_pos hd), ofList_toList]
    obtain ⟨_, _, _, w, hw', hnorm⟩ := hx
    have hlat : w ∈ Cyclic.lattice (Cyclotomic.power_two_pos hd)
        (ofList (separatedG x)) (separatedB x) := by
      rw [Cyclic.mem_lattice, ← he]
      exact hw'
    rw [← Cyclic.mulHom_range] at hlat
    obtain ⟨q, rfl⟩ := hlat
    exact ⟨toList q, (separatedCyclicVerifier_spec x _ hw).mpr
      ⟨length_toList _, by simpa using hnorm⟩⟩
  · rintro ⟨q, hq⟩
    have hw : separatedCyclicCheck x = true := by
      have hh := hq
      simp only [separatedCyclicVerifier, Bool.and_eq_true] at hh
      exact hh.1.1
    obtain ⟨hd, ht, hg, hB, hne⟩ := (separatedCyclicCheck_spec x).mp hw
    obtain ⟨_, hnorm⟩ := (separatedCyclicVerifier_spec x q hw).mp hq
    refine ⟨hw, hd, ?_, ht, _, ?_, hnorm⟩
    · rw [hg]; simp [separatedGenerator]
    · have hr := Cyclic.mulHom_range (Cyclotomic.power_two_pos hd)
        (ofList (separatedG x)) (separatedB x)
      have hm : Cyclic.mulHom (Cyclotomic.power_two_pos hd) (ofList (separatedG x))
          (separatedB x) (ofList q) ∈ Cyclic.lattice (Cyclotomic.power_two_pos hd)
            (ofList (separatedG x)) (separatedB x) := by
        rw [← hr]; exact ⟨_, rfl⟩
      rw [Cyclic.mem_lattice] at hm
      simpa only [hg, separatedGenerator_eq (Cyclotomic.power_two_pos hd), ofList_toList] using hm

/-- A polynomial-time computable diagonal comparison basis for Cramer's bound. -/
def cyclicMagnitude (x : CVPInput) : ℤ :=
  1 + listSqDistance x.1 (separatedG x) [] + (separatedB x)^2

def cyclicEntryBound (x : CVPInput) : ℤ :=
  2*cyclicMagnitude x + 2*(x.1 : ℤ)^2*cyclicMagnitude x

def cyclicBoundInput (x : CVPInput) : CVPInput :=
  (2*x.1, constantList (2*x.1) ((2*x.1 : ℕ)*cyclicEntryBound x), x.2.2.1, x.2.2.2)

theorem multiplicationMatrix_constantList {n : ℕ} (hn : 0 < n) (M : ℤ) (i j : Fin n) :
    multiplicationMatrix (ofList (d := n) (constantList n M)) i j = if i = j then M else 0 := by
  have he : ofList (d := n) (constantList n M) = Cyclotomic.monomial ⟨0, hn⟩ M := by
    funext r
    simp [ofList_constantList, Cyclotomic.monomial, Fin.ext_iff]
  rw [multiplicationMatrix, he, Cyclotomic.mul_monomial_left]
  simp only [zero_add, Nat.mod_eq_of_lt (Fin.isLt _), ite_eq_left (Fin.isLt _), one_mul]
  simp [← Fin.ext_iff, Cyclotomic.monomial]

theorem cyclicMagnitude_bounds (x : CVPInput) :
    0 ≤ cyclicMagnitude x ∧ |separatedB x| ≤ cyclicMagnitude x ∧
      ∀ i : Fin x.1, |ofList (separatedG x) i| ≤ cyclicMagnitude x := by
  have hz : ofList (d := x.1) ([] : List ℤ) = 0 := by ext; simp [ofList]
  simp only [cyclicMagnitude, listSqDistance_eq, hz, sub_zero]
  have hs := sqNorm_nonneg (ofList (d := x.1) (separatedG x))
  have hb := sq_nonneg (separatedB x)
  refine ⟨by omega, (int_abs_le_sq _).trans (by omega), ?_⟩
  intro i
  exact (residual_coordinate_le _ i).trans (by omega)

theorem cyclicBoundInput_dominates (x : CVPInput) (hw : separatedCyclicCheck x = true) :
    certificateBound (Cyclic.multiplicationMatrix
      (Cyclotomic.power_two_pos ((separatedCyclicCheck_spec x).mp hw).1)
        (ofList (separatedG x)) (separatedB x)) (ofList x.2.2.1) x.2.2.2 ≤
      cvpCertificateBound (cyclicBoundInput x) := by
  have hd := Cyclotomic.power_two_pos ((separatedCyclicCheck_spec x).mp hw).1
  obtain ⟨hA, hB, hg⟩ := cyclicMagnitude_bounds x
  have hE : 0 ≤ cyclicEntryBound x := by unfold cyclicEntryBound; positivity
  have hM : 0 ≤ ((2*x.1 : ℕ) : ℤ)*cyclicEntryBound x := mul_nonneg (by positivity) hE
  have hbase : basisMagnitude (Cyclic.multiplicationMatrix hd (ofList (separatedG x))
      (separatedB x)) ≤ basisMagnitude (multiplicationMatrix
        (ofList (d := 2*x.1) (cyclicBoundInput x).2.1)) := by
    calc
      _ ≤ ∑ _i : Fin (2*x.1), ∑ _j : Fin (2*x.1), cyclicEntryBound x := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact Cyclic.multiplicationMatrix_entry_bound hd _ _ _ hA hg hB i j
      _ = _ := by
        unfold basisMagnitude cyclicBoundInput
        simp only [multiplicationMatrix_constantList (by omega : 0 < 2*x.1),
          apply_ite abs, abs_zero, abs_of_nonneg hM]
        simp
  unfold certificateBound cvpCertificateBound cyclicBoundInput
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀
  · have := basisMagnitude_nonneg (Cyclic.multiplicationMatrix hd
        (ofList (separatedG x)) (separatedB x))
    have := targetMagnitude_nonneg (ofList (d := 2*x.1) x.2.2.1)
    have := abs_nonneg x.2.2.2
    omega
  · dsimp only [cyclicBoundInput] at hbase
    linarith only [hbase]

attribute [local irreducible] List.getD

@[fun_prop] theorem poly_separatedGenerator : ComputableTidilyInPolyTime
    (fun p : RingArgs × ℤ => separatedGenerator p.1.1 p.1.2.1 p.2)
      (encPair encRingArgs encIntBin) (encList encIntBin) := by
  unfold separatedGenerator encRingArgs
  fun_prop

@[fun_prop] theorem poly_separatedB : ComputableTidilyInPolyTime separatedB encCVP encIntBin := by
  have hl : ComputableTidilyInPolyTime (fun x : CVPInput => x.2.1)
      encCVP (encList encIntBin) := by unfold encCVP; fun_prop
  have hd : ComputableTidilyInPolyTime (fun x : CVPInput => x.1)
      encCVP encUnary := by unfold encCVP; fun_prop
  unfold separatedB
  apply poly_binaryHalf.comp
  exact intBin_add.comp
    (((listGetD (encA := encIntBin) 0).comp (hl.prod (const 0))).prod
      ((listGetD (encA := encIntBin) 0).comp (hl.prod hd)))

@[fun_prop] theorem poly_separatedG : ComputableTidilyInPolyTime separatedG encCVP (encList encIntBin) := by
  unfold separatedG
  fun_prop

@[fun_prop] theorem poly_separatedCyclicCheck : ComputableTidilyInPolyTime
    separatedCyclicCheck encCVP encBool := by
  unfold separatedCyclicCheck
  have hr : ComputableTidilyInPolyTime
      (fun x : CVPInput => separatedGenerator x.1 (separatedG x) (separatedB x))
        encCVP (encList encIntBin) :=
    poly_separatedGenerator.comp (show ComputableTidilyInPolyTime
      (fun x : CVPInput => ((x.1, separatedG x, ([] : List ℤ)), separatedB x))
        encCVP (encPair encRingArgs encIntBin) by unfold encRingArgs encCVP; fun_prop)
  unfold encCVP
  fun_prop

@[fun_prop] theorem poly_cyclicDifference : ComputableTidilyInPolyTime
    (fun p : ℕ × List ℤ => cyclicDifference p.1 p.2)
      (encPair encUnary (encList encIntBin)) (encList encIntBin) := by
  unfold cyclicDifference
  fun_prop

abbrev CyclicAssembleArgs := ℕ × (ℤ × (List ℤ × List ℤ))
def encCyclicAssemble : CyclicAssembleArgs ↪ List Bool :=
  encPair encUnary (encPair encIntBin (encPair (encList encIntBin) (encList encIntBin)))

@[fun_prop] theorem poly_cyclicAssembleCoeff : ComputableTidilyInPolyTime
    (fun p : CyclicAssembleArgs × ℕ => cyclicAssembleCoeff p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2)
      (encPair encCyclicAssemble encUnary) encIntBin := by
  have hi : ComputableTidilyInPolyTime
      (fun p : CyclicAssembleArgs × ℕ => if p.2 < p.1.1 then p.2 else p.2-p.1.1)
        (encPair encCyclicAssemble encUnary) encUnary := by unfold encCyclicAssemble; fun_prop
  have hdi : ComputableTidilyInPolyTime
      (fun p : CyclicAssembleArgs × ℕ => p.1.1 + (if p.2 < p.1.1 then p.2 else p.2-p.1.1))
        (encPair encCyclicAssemble encUnary) encUnary := by
    unfold encCyclicAssemble at hi ⊢; fun_prop
  have hq : ComputableTidilyInPolyTime (fun p : CyclicAssembleArgs × ℕ => p.1.2.2.1)
      (encPair encCyclicAssemble encUnary) (encList encIntBin) := by
    unfold encCyclicAssemble; fun_prop
  have hv : ComputableTidilyInPolyTime (fun p : CyclicAssembleArgs × ℕ => p.1.2.2.2)
      (encPair encCyclicAssemble encUnary) (encList encIntBin) := by
    unfold encCyclicAssemble; fun_prop
  have hB : ComputableTidilyInPolyTime (fun p : CyclicAssembleArgs × ℕ => p.1.2.1)
      (encPair encCyclicAssemble encUnary) encIntBin := by unfold encCyclicAssemble; fun_prop
  have hc : ComputableTidilyInPolyTime (fun p : CyclicAssembleArgs × ℕ => decide (p.2 < p.1.1))
      (encPair encCyclicAssemble encUnary) encBool := by unfold encCyclicAssemble; fun_prop
  have hq0 := (listGetD (encA := encIntBin) 0).comp (hq.prod hi)
  have hq1 := (listGetD (encA := encIntBin) 0).comp (hq.prod hdi)
  have hv0 := (listGetD (encA := encIntBin) 0).comp (hv.prod hi)
  have hs := hc.ite' hv0 (intBin_neg.comp hv0)
  have h := intBin_add.comp ((intBin_mul.comp (hB.prod (intBin_add.comp (hq0.prod hq1)))).prod hs)
  simpa only [cyclicAssembleCoeff, Function.comp_def, decide_eq_true_eq] using h

@[fun_prop] theorem poly_cyclicAssemble : ComputableTidilyInPolyTime
    (fun p : CyclicAssembleArgs => cyclicAssemble p.1 p.2.1 p.2.2.1 p.2.2.2)
      encCyclicAssemble (encList encIntBin) := by
  unfold cyclicAssemble
  apply mapWithInput (encA := encUnary)
  · unfold encCyclicAssemble; fun_prop
  · exact poly_cyclicAssembleCoeff

@[fun_prop] theorem poly_separatedProduct : ComputableTidilyInPolyTime
    (fun p : RingArgs × ℤ => separatedProduct p.1.1 p.1.2.1 p.2 p.1.2.2)
      (encPair encRingArgs encIntBin) (encList encIntBin) := by
  have hv : ComputableTidilyInPolyTime
      (fun p : RingArgs × ℤ => negacyclicMul p.1.1 p.1.2.1 (cyclicDifference p.1.1 p.1.2.2))
        (encPair encRingArgs encIntBin) (encList encIntBin) :=
    poly_negacyclicMul.comp (show ComputableTidilyInPolyTime
      (fun p : RingArgs × ℤ => (p.1.1, p.1.2.1, cyclicDifference p.1.1 p.1.2.2))
        (encPair encRingArgs encIntBin) encRingArgs by unfold encRingArgs; fun_prop)
  unfold separatedProduct
  exact poly_cyclicAssemble.comp (show ComputableTidilyInPolyTime
    (fun p : RingArgs × ℤ => (p.1.1, p.2, p.1.2.2,
      negacyclicMul p.1.1 p.1.2.1 (cyclicDifference p.1.1 p.1.2.2)))
      (encPair encRingArgs encIntBin) encCyclicAssemble by
        unfold encRingArgs at hv ⊢
        unfold encCyclicAssemble
        fun_prop)

@[fun_prop] theorem poly_separatedCyclicVerifier : ComputableTidilyInPolyTime
    separatedCyclicVerifier (encPair encCVP (encList encIntBin)) encBool := by
  have hp : ComputableTidilyInPolyTime
      (fun p : CVPInput × List ℤ => separatedProduct p.1.1 (separatedG p.1) (separatedB p.1) p.2)
        (encPair encCVP (encList encIntBin)) (encList encIntBin) :=
    poly_separatedProduct.comp (show ComputableTidilyInPolyTime
      (fun p : CVPInput × List ℤ => ((p.1.1, separatedG p.1, p.2), separatedB p.1))
        (encPair encCVP (encList encIntBin)) (encPair encRingArgs encIntBin) by
          unfold encRingArgs; fun_prop)
  unfold separatedCyclicVerifier
  fun_prop

@[fun_prop] theorem poly_cyclicMagnitude : ComputableTidilyInPolyTime cyclicMagnitude encCVP encIntBin := by
  unfold cyclicMagnitude
  fun_prop

@[fun_prop] theorem poly_cyclicEntryBound : ComputableTidilyInPolyTime cyclicEntryBound encCVP encIntBin := by
  unfold cyclicEntryBound encCVP
  fun_prop

@[fun_prop] theorem poly_cyclicBoundInput : ComputableTidilyInPolyTime cyclicBoundInput encCVP encCVP := by
  unfold cyclicBoundInput encCVP
  fun_prop

end Hardness

namespace Hardness
open Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Every accepted input has the same Cramer-bounded cyclic multiplier. -/
theorem separatedCyclic_bounded_certificate (x : CVPInput) (hx : x ∈ SeparatedPrincipalCyclicCVP) :
    ∃ q : List ℤ, separatedCyclicVerifier (x, q) = true ∧
      (∀ z ∈ q, |z| ≤ cvpCertificateBound (cyclicBoundInput x)) ∧
      (encList encIntBin q).length ≤ witnessPolynomial.eval (encCVP (cyclicBoundInput x)).length := by
  obtain ⟨q, hq⟩ := (separatedCyclic_iff_exists_check x).mp hx
  have hw := hx.1
  obtain ⟨hd, _, _, hB, hg⟩ := (separatedCyclicCheck_spec x).mp hw
  have hnorm := ((separatedCyclicVerifier_spec x q hw).mp hq).2
  let M := Cyclic.multiplicationMatrix (Cyclotomic.power_two_pos hd)
    (ofList (separatedG x)) (separatedB x)
  have hdet : M.det ≠ 0 := Cyclic.multiplicationMatrix_det_ne_zero hd _ hg _ hB
  have hbound (i : Fin (2*x.1)) : |ofList q i| ≤ cvpCertificateBound (cyclicBoundInput x) := by
    apply (certificate_coeff_le M hdet (ofList x.2.2.1) x.2.2.2 (ofList q)
      (by simpa [M] using hnorm) i).trans
    exact cyclicBoundInput_dominates x hw
  refine ⟨toList (ofList (d := 2*x.1) q), ?_, ?_, ?_⟩
  · apply (separatedCyclicVerifier_spec x _ hw).mpr
    exact ⟨length_toList _, by simpa using hnorm⟩
  · intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hbound i
  · have hb : ∀ z ∈ toList (ofList (d := 2*x.1) q), |z| ≤ cvpCertificateBound (cyclicBoundInput x) := by
      intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact hbound i
    have hlen := intList_encoding_length_le _ _ (cvpCertificateBound_nonneg _) hb
    have hbits := cvpCertificateBound_bits (cyclicBoundInput x)
    have hn := (cvp_input_length_bounds (cyclicBoundInput x)).1
    rw [length_toList] at hlen
    simp only [witnessPolynomial, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]
    exact hlen.trans (Nat.mul_le_mul hn (by unfold certificateBitBound at hbits; omega))

/-- Native NP membership; the auxiliary diagonal input has polynomial encoded size. -/
theorem principalCyclicCVP_mem_NP : SeparatedPrincipalCyclicCVP ∈ NP encCVP := by
  obtain ⟨p, hp⟩ := poly_cyclicBoundInput.polyBounded_length.exists_polynomial
  have he : SeparatedPrincipalCyclicCVP = {x | ∃ q, separatedCyclicVerifier (x, q) = true} := by
    ext x; exact separatedCyclic_iff_exists_check x
  rw [he]
  apply mem_NP_of_witness (p := witnessPolynomial.comp p) intBinDecoder.list
    poly_separatedCyclicVerifier (fun _ _ => Iff.rfl)
  intro x q hq
  obtain ⟨q', hq', _, hlen⟩ := separatedCyclic_bounded_certificate x
    ((separatedCyclic_iff_exists_check x).mpr ⟨q, hq⟩)
  refine ⟨q', hq', hlen.trans ?_⟩
  rw [Polynomial.eval_comp]
  exact witnessPolynomial.eval_mono (hp x)

theorem separatedB_generator {d : ℕ} (hd : 0 < d) (g : Coeff d) (B : ℤ)
    (T : List ℤ) (Δ : ℤ) :
    separatedB (d, toList (Cyclic.generator hd g B), T, Δ) = B := by
  simp only [separatedB, binaryHalf_eq, toList, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    show 0 < 2*d by omega, show d < 2*d by omega, ↓reduceDIte, Option.getD_some]
  rw [Cyclic.generator, CyclicFast.concat_apply, CyclicFast.concat_apply]
  simp only [hd, Nat.lt_irrefl, ↓reduceDIte, Nat.sub_self, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, Cyclic.one, Cyclotomic.monomial, ↓reduceIte, mul_one]
  omega

theorem separatedG_generator {d : ℕ} (hd : 0 < d) (g : Coeff d) (B : ℤ)
    (T : List ℤ) (Δ : ℤ) :
    separatedG (d, toList (Cyclic.generator hd g B), T, Δ) = toList g := by
  unfold separatedG
  rw [separatedB_generator]
  apply Fast.map_range_eq_toList
  intro i
  simp only [toList, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    show i.val < 2*d by omega, ↓reduceDIte, Option.getD_some]
  rw [Cyclic.generator, CyclicFast.concat_apply, dite_eq_left i.isLt]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Cyclic.one, Cyclotomic.monomial]
  by_cases h : i.val = 0
  · have he : i = ⟨0, hd⟩ := Fin.ext h
    simp [he]
  · have he : i ≠ ⟨0, hd⟩ := fun hh => h (congrArg Fin.val hh)
    simp [h, he]

theorem separatedCyclicCheck_generator {d : ℕ} (hd : ∃ k, d = 2^k)
    (g : Coeff d) (hg : g ≠ 0) (B : ℤ) (hB : B ≠ 0) (T : List ℤ)
    (ht : T.length = 2*d) (Δ : ℤ) :
    separatedCyclicCheck (d, toList (Cyclic.generator (Cyclotomic.power_two_pos hd) g B), T, Δ) = true := by
  apply (separatedCyclicCheck_spec _).mpr
  simp only [separatedB_generator, separatedG_generator, ofList_toList]
  exact ⟨hd, ht, by rw [separatedGenerator_eq (Cyclotomic.power_two_pos hd), ofList_toList], hB, hg⟩

/-- Exact mathematical scope of the polynomial-time recognizer. -/
theorem separatedCyclicCheck_iff (x : CVPInput) :
    separatedCyclicCheck x = true ↔
      ∃ hd : ∃ k, x.1 = 2^k, ∃ g : Coeff x.1, ∃ B : ℤ,
        g ≠ 0 ∧ B ≠ 0 ∧
          x.2.1 = toList (Cyclic.generator (Cyclotomic.power_two_pos hd) g B) ∧
          x.2.2.1.length = 2*x.1 := by
  constructor
  · intro hw
    obtain ⟨hd, ht, he, hB, hg⟩ := (separatedCyclicCheck_spec x).mp hw
    exact ⟨hd, ofList (separatedG x), separatedB x, hg, hB,
      he.trans (separatedGenerator_eq _ _ _), ht⟩
  · rintro ⟨hd, g, B, hg, hB, he, ht⟩
    have hx : x = (x.1, toList (Cyclic.generator (Cyclotomic.power_two_pos hd) g B),
        x.2.2.1, x.2.2.2) := Prod.ext rfl (Prod.ext he rfl)
    exact (congrArg separatedCyclicCheck hx).trans
      (separatedCyclicCheck_generator hd g hg B hB x.2.2.1 ht x.2.2.2)

/-- The recognized multiplication matrix has a unique integral preimage. -/
theorem separatedCyclic_multiplier_unique (x : CVPInput)
    (hw : separatedCyclicCheck x = true) (q r : Coeff (2*x.1))
    (he : Cyclic.mulHom (Cyclotomic.power_two_pos ((separatedCyclicCheck_spec x).mp hw).1)
      (ofList (separatedG x)) (separatedB x) q =
        Cyclic.mulHom (Cyclotomic.power_two_pos ((separatedCyclicCheck_spec x).mp hw).1)
          (ofList (separatedG x)) (separatedB x) r) : q = r := by
  obtain ⟨hd, _, _, hB, hg⟩ := (separatedCyclicCheck_spec x).mp hw
  exact Cyclic.mulHom_injective _ _ _ (Cyclotomic.mul_injective hd hg) hB he

theorem CyclicFast.compile_separated (S : MaskedSys) :
    separatedCyclicCheck (CyclicFast.compile S) = true := by
  rw [CyclicFast.compile_eq]
  apply separatedCyclicCheck_generator S.reductionDataCubic.d_power_two _
    S.reductionDataCubic.g_ne_zero _ _ _ (length_toList _) _
  have hb : 0 < CyclicFast.B S := by unfold CyclicFast.B; omega
  exact ne_of_gt (by exact_mod_cast hb)

theorem compileCyclicFast_separated_correct (S : MaskedSys) :
    S.Feasible ↔ compileCyclicFast S ∈ SeparatedPrincipalCyclicCVP := by
  constructor
  · intro hs
    refine ⟨?_, (compileCyclicFast_correct S).mp hs⟩
    rw [compileCyclicFast, ite_eq_left ((Fast.wellFormed_eq S).mpr hs.1)]
    exact CyclicFast.compile_separated S
  · exact fun h => (compileCyclicFast_correct S).mpr h.2

theorem polyTimeReducible_Masked_SeparatedCyclicCVP :
    PolyTimeReducible encMasked encCVP {S | S.Feasible} SeparatedPrincipalCyclicCVP :=
  ⟨compileCyclicFast, poly_compileCyclicFast, compileCyclicFast_separated_correct⟩

theorem separatedPrincipalCyclicCVP_npHard : NPHard encCVP SeparatedPrincipalCyclicCVP :=
  maskedSys_npHard.trans polyTimeReducible_Masked_SeparatedCyclicCVP

/-- NP-completeness on the recognized integral separated class. Arbitrary
singular cyclic generators remain admitted only by `PrincipalCyclicCVP`. -/
theorem principalCyclicCVP_npComplete : NPComplete encCVP SeparatedPrincipalCyclicCVP :=
  ⟨principalCyclicCVP_mem_NP, separatedPrincipalCyclicCVP_npHard⟩

end Hardness
