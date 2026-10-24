import Rank2ModuleSVP.ReductionMap
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration

/-! Polynomial-time certificates for the integral v2 reduction. -/
namespace Rank2ModuleSVP.ReductionMap
open scoped BigOperators
open Rank2ModuleSVP.Membership IdealCVP
open Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD Membership.mul Membership.add Membership.sub
  cyclicCoeff coeff

/-- Total list implementation, including dimension zero. -/
def powList (q : ℕ) (a : List ℤ) : ℕ → List ℤ
  | 0 => singleList q 0 1
  | n+1 => mul q (powList q a n) a

theorem powList_eq_ringPow (q : ℕ) [NeZero q] (a : List ℤ) (n : ℕ) :
    powList q a n = ringPow q a n := by
  induction n with
  | zero => simpa only [powList, ringPow, scalar, ZMod.val_zero] using singleList_eq_atom (0 : ZMod q) 1
  | succ n ih => simp only [powList, ringPow, ih]

@[simp] theorem length_powList (q : ℕ) (a : List ℤ) (n : ℕ) :
    (powList q a n).length = q-1 := by
  cases n <;> simp [powList, singleList, mul]

theorem powList_eq_iterate (q : ℕ) (a : List ℤ) (n : ℕ) :
    powList q a n = (fun b => mul q b a)^[n] (singleList q 0 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', powList, ih]

abbrev encPowArgs := encPair encUnary (encPair (encList encIntBin) encUnary)

/-- Every intermediate power has a polynomial number of bits, uniformly in all inputs. -/
theorem powList_length_bound (p : ℕ × List ℤ × ℕ) (i : ℕ) (hi : i ≤ p.2.2) :
    (encList encIntBin (powList p.1 p.2.1 i)).length ≤
      (encPowArgs p).length * (2*(3+(2*(encPowArgs p).length+2)*(encPowArgs p).length)+1) := by
  let N := (encPowArgs p).length
  have hq : p.1 ≤ N := by
    have := length_le_encPair_left encUnary (encPair (encList encIntBin) encUnary) p
    simpa [N, encPowArgs] using this
  have hn : p.2.2 ≤ N := by
    have := length_le_encPair_right encUnary (encPair (encList encIntBin) encUnary) p
    have := (length_le_encPair_right (encList encIntBin) encUnary p.2).trans this
    simpa [N, encPowArgs] using this
  have haLen : (encList encIntBin p.2.1).length ≤ N :=
    (length_le_encPair_left (encList encIntBin) encUnary p.2).trans
      (length_le_encPair_right encUnary (encPair (encList encIntBin) encUnary) p)
  have ha : ∀ z ∈ p.2.1, |z| ≤ (2 : ℤ)^N := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hz
    have h := getD_abs_le_two_pow p.2.1 N haLen j
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some] using h
  have hb : ∀ z ∈ powList p.1 p.2.1 i, |z| ≤ (2 : ℤ)^(1+(2*N+2)*N) := by
    intro z hz
    by_cases hzero : p.1 = 0
    · have he : powList p.1 p.2.1 i = [] :=
        List.length_eq_zero_iff.mp (by simp [hzero])
      simp [he] at hz
    · let : NeZero p.1 := ⟨hzero⟩
      rw [powList_eq_ringPow] at hz
      have h := ringPow_abs_bound p.1 p.2.1 ((2 : ℤ)^N) (by positivity) ha i z hz
      have hqpow : (p.1 : ℤ) ≤ 2^N := by
        exact_mod_cast hq.trans (Nat.le_of_lt (Nat.lt_two_pow_self))
      have hbase : 2*(p.1 : ℤ)*(2^N+1) ≤ (2 : ℤ)^(2*N+2) := by
        calc
          _ ≤ 2*(2 : ℤ)^N*(2^N+2^N) := by gcongr; exact one_le_pow₀ (by norm_num)
          _ = (2 : ℤ)^(2*N+2) := by
            rw [show 2*N+2 = N+N+1+1 by omega]
            simp only [pow_add, pow_one]
            ring
      calc
        |z| ≤ 2*(2*(p.1 : ℤ)*(2^N+1))^i := h
        _ ≤ 2*((2 : ℤ)^(2*N+2))^i := by gcongr
        _ = (2 : ℤ)^(1+(2*N+2)*i) := by rw [pow_add (2 : ℤ) 1 ((2*N+2)*i), pow_one, pow_mul]
        _ ≤ (2 : ℤ)^(1+(2*N+2)*N) := by
          apply pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hi.trans hn)) _
  have he : ∀ z ∈ powList p.1 p.2.1 i,
      (encIntBin z).length ≤ 3+(2*N+2)*N := by
    intro z hz
    rw [length_encIntBin]
    have hnat : z.natAbs ≤ 2^(1+(2*N+2)*N) := by
      have hh : (z.natAbs : ℤ) ≤ (2 : ℤ)^(1+(2*N+2)*N) := by
        simpa only [Int.natCast_natAbs] using hb z hz
      exact_mod_cast hh
    have hs : z.natAbs.size ≤ 2+(2*N+2)*N := Nat.size_le.mpr
      (hnat.trans_lt (by exact_mod_cast (pow_lt_pow_right₀ (by norm_num : 1 < (2 : ℕ)) (by omega : 1+(2*N+2)*N < 2+(2*N+2)*N))))
    omega
  exact (length_encList_le encIntBin _ he).trans
    (Nat.mul_le_mul_right _ (by rw [length_powList]; omega))

@[fun_prop] theorem poly_powList : ComputableTidilyInPolyTime
    (fun p : ℕ × List ℤ × ℕ => powList p.1 p.2.1 p.2.2)
    encPowArgs (encList encIntBin) := by
  have hpar : ComputableTidilyInPolyTime
      (fun p : ℕ × List ℤ × ℕ => (p.1,p.2.1)) encPowArgs
      (encPair encUnary (encList encIntBin)) := by unfold encPowArgs; fun_prop
  have hc : ComputableTidilyInPolyTime
      (fun p : ℕ × List ℤ × ℕ => p.2.2) encPowArgs encUnary := by
    unfold encPowArgs; fun_prop
  have hinit : ComputableTidilyInPolyTime
      (fun p : ℕ × List ℤ × ℕ => singleList p.1 0 1) encPowArgs (encList encIntBin) := by
    apply poly_singleList.comp (g := fun p : ℕ × List ℤ × ℕ => ((p.1,0),1))
    unfold encPowArgs
    fun_prop
  have hstep : ComputableTidilyInPolyTime
      (fun p : (ℕ × List ℤ) × List ℤ => mul p.1.1 p.2 p.1.2)
      (encPair (encPair encUnary (encList encIntBin)) (encList encIntBin))
      (encList encIntBin) := by
    apply poly_mul.comp (g := fun p : (ℕ × List ℤ) × List ℤ => (p.1.1,p.2,p.1.2))
    unfold encRingArgs
    fun_prop
  have hbound : PolyBounded (fun p : ℕ × List ℤ × ℕ => (encPowArgs p).length)
      (fun p => (encPowArgs p).length * (2*(3+(2*(encPowArgs p).length+2)*(encPowArgs p).length)+1)) := by
    exact PolyBounded.of_polynomiallyBounded _
      (by fun_prop : Cslib.PolynomiallyBounded (fun N => N*(2*(3+(2*N+2)*N)+1)))
  have h := iterateWith
    (par := fun p : ℕ × List ℤ × ℕ => (p.1,p.2.1))
    (count := fun p : ℕ × List ℤ × ℕ => p.2.2)
    (init := fun p : ℕ × List ℤ × ℕ => singleList p.1 0 1)
    (step := fun (p : ℕ × List ℤ) (b : List ℤ) => mul p.1 b p.2)
    hpar hc hinit hstep hbound
    (fun p i hi => by rw [← powList_eq_iterate]; exact powList_length_bound p i hi)
  simpa only [← powList_eq_iterate] using h


/-- Subtraction modulo the dimension, performed entirely in unary naturals. -/
def residueSub (q a b : ℕ) : ℕ := (a%q+q-b%q)%q

@[simp] theorem residueSub_cast (q : ℕ) [NeZero q] (a b : ℕ) :
    (residueSub q a b : ZMod q) = (a : ZMod q) - b := by
  unfold residueSub
  rw [ZMod.natCast_mod, Nat.cast_sub (by have := Nat.mod_lt b (NeZero.pos q); omega)]
  simp

/-- The row offset associated to a cubic witness position. -/
def plainOffset (q n j i : ℕ) : ℕ :=
  residueSub q ((2*SidonPositions.cubicAlpha n (n-1)+1)*(i+1))
    (SidonPositions.cubicAlpha n j)

/-- The checker loop on ordinary input lists, with padded lookup outside the loop range. -/
def plainG (q : ℕ) (x : X3CList) : List ℤ :=
  sumLists q ((List.range x.2.length).map fun j =>
    sumLists q ((List.range (3*x.1)).map fun i =>
      if X3CList.incident i (x.2.getD j (0,0,0)) then
        add q (singleList q (plainOffset q x.2.length j i) 1)
          (singleList q (residueSub q 0 (plainOffset q x.2.length j i)) 1)
      else singleList q 0 0))

def plainV (q : ℕ) (x : X3CList) : List ℤ :=
  mul q (singleList q 0 6) (sumLists q ((List.range x.2.length).map fun j =>
    singleList q (SidonPositions.cubicAlpha x.2.length j) 1))

abbrev encPlainArgs := encPair encUnary encX3C
abbrev encOffsetArgs := encPair encUnary (encPair encUnary (encPair encUnary encUnary))

@[fun_prop] theorem poly_residueSub : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ × ℕ => residueSub p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encUnary encUnary)) encUnary := by
  unfold residueSub
  fun_prop

@[fun_prop] theorem poly_cubicAlpha : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ => SidonPositions.cubicAlpha p.1 p.2)
    (encPair encUnary encUnary) encUnary := by
  unfold SidonPositions.cubicAlpha
  fun_prop

@[fun_prop] theorem poly_plainOffset : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ × ℕ × ℕ => plainOffset p.1 p.2.1 p.2.2.1 p.2.2.2)
    encOffsetArgs encUnary := by
  unfold plainOffset
  apply poly_residueSub.comp (g := fun p : ℕ × ℕ × ℕ × ℕ =>
    (p.1,(2*SidonPositions.cubicAlpha p.2.1 (p.2.1-1)+1)*(p.2.2.2+1),
      SidonPositions.cubicAlpha p.2.1 p.2.2.1))
  unfold encOffsetArgs
  fun_prop

section Composition
variable {α : Type} {E : α ↪ List Bool}

@[fun_prop] theorem poly_singleList_of {q r : α → ℕ} {c : α → ℤ}
    (hq : ComputableTidilyInPolyTime q E encUnary)
    (hr : ComputableTidilyInPolyTime r E encUnary)
    (hc : ComputableTidilyInPolyTime c E encIntBin) :
    ComputableTidilyInPolyTime (fun p => singleList (q p) (r p) (c p)) E (encList encIntBin) :=
  poly_singleList.comp ((hq.prod hr).prod hc)

@[fun_prop] theorem poly_sumLists_of {q : α → ℕ} {a : α → List (List ℤ)}
    (hq : ComputableTidilyInPolyTime q E encUnary)
    (ha : ComputableTidilyInPolyTime a E (encList (encList encIntBin))) :
    ComputableTidilyInPolyTime (fun p => sumLists (q p) (a p)) E (encList encIntBin) :=
  poly_sumLists.comp (hq.prod ha)

@[fun_prop] theorem poly_mul_of {q : α → ℕ} {a b : α → List ℤ}
    (hq : ComputableTidilyInPolyTime q E encUnary)
    (ha : ComputableTidilyInPolyTime a E (encList encIntBin))
    (hb : ComputableTidilyInPolyTime b E (encList encIntBin)) :
    ComputableTidilyInPolyTime (fun p => mul (q p) (a p) (b p)) E (encList encIntBin) :=
  poly_mul.comp (g := fun p => (q p,a p,b p)) (hq.prod (ha.prod hb))

@[fun_prop] theorem poly_add_of {q : α → ℕ} {a b : α → List ℤ}
    (hq : ComputableTidilyInPolyTime q E encUnary)
    (ha : ComputableTidilyInPolyTime a E (encList encIntBin))
    (hb : ComputableTidilyInPolyTime b E (encList encIntBin)) :
    ComputableTidilyInPolyTime (fun p => add (q p) (a p) (b p)) E (encList encIntBin) :=
  poly_add.comp (g := fun p => (q p,a p,b p)) (hq.prod (ha.prod hb))

@[fun_prop] theorem poly_sub_of {q : α → ℕ} {a b : α → List ℤ}
    (hq : ComputableTidilyInPolyTime q E encUnary)
    (ha : ComputableTidilyInPolyTime a E (encList encIntBin))
    (hb : ComputableTidilyInPolyTime b E (encList encIntBin)) :
    ComputableTidilyInPolyTime (fun p => sub (q p) (a p) (b p)) E (encList encIntBin) :=
  poly_sub.comp (g := fun p => (q p,a p,b p)) (hq.prod (ha.prod hb))

@[fun_prop] theorem poly_powList_of {q n : α → ℕ} {a : α → List ℤ}
    (hq : ComputableTidilyInPolyTime q E encUnary)
    (ha : ComputableTidilyInPolyTime a E (encList encIntBin))
    (hn : ComputableTidilyInPolyTime n E encUnary) :
    ComputableTidilyInPolyTime (fun p => powList (q p) (a p) (n p)) E (encList encIntBin) :=
  poly_powList.comp (hq.prod (ha.prod hn))

@[fun_prop] theorem poly_residueSub_of {q a b : α → ℕ}
    (hq : ComputableTidilyInPolyTime q E encUnary)
    (ha : ComputableTidilyInPolyTime a E encUnary)
    (hb : ComputableTidilyInPolyTime b E encUnary) :
    ComputableTidilyInPolyTime (fun p => residueSub (q p) (a p) (b p)) E encUnary :=
  poly_residueSub.comp (hq.prod (ha.prod hb))

@[fun_prop] theorem poly_cubicAlpha_of {n j : α → ℕ}
    (hn : ComputableTidilyInPolyTime n E encUnary)
    (hj : ComputableTidilyInPolyTime j E encUnary) :
    ComputableTidilyInPolyTime (fun p => SidonPositions.cubicAlpha (n p) (j p)) E encUnary :=
  poly_cubicAlpha.comp (hn.prod hj)

@[fun_prop] theorem poly_plainOffset_of {q n j i : α → ℕ}
    (hq : ComputableTidilyInPolyTime q E encUnary)
    (hn : ComputableTidilyInPolyTime n E encUnary)
    (hj : ComputableTidilyInPolyTime j E encUnary)
    (hi : ComputableTidilyInPolyTime i E encUnary) :
    ComputableTidilyInPolyTime (fun p => plainOffset (q p) (n p) (j p) (i p)) E encUnary :=
  poly_plainOffset.comp (g := fun p => (q p,n p,j p,i p)) (hq.prod (hn.prod (hj.prod hi)))
end Composition

@[fun_prop] theorem poly_plainV : ComputableTidilyInPolyTime
    (fun p : ℕ × X3CList => plainV p.1 p.2) encPlainArgs (encList encIntBin) := by
  have hs : ComputableTidilyInPolyTime (fun p : ℕ × X3CList =>
      (List.range p.2.2.length).map fun j =>
        singleList p.1 (SidonPositions.cubicAlpha p.2.2.length j) 1)
      encPlainArgs (encList (encList encIntBin)) := by
    apply mapWithInput (encA := encUnary) (by unfold encPlainArgs encX3C; fun_prop)
    unfold encPlainArgs encX3C
    fun_prop
  have hq : ComputableTidilyInPolyTime (fun p : ℕ × X3CList => p.1)
      encPlainArgs encUnary := fst _ _
  exact poly_mul_of hq (poly_singleList_of hq (const 0) (const 6))
    (poly_sumLists_of hq hs)

@[fun_prop] theorem poly_plainG : ComputableTidilyInPolyTime
    (fun p : ℕ × X3CList => plainG p.1 p.2) encPlainArgs (encList encIntBin) := by
  unfold plainG
  apply poly_sumLists_of (by unfold encPlainArgs; fun_prop)
  apply mapWithInput (encA := encUnary) (by unfold encPlainArgs encX3C; fun_prop)
  apply poly_sumLists_of (by unfold encPlainArgs; fun_prop)
  apply mapWithInput (encA := encUnary) (by unfold encPlainArgs encX3C; fun_prop)
  let E := encPair (encPair encPlainArgs encUnary) encUnary
  have hoff : ComputableTidilyInPolyTime
      (fun p : ((ℕ × X3CList) × ℕ) × ℕ => plainOffset p.1.1.1 p.1.1.2.2.length p.1.2 p.2)
      E encUnary := by unfold E encPlainArgs encX3C; fun_prop
  have hq : ComputableTidilyInPolyTime
      (fun p : ((ℕ × X3CList) × ℕ) × ℕ => p.1.1.1) E encUnary := by
    unfold E encPlainArgs; fun_prop
  have hpos := poly_singleList_of hq hoff (const 1)
  have hneg := poly_singleList_of hq (poly_residueSub_of hq (const 0) hoff) (const 1)
  have hsum := poly_add_of hq hpos hneg
  have hzero := poly_singleList_of hq (const 0) (const 0)
  have hinc : ComputableTidilyInPolyTime
      (fun p : ((ℕ × X3CList) × ℕ) × ℕ =>
        X3CList.incident p.2 (p.1.1.2.2.getD p.1.2 (0,0,0))) E encBool := by
    apply X3CList.poly_incident.comp (g := fun p : ((ℕ × X3CList) × ℕ) × ℕ =>
      (p.2,p.1.1.2.2.getD p.1.2 (0,0,0)))
    unfold E encPlainArgs encX3C
    fun_prop
  exact ComputableTidilyInPolyTime.ite hinc (hsum.restrict _) (hzero.restrict _)

/-- Range loops and proof-carrying finite loops agree extensionally. -/
theorem range_map_eq_ofFn {α : Type} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn (fun j : Fin n => f j.val) := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp

/-- A natural exponent denotes the same power-basis atom as its cyclic residue. -/
theorem singleList_eq_atom_cast (q : ℕ) [NeZero q] (r : ℕ) (c : ℤ) :
    singleList q r c = atom (r : ZMod q) c := by
  have he : singleList q r c = singleList q (r%q) c := by simp [singleList]
  rw [he, ← ZMod.val_natCast q r]
  exact singleList_eq_atom _ _

theorem plainV_eq_vList (q : ℕ) [NeZero q] (x : X3CList) (hw : x.WellFormed)
    (hM : 0 < x.1) (hn : 0 < x.2.length) :
    plainV q x = vList q (x.toInstance hw hM hn) (SidonPositions.cubic x.2.length) := by
  simp only [plainV, vList, range_map_eq_ofFn, singleList_eq_atom_cast, scalar,
    SidonPositions.cubic, X3CList.toInstance, Nat.cast_zero]

theorem plainG_eq_gList (q : ℕ) [NeZero q] (x : X3CList) (hw : x.WellFormed)
    (hM : 0 < x.1) (hn : 0 < x.2.length) :
    plainG q x = gList q (x.toInstance hw hM hn) (SidonPositions.cubic x.2.length) := by
  unfold plainG gList
  rw [range_map_eq_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  rw [range_map_eq_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  have hi : X3CList.incident i.val (x.2.getD j.val (0,0,0)) =
      decide (i ∈ (x.toInstance hw hM hn).triples j) := by
    rw [List.getD_eq_getElem _ _ j.isLt]
    exact (X3CList.toInstance_system x hw hM hn i j).symm
  rw [hi]
  simp only [decide_eq_true_eq]
  split_ifs
  · simp only [singleList_eq_atom_cast, plainOffset, residueSub_cast,
      SidonPositions.cubic, X3CList.toInstance, Nat.cast_zero, zero_sub,
      Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Int.cast_sub,
      Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_one, Int.cast_ofNat]
  · simpa only [scalar, Nat.cast_zero] using singleList_eq_atom_cast q 0 0


/-- Total versions of all four generator computations. -/
def plainPi (q : ℕ) : List ℤ := sub q (singleList q 0 1) (singleList q 1 1)
def plainU (q : ℕ) (x : X3CList) (k : ℕ) : List ℤ :=
  add q (singleList q 0 (qScale x.2.length (21*k/20))) (mul q (plainG q x) (plainG q x))
def plainCenter (q k : ℕ) : List ℤ :=
  add q (singleList q 0 ((21*k/20 : ℕ) : ℤ)) (powList q (plainPi q) (k/2))
def plainCore (q : ℕ) (x : X3CList) (k : ℕ) : SVPInput :=
  (q, ((mul q (plainU q x k) (powList q (plainPi q) k), singleList q 0 0),
    ((sub q (mul q (plainU q x k) (plainCenter q k)) (plainV q x),
      singleList q 0 (-((qScale x.2.length (21*k/20) : ℤ)*mapGamma k))),
      threshold q x.1 x.2.length k)))

abbrev encCoreArgs := encPair encUnary (encPair encX3C encUnary)

@[fun_prop] theorem poly_plainPi : ComputableTidilyInPolyTime
    plainPi encUnary (encList encIntBin) := by unfold plainPi; fun_prop

@[fun_prop] theorem poly_plainU : ComputableTidilyInPolyTime
    (fun p : ℕ × X3CList × ℕ => plainU p.1 p.2.1 p.2.2)
    encCoreArgs (encList encIntBin) := by
  have hg : ComputableTidilyInPolyTime
      (fun p : ℕ × X3CList × ℕ => plainG p.1 p.2.1)
      encCoreArgs (encList encIntBin) :=
    poly_plainG.comp (g := fun p : ℕ × X3CList × ℕ => (p.1,p.2.1))
      (by unfold encCoreArgs encPlainArgs; fun_prop)
  unfold plainU encCoreArgs at *
  fun_prop

@[fun_prop] theorem poly_plainCenter : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ => plainCenter p.1 p.2)
    (encPair encUnary encUnary) (encList encIntBin) := by
  unfold plainCenter
  fun_prop

@[fun_prop] theorem poly_plainCore : ComputableTidilyInPolyTime
    (fun p : ℕ × X3CList × ℕ => plainCore p.1 p.2.1 p.2.2)
    encCoreArgs encSVP := by
  have hq : ComputableTidilyInPolyTime (fun p : ℕ × X3CList × ℕ => p.1)
      encCoreArgs encUnary := by unfold encCoreArgs; fun_prop
  have hk : ComputableTidilyInPolyTime (fun p : ℕ × X3CList × ℕ => p.2.2)
      encCoreArgs encUnary := by unfold encCoreArgs; fun_prop
  have hx : ComputableTidilyInPolyTime (fun p : ℕ × X3CList × ℕ => p.2.1)
      encCoreArgs encX3C := by unfold encCoreArgs; fun_prop
  have hv := poly_plainV.comp (hq.prod hx)
  have hc := poly_plainCenter.comp (hq.prod hk)
  have ht : ComputableTidilyInPolyTime (fun p : ℕ × X3CList × ℕ =>
      threshold p.1 p.2.1.1 p.2.1.2.length p.2.2) encCoreArgs encIntBin :=
    poly_threshold.comp (g := fun p : ℕ × X3CList × ℕ =>
      (p.1,p.2.1.1,p.2.1.2.length,p.2.2))
      (by unfold encCoreArgs encThresholdArgs encX3C; fun_prop)
  have hp := poly_powList_of hq (poly_plainPi.comp hq) hk
  have hfirst := poly_mul_of hq poly_plainU hp
  have hsecond := poly_sub_of hq (poly_mul_of hq poly_plainU hc) hv
  have hzero := poly_singleList_of hq (const 0) (const 0)
  have hneg : ComputableTidilyInPolyTime (fun p : ℕ × X3CList × ℕ =>
      -((qScale p.2.1.2.length (21*p.2.2/20) : ℤ)*mapGamma p.2.2))
      encCoreArgs encIntBin := by
    unfold encCoreArgs encX3C
    fun_prop
  have hscalar := poly_singleList_of hq (const 0) hneg
  exact hq.prod ((hfirst.prod hzero).prod ((hsecond.prod hscalar).prod ht))

@[simp] theorem plainPi_eq_piList (q : ℕ) [NeZero q] : plainPi q = piList q := by
  simp [plainPi, piList, singleList_eq_atom_cast, scalar]

theorem plainCore_eq_coreInput (q : ℕ) [NeZero q] (x : X3CList) (hw : x.WellFormed)
    (hM : 0 < x.1) (hn : 0 < x.2.length) (k : ℕ) :
    plainCore q x k = coreInput q (x.toInstance hw hM hn)
      (SidonPositions.cubic x.2.length) k := by
  have hg := plainG_eq_gList q x hw hM hn
  have hv := plainV_eq_vList q x hw hM hn
  simp only [plainCore, coreInput, plainU, plainCenter, hg, hv,
    plainPi_eq_piList, powList_eq_ringPow, singleList_eq_atom_cast, Nat.cast_zero,
    scalar, uList, centerList, X3CList.toInstance]

/-- A proof-free wrapper with exactly the same preprocessing as `reductionMap`. -/
def plainReduction (K0 C0 : ℕ) (x : X3CList) : SVPInput :=
  if x.WellFormed then
    if x.1 = 0 then fixedYes
    else if hasZeroRow x = true then fixedNo
    else plainCore (mapQ K0 C0 x) x (mapK K0 x)
  else fixedNo

theorem plainReduction_eq_reductionMap (K0 C0 : ℕ) (x : X3CList) :
    plainReduction K0 C0 x = reductionMap K0 C0 x := by
  unfold plainReduction reductionMap
  split_ifs with hw hM hz
  · rfl
  · rfl
  · exact plainCore_eq_coreInput _ x hw (by omega)
      (nonempty_of_no_zeroRow x (by omega) hz) _
  · rfl

@[fun_prop] theorem poly_plainReduction (K0 C0 : ℕ) : ComputableTidilyInPolyTime
    (plainReduction K0 C0) encX3C encSVP := by
  have hw : ComputableTidilyInPolyTime (fun x : X3CList => decide x.WellFormed)
      encX3C encBool := by
    convert X3CList.poly_wellFormedCheck using 1
    funext x
    exact Bool.eq_iff_iff.mpr (by simp)
  have hM : ComputableTidilyInPolyTime (fun x : X3CList => decide (x.1 = 0))
      encX3C encBool := by unfold encX3C; fun_prop
  have hc := poly_plainCore.comp ((poly_mapQ K0 C0).prod (id'.prod (poly_mapK K0)))
  have hz := ComputableTidilyInPolyTime.ite poly_hasZeroRow
    ((const fixedNo).restrict _) (hc.restrict _)
  have hm := ComputableTidilyInPolyTime.ite hM ((const fixedYes).restrict _) (hz.restrict _)
  have h := ComputableTidilyInPolyTime.ite hw (hm.restrict _) ((const fixedNo).restrict _)
  convert h using 1
  funext x
  simp only [plainReduction, decide_eq_true_eq, Function.comp_apply]

/-- Paper v2 §5.3: the entire reduction, for any fixed natural cutoffs, is polynomial time. -/
@[fun_prop] theorem reductionMap_polytime (K0 C0 : ℕ) :
    ComputableTidilyInPolyTime (reductionMap K0 C0) IdealCVP.encX3C encSVP := by
  have he : plainReduction K0 C0 = reductionMap K0 C0 :=
    funext (plainReduction_eq_reductionMap K0 C0)
  rw [← he]
  exact poly_plainReduction K0 C0

/-- Package the certificate with an independently proved semantic correctness theorem. -/
theorem reductionMap_polyTimeReducible_of_correct (K0 C0 : ℕ)
    (h : ∀ x, x ∈ IdealCVP.X3CLang ↔ reductionMap K0 C0 x ∈ ModuleSVPLang) :
    PolyTimeReducible IdealCVP.encX3C encSVP IdealCVP.X3CLang ModuleSVPLang :=
  ⟨reductionMap K0 C0, reductionMap_polytime K0 C0, h⟩

end Rank2ModuleSVP.ReductionMap
