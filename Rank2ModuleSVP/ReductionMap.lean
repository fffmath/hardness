import Rank2ModuleSVP.ReductionMapAux
import IdealCVP.Complexity.X3CVerifier

/-! The total list-X3C map of paper v2 §5.3. No search for completion witnesses
is performed by the map. Its parameters `K0 C0` can be enlarged by final assembly. -/
namespace Rank2ModuleSVP
namespace ReductionMap
open scoped BigOperators
open Rank2ModuleSVP.Membership IdealCVP
open Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] List.getD

/-- At most `Y+1` candidates, in increasing order. -/
def primeCandidates (Y : ℕ) : List ℕ := (List.range (Y+1)).map (Y+·)
def oddPrimeCheck (p : ℕ) : Bool := decide (p ≠ 2) && primeCheck p

def primeScan (Y : ℕ) : ℕ := ((primeCandidates Y).find? oddPrimeCheck).getD 3

@[simp] theorem length_primeCandidates (Y : ℕ) : (primeCandidates Y).length = Y+1 := by
  simp [primeCandidates]

@[simp] theorem mem_primeCandidates (p Y : ℕ) :
    p ∈ primeCandidates Y ↔ Y ≤ p ∧ p ≤ 2*Y := by
  simp only [primeCandidates, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨hl,hu⟩
    exact ⟨p-Y, by omega, by omega⟩

@[simp] theorem oddPrimeCheck_eq (p : ℕ) :
    oddPrimeCheck p = true ↔ p.Prime ∧ p ≠ 2 := by
  simp [oddPrimeCheck, primeCheck_eq, and_comm]

/-- Bertrand supplies an odd prime in the entire dyadic scan. -/
theorem primeScan_exists (Y : ℕ) (hY : 2 ≤ Y) :
    ∃ p, (primeCandidates Y).find? oddPrimeCheck = some p := by
  obtain ⟨p, hp, hl, hu⟩ := Nat.bertrand Y (by omega)
  have he : ((primeCandidates Y).find? oddPrimeCheck).isSome = true :=
    List.find?_isSome.mpr ⟨p, (mem_primeCandidates _ _).mpr ⟨hl.le, hu⟩,
      (oddPrimeCheck_eq _).mpr ⟨hp, by omega⟩⟩
  cases hf : (primeCandidates Y).find? oddPrimeCheck with
  | none => simp [hf] at he
  | some p => exact ⟨p, rfl⟩

/-- The fallback `3` makes the function total even for `Y=0,1`. -/
theorem primeScan_prime (Y : ℕ) : (primeScan Y).Prime ∧ primeScan Y ≠ 2 := by
  unfold primeScan
  cases hf : (primeCandidates Y).find? oddPrimeCheck with
  | none => norm_num
  | some p =>
    simpa using (oddPrimeCheck_eq p).mp (List.find?_some hf)

theorem primeScan_interval (Y : ℕ) (hY : 2 ≤ Y) :
    Y ≤ primeScan Y ∧ primeScan Y ≤ 2*Y := by
  obtain ⟨p, hp⟩ := primeScan_exists Y hY
  have hm : p ∈ primeCandidates Y := by
    obtain ⟨_,i,hi,he,_⟩ := List.find?_eq_some_iff_getElem.mp hp
    exact he ▸ List.getElem_mem hi
  simpa [primeScan, hp] using (mem_primeCandidates p Y).mp hm

/-- The scan chooses the least odd prime in its interval. -/
theorem primeScan_le (Y p : ℕ) (hY : 2 ≤ Y) (hp : p.Prime)
    (hodd : p ≠ 2) (hl : Y ≤ p) (hu : p ≤ 2*Y) : primeScan Y ≤ p := by
  obtain ⟨r, hr⟩ := primeScan_exists Y hY
  obtain ⟨_,i,hi,he,hprev⟩ := List.find?_eq_some_iff_getElem.mp hr
  have hi' : i < Y+1 := by simpa using hi
  have hei : Y+i = r := by simpa [primeCandidates] using he
  have hri : primeScan Y = r := by simp [primeScan, hr]
  rw [hri]
  by_contra h
  have hj : p-Y < i := by omega
  have hf := hprev (p-Y) hj
  have hidx : (primeCandidates Y)[p-Y] = p := by
    simp [primeCandidates, show Y+(p-Y)=p by omega]
  rw [hidx, (oddPrimeCheck_eq p).mpr ⟨hp,hodd⟩] at hf
  contradiction

/-- Row detection on the explicit list incidence matrix. -/
def hasZeroRow (x : X3CList) : Bool :=
  (List.range (3*x.1)).any fun u => !(x.2.any (X3CList.incident u))

theorem hasZeroRow_eq (x : X3CList) : hasZeroRow x = true ↔
    ∃ u : Fin (3*x.1), ∀ t ∈ x.2, X3CList.incident u.val t = false := by
  simp only [hasZeroRow, List.any_eq_true, List.mem_range, Bool.not_eq_true',
    List.any_eq_false, Bool.not_eq_true]
  constructor
  · rintro ⟨u,hu,h⟩; exact ⟨⟨u,hu⟩,h⟩
  · rintro ⟨u,h⟩; exact ⟨u.val,u.isLt,h⟩

theorem zeroRow_not_mem (x : X3CList) (hz : hasZeroRow x = true) : x ∉ X3CLang := by
  obtain ⟨u,hu⟩ := (hasZeroRow_eq x).mp hz
  rintro ⟨_,ξ,hξ⟩
  have h := hξ u
  have hzero : ∀ j : Fin x.2.length, X3CList.incident u.val x.2[j.val] = false :=
    fun j => hu _ (List.getElem_mem j.isLt)
  simp [hzero, bit_false] at h

theorem nonempty_of_no_zeroRow (x : X3CList) (hM : 0 < x.1)
    (hz : hasZeroRow x ≠ true) : 0 < x.2.length := by
  by_contra hn
  have he : x.2 = [] := List.length_eq_zero_iff.mp (by omega)
  apply hz
  apply (hasZeroRow_eq x).mpr
  exact ⟨⟨0,by omega⟩, by simp [he]⟩

/-- Parameters are selected from the number of triples, before prime selection. -/
def mapK (K0 : ℕ) (x : X3CList) : ℕ := max K0 ((x.2.length+2)^2)
def mapY (K0 C0 : ℕ) (x : X3CList) : ℕ := (2*mapK K0 x)^C0
def mapQ (K0 C0 : ℕ) (x : X3CList) : ℕ := primeScan (mapY K0 C0 x)

instance mapQ_neZero (K0 C0 : ℕ) (x : X3CList) : NeZero (mapQ K0 C0 x) :=
  ⟨(primeScan_prime _).1.ne_zero⟩

/-- The map is total on malformed and degenerate inputs, and uses no completion oracle. -/
def reductionMap (K0 C0 : ℕ) (x : X3CList) : SVPInput :=
  if hw : x.WellFormed then
    if hM : x.1 = 0 then fixedYes
    else if hz : hasZeroRow x = true then fixedNo
    else
      let I := x.toInstance hw (by omega) (nonempty_of_no_zeroRow x (by omega) hz)
      coreInput (mapQ K0 C0 x) I (SidonPositions.cubic I.n) (mapK K0 x)
  else fixedNo

theorem reductionMap_malformed (K0 C0 : ℕ) (x : X3CList) (hw : ¬x.WellFormed) :
    reductionMap K0 C0 x = fixedNo := by simp [reductionMap, hw]

theorem reductionMap_empty (K0 C0 : ℕ) (x : X3CList) (hw : x.WellFormed)
    (hM : x.1 = 0) : reductionMap K0 C0 x = fixedYes := by
  simp [reductionMap, hw, hM]

theorem reductionMap_zeroRow (K0 C0 : ℕ) (x : X3CList) (hw : x.WellFormed)
    (hM : x.1 ≠ 0) (hz : hasZeroRow x = true) :
    reductionMap K0 C0 x = fixedNo := by simp [reductionMap, hw, hM, hz]

section Semantics
variable (K0 C0 : ℕ) (x : X3CList) (hw : x.WellFormed)
  (hM : 0 < x.1) (hz : hasZeroRow x ≠ true)

abbrev mapInstance := x.toInstance hw hM (nonempty_of_no_zeroRow x hM hz)

include hw hM hz

/-- Explicit equality of encoded output orders avoids any quotient transport. -/
theorem reductionMap_q : (reductionMap K0 C0 x).q = mapQ K0 C0 x := by
  simp [reductionMap, hw, Nat.ne_of_gt hM, hz, coreInput]

/-- First generator, stated directly on the produced coordinate lists. -/
theorem reductionMap_m₁ :
    powerPair (q := mapQ K0 C0 x) (reductionMap K0 C0 x).m₁ =
      (Checker.U (q := mapQ K0 C0 x) (mapInstance x hw hM hz)
        (SidonPositions.cubic x.2.length) (sepWeight (mapK K0 x)) * (pi : IntegerRing (mapQ K0 C0 x))^(mapK K0 x), 0) := by
  simpa only [reductionMap, dite_eq_left hw, dite_eq_right (Nat.ne_of_gt hM), dite_eq_right hz, mapInstance, X3CList.toInstance]
    using coreInput_m₁ (mapQ K0 C0 x) (mapInstance x hw hM hz)
      (SidonPositions.cubic x.2.length) (mapK K0 x)

/-- Second generator, including the integral second coordinate `-QΓ`. -/
theorem reductionMap_m₂ :
    powerPair (q := mapQ K0 C0 x) (reductionMap K0 C0 x).m₂ =
      (Checker.U (q := mapQ K0 C0 x) (mapInstance x hw hM hz)
        (SidonPositions.cubic x.2.length) (sepWeight (mapK K0 x))*sepCenter (mapK K0 x) -
          Checker.V (mapInstance x hw hM hz) (SidonPositions.cubic x.2.length),
        -((Checker.Q (mapInstance x hw hM hz) (sepWeight (mapK K0 x)) :
          IntegerRing (mapQ K0 C0 x))*(mapGamma (mapK K0 x) : IntegerRing (mapQ K0 C0 x)))) := by
  simpa only [reductionMap, dite_eq_left hw, dite_eq_right (Nat.ne_of_gt hM), dite_eq_right hz, mapInstance, X3CList.toInstance]
    using coreInput_m₂ (mapQ K0 C0 x) (mapInstance x hw hM hz)
      (SidonPositions.cubic x.2.length) (mapK K0 x)

/-- The threshold is exactly the integral numerator from Checker. -/
theorem reductionMap_S :
    (reductionMap K0 C0 x).threshold =
      Checker.thresholdNumerator (q := mapQ K0 C0 x) (mapInstance x hw hM hz)
        (sepWeight (mapK K0 x))
        ((mapGamma (mapK K0 x) : ℤ)^2*((mapQ K0 C0 x : ℤ)-1)) := by
  simpa only [reductionMap, dite_eq_left hw, dite_eq_right (Nat.ne_of_gt hM), dite_eq_right hz, mapInstance, X3CList.toInstance]
    using coreInput_S (mapQ K0 C0 x) (mapInstance x hw hM hz)
      (SidonPositions.cubic x.2.length) (mapK K0 x)

/-- Nonzero rows supply exactly the incidence coverage required by the checker. -/
theorem mapInstance_cover :
    ∀ i : Fin (3*(mapInstance x hw hM hz).q),
      ∃ j, i ∈ (mapInstance x hw hM hz).triples j := by
  classical
  intro i
  have hs : ∃ t ∈ x.2, X3CList.incident i.val t = true := by
    by_contra he
    apply hz
    apply (hasZeroRow_eq x).mpr
    refine ⟨i, fun t ht => ?_⟩
    exact Bool.eq_false_iff.mpr (fun hi => he ⟨t, ht, hi⟩)
  obtain ⟨t,ht,hi⟩ := hs
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp ht
  refine ⟨⟨j,hj⟩, ?_⟩
  have hA : (mapInstance x hw hM hz).system.A i ⟨j,hj⟩ = true := by
    rw [X3CList.toInstance_system]
    simpa only [he] using hi
  exact of_decide_eq_true hA

/-- A nondegenerate preprocessed instance has at most three incidences per column. -/
theorem mapM_le_n : x.1 ≤ x.2.length := by
  have hc := Checker.rows_le_incidence_count (mapInstance x hw hM hz)
    (mapInstance_cover x hw hM hz)
  rw [Checker.incidence_count] at hc
  change 3*x.1 ≤ 3*x.2.length at hc
  omega

end Semantics

/-- Equation (23), stated without any existential choice of the integral threshold. -/
theorem reductionMap_S_formula (K0 C0 : ℕ) (x : X3CList) (hw : x.WellFormed)
    (hM : 0 < x.1) (hz : hasZeroRow x ≠ true) :
    ((reductionMap K0 C0 x).threshold : ℚ) =
      (Checker.Q (mapInstance x hw hM hz) (sepWeight (mapK K0 x)) : ℚ)^2 *
        (Checker.B₀ (q := mapQ K0 C0 x) (mapInstance x hw hM hz) (sepWeight (mapK K0 x)) +
          ((mapGamma (mapK K0 x) : ℤ)^2*((mapQ K0 C0 x : ℤ)-1) : ℤ) +
          Checker.kappa (q := mapQ K0 C0 x) (mapInstance x hw hM hz) (sepWeight (mapK K0 x))) := by
  have hk : 4 ≤ mapK K0 x := by
    have : 4 ≤ (x.2.length+2)^2 := by nlinarith [Nat.zero_le x.2.length]
    exact this.trans (le_max_right _ _)
  have hh : 1 ≤ sepWeight (mapK K0 x) := by unfold sepWeight; omega
  rw [reductionMap_S K0 C0 x hw hM hz]
  symm
  rw [mul_add, mul_add, Checker.baseline_scale_eq _ _ hh, Checker.kappa_scale_eq _ _ hh]
  simp only [Checker.thresholdNumerator, Int.cast_add, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast, Int.cast_ofNat]

/-- The chosen exponent meets both the supplied cutoff and the size requirement. -/
theorem mapK_bounds (K0 : ℕ) (x : X3CList) :
    K0 ≤ mapK K0 x ∧ (x.2.length+2)^2 ≤ mapK K0 x ∧ 4 ≤ mapK K0 x := by
  have hs : 4 ≤ (x.2.length+2)^2 := by nlinarith [Nat.zero_le x.2.length]
  exact ⟨le_max_left _ _, le_max_right _ _, hs.trans (le_max_right _ _)⟩

theorem mapY_ge_two (K0 C0 : ℕ) (x : X3CList) (hC : 1 ≤ C0) :
    2 ≤ mapY K0 C0 x := by
  have hk := (mapK_bounds K0 x).2.2
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ 2*mapK K0 x) hC
  change 2 ≤ (2*mapK K0 x)^C0
  have hp' : 2*mapK K0 x ≤ (2*mapK K0 x)^C0 := by simpa only [pow_one] using hp
  exact (show 2 ≤ 2*mapK K0 x by omega).trans hp'

/-- Exactly the dyadic bound in v2 §5.3, with an odd prime for every input. -/
theorem mapQ_spec (K0 C0 : ℕ) (x : X3CList) (hC : 1 ≤ C0) :
    (mapQ K0 C0 x).Prime ∧ mapQ K0 C0 x ≠ 2 ∧
    (2*max K0 ((x.2.length+2)^2))^C0 ≤ mapQ K0 C0 x ∧
    mapQ K0 C0 x ≤ 2*(2*max K0 ((x.2.length+2)^2))^C0 :=
  ⟨(primeScan_prime _).1, (primeScan_prime _).2,
    primeScan_interval _ (mapY_ge_two K0 C0 x hC)⟩

@[fun_prop] theorem poly_primeCandidates : ComputableTidilyInPolyTime
    primeCandidates encUnary (encList encUnary) := by
  unfold primeCandidates
  apply mapWithInput (encA := encUnary) (by fun_prop)
  fun_prop

@[fun_prop] theorem poly_oddPrimeCheck : ComputableTidilyInPolyTime
    oddPrimeCheck encUnary encBool := by
  unfold oddPrimeCheck
  fun_prop

/-- The scan, including trial division, is polynomial in unary `Y`. -/
@[fun_prop] theorem poly_primeScan : ComputableTidilyInPolyTime
    primeScan encUnary encUnary := by
  have hf : ComputableTidilyInPolyTime
      (fun Y => (primeCandidates Y).find? oddPrimeCheck) encUnary (encOption encUnary) := by
    apply findWithInput poly_primeCandidates
    exact poly_oddPrimeCheck.comp (snd _ _)
  unfold primeScan
  fun_prop

@[fun_prop] theorem poly_mapK (K0 : ℕ) : ComputableTidilyInPolyTime
    (mapK K0) encX3C encUnary := by
  unfold mapK encX3C
  fun_prop

@[fun_prop] theorem poly_mapY (K0 C0 : ℕ) : ComputableTidilyInPolyTime
    (mapY K0 C0) encX3C encUnary := by
  exact (unary_pow C0).comp (unary_mul.comp ((const 2).prod (poly_mapK K0)))

@[fun_prop] theorem poly_mapQ (K0 C0 : ℕ) : ComputableTidilyInPolyTime
    (mapQ K0 C0) encX3C encUnary := poly_primeScan.comp (poly_mapY K0 C0)

@[fun_prop] theorem poly_hasZeroRow : ComputableTidilyInPolyTime
    hasZeroRow encX3C encBool := by
  unfold hasZeroRow
  apply anyWithInput (encA := encUnary) (by unfold encX3C; fun_prop)
  apply bool_not.comp
  apply anyWithInput (encA := encX3CTriple) (by unfold encX3C; fun_prop)
  have hp : ComputableTidilyInPolyTime
      (fun p : (X3CList × ℕ) × X3CTriple => (p.1.2, p.2))
      (encPair (encPair encX3C encUnary) encX3CTriple)
      (encPair encNat encX3CTriple) :=
    (unary_to_binary.comp (fst _ _).snd').prod (snd _ _)
  exact X3CList.poly_incident.comp hp

abbrev encSumArgs := encPair encUnary (encList (encList encIntBin))

/-- Coordinatewise sums need no growing-accumulator loop. -/
@[fun_prop] theorem poly_sumLists : ComputableTidilyInPolyTime
    (fun p : ℕ × List (List ℤ) => sumLists p.1 p.2) encSumArgs (encList encIntBin) := by
  unfold sumLists
  apply mapWithInput (encA := encUnary) (by unfold encSumArgs; fun_prop)
  apply intBin_sum.comp
  apply mapWithInput (encA := encList encIntBin) (by unfold encSumArgs; fun_prop)
  have hp : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List (List ℤ)) × ℕ) × List ℤ => ((p.1.1.1,p.2),p.1.2))
      (encPair (encPair encSumArgs encUnary) (encList encIntBin))
      (encPair (encPair encUnary (encList encIntBin)) encUnary) := by
    unfold encSumArgs
    fun_prop
  exact poly_coeff.comp hp

/-- Cyclic single coefficients and their power-basis conversion have a total polynomial compiler. -/
@[fun_prop] theorem poly_singleList : ComputableTidilyInPolyTime
    (fun p : (ℕ × ℕ) × ℤ => singleList p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) encIntBin) (encList encIntBin) := by
  unfold singleList
  apply mapWithInput (encA := encUnary) (by fun_prop)
  fun_prop

/-- A bounded unary scan computes the usual natural square root. -/
def sqrtScan (r : ℕ) : ℕ :=
  (List.range (r+1)).countP fun i => decide ((i+1)^2 ≤ r)

theorem sqrtScan_eq (r : ℕ) : sqrtScan r = Nat.sqrt r := by
  have he : {i ∈ Finset.range (r+1) | (i+1)^2 ≤ r} = Finset.range (Nat.sqrt r) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, ← Nat.le_sqrt']
    have := Nat.sqrt_le_self r
    omega
  unfold sqrtScan
  change Nat.count (fun i => (i+1)^2 ≤ r) (r+1) = _
  rw [Nat.count_eq_card_filter_range, he, Finset.card_range]

@[fun_prop] theorem poly_sqrtScan : ComputableTidilyInPolyTime
    sqrtScan encUnary encUnary := by
  unfold sqrtScan
  apply countPWithInput (encA := encUnary) (by fun_prop)
  fun_prop

@[fun_prop] theorem poly_nat_sqrt : ComputableTidilyInPolyTime
    Nat.sqrt encUnary encUnary := by
  have he : sqrtScan = Nat.sqrt := funext sqrtScan_eq
  rw [← he]
  exact poly_sqrtScan

@[fun_prop] theorem poly_mapGamma : ComputableTidilyInPolyTime
    mapGamma encUnary encUnary := by unfold mapGamma; fun_prop

@[fun_prop] theorem poly_qScale : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ => qScale p.1 p.2) (encPair encUnary encUnary) encUnary := by
  unfold qScale
  fun_prop

/-- Fixed-degree integer arithmetic after the natural parameters have been computed. -/
def thresholdArithmetic (p : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) : ℤ :=
  let q := p.1
  let M := p.2.1
  let W := p.2.2.1
  let h := p.2.2.2.1
  let Q := p.2.2.2.2.1
  let G := p.2.2.2.2.2
  Q^2*h*(q-h) + 2*q*Q*(2*W*h-2*(3*M)) +
    2*Q*(2*h*W-4*h^2*W^2) + Q^2*(G^2*(q-1)) + 2*q*Q

abbrev encThresholdArgs := encPair encUnary (encPair encUnary (encPair encUnary encUnary))
abbrev encThresholdInts := encPair encIntBin (encPair encIntBin (encPair encIntBin
  (encPair encIntBin (encPair encIntBin encIntBin))))

@[fun_prop] theorem poly_thresholdArithmetic : ComputableTidilyInPolyTime
    thresholdArithmetic encThresholdInts encIntBin := by
  let E := encThresholdInts
  have hq : ComputableTidilyInPolyTime (fun p : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ => p.1)
      E encIntBin := by unfold E encThresholdInts; fun_prop
  have hM : ComputableTidilyInPolyTime (fun p : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ => p.2.1)
      E encIntBin := by unfold E encThresholdInts; fun_prop
  have hW : ComputableTidilyInPolyTime (fun p : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ => p.2.2.1)
      E encIntBin := by unfold E encThresholdInts; fun_prop
  have hh : ComputableTidilyInPolyTime (fun p : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ => p.2.2.2.1)
      E encIntBin := by unfold E encThresholdInts; fun_prop
  have hQ : ComputableTidilyInPolyTime (fun p : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ => p.2.2.2.2.1)
      E encIntBin := by unfold E encThresholdInts; fun_prop
  have hG : ComputableTidilyInPolyTime (fun p : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ => p.2.2.2.2.2)
      E encIntBin := by unfold E encThresholdInts; fun_prop
  have hQ2 := intBin_pow.comp (hQ.prod (const 2))
  have hh2 := intBin_pow.comp (hh.prod (const 2))
  have hW2 := intBin_pow.comp (hW.prod (const 2))
  have hG2 := intBin_pow.comp (hG.prod (const 2))
  have h2qQ := intBin_mul.comp ((intBin_mul.comp ((const 2).prod hq)).prod hQ)
  have ht1 := intBin_mul.comp ((intBin_mul.comp (hQ2.prod hh)).prod
    (intBin_sub.comp (hq.prod hh)))
  have ht2 := intBin_mul.comp (h2qQ.prod (intBin_sub.comp
    ((intBin_mul.comp ((intBin_mul.comp ((const 2).prod hW)).prod hh)).prod
      (intBin_mul.comp ((const 2).prod (intBin_mul.comp ((const 3).prod hM)))))))
  have ht3 := intBin_mul.comp ((intBin_mul.comp ((const 2).prod hQ)).prod
    (intBin_sub.comp
      ((intBin_mul.comp ((intBin_mul.comp ((const 2).prod hh)).prod hW)).prod
        (intBin_mul.comp ((intBin_mul.comp ((const 4).prod hh2)).prod hW2)))))
  have ht4 := intBin_mul.comp (hQ2.prod (intBin_mul.comp (hG2.prod
    (intBin_sub.comp (hq.prod (const 1))))))
  exact intBin_add.comp ((intBin_add.comp ((intBin_add.comp
    ((intBin_add.comp (ht1.prod ht2)).prod ht3)).prod ht4)).prod h2qQ)

/-- The integral threshold, including Γ, has a polynomial-time arithmetic implementation. -/
@[fun_prop] theorem poly_threshold : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ × ℕ × ℕ => threshold p.1 p.2.1 p.2.2.1 p.2.2.2)
    encThresholdArgs encIntBin := by
  have hh : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ => 21*p.2.2.2/20)
      encThresholdArgs encUnary := by unfold encThresholdArgs; fun_prop
  have hQ : ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ × ℕ × ℕ => qScale p.2.2.1 (21*p.2.2.2/20))
      encThresholdArgs encUnary := by
    have hn : ComputableTidilyInPolyTime
        (fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.1) encThresholdArgs encUnary := by
      unfold encThresholdArgs; fun_prop
    exact poly_qScale.comp (hn.prod hh)
  have hG : ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ × ℕ × ℕ => mapGamma p.2.2.2)
      encThresholdArgs encUnary := by
    exact poly_mapGamma.comp (by unfold encThresholdArgs; fun_prop)
  change ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ =>
    thresholdArithmetic ((p.1 : ℤ), (p.2.1 : ℤ), (3*(p.2.2.1 : ℤ)),
      ((21*p.2.2.2/20 : ℕ) : ℤ), (qScale p.2.2.1 (21*p.2.2.2/20) : ℤ),
      (mapGamma p.2.2.2 : ℤ))) encThresholdArgs encIntBin
  apply poly_thresholdArithmetic.comp
  unfold encThresholdInts encThresholdArgs at *
  fun_prop

/-- Both fixed outputs satisfy the v2 odd-prime input conditions. -/
theorem fixed_outputs_wellFormed : fixedYes.WellFormed ∧ fixedNo.WellFormed :=
  ⟨fixedInput_wellFormed 8 (by omega), fixedInput_wellFormed 1 (by omega)⟩

/-- Each rejected malformed X3C input maps to a semantic NO instance. -/
theorem reductionMap_malformed_correct (K0 C0 : ℕ) (x : X3CList)
    (hw : ¬x.WellFormed) :
    (x ∈ X3CLang ↔ reductionMap K0 C0 x ∈ ModuleSVPLang) := by
  rw [reductionMap_malformed K0 C0 x hw]
  simp only [X3CLang, Set.mem_ofPred_eq, hw, false_and,
    iff_false_intro fixedNo_not_mem]

/-- Empty-universe preprocessing preserves the language, including duplicate input indices. -/
theorem reductionMap_empty_correct (K0 C0 : ℕ) (x : X3CList)
    (hw : x.WellFormed) (hM : x.1 = 0) :
    (x ∈ X3CLang ↔ reductionMap K0 C0 x ∈ ModuleSVPLang) := by
  rw [reductionMap_empty K0 C0 x hw hM]
  have he : x.2 = [] := by
    have hh : X3CList.WellFormed (0,x.2) := by
      simpa only [X3CList.WellFormed, hM] using hw
    exact (X3CList.zero_universe _).mp hh
  have hx : x = (0,[]) := Prod.ext hM he
  simp only [hx, x3cList_empty_mem, fixedYes_mem]

/-- Zero rows have no exact cover and map to the fixed semantic NO instance. -/
theorem reductionMap_zeroRow_correct (K0 C0 : ℕ) (x : X3CList)
    (hw : x.WellFormed) (hM : x.1 ≠ 0) (hz : hasZeroRow x = true) :
    (x ∈ X3CLang ↔ reductionMap K0 C0 x ∈ ModuleSVPLang) := by
  rw [reductionMap_zeroRow K0 C0 x hw hM hz]
  exact iff_of_false (zeroRow_not_mem x hz) fixedNo_not_mem

/-- The order of every output is an odd prime, including fixed outputs. -/
theorem reductionMap_order (K0 C0 : ℕ) (x : X3CList) :
    (reductionMap K0 C0 x).q.Prime ∧ (reductionMap K0 C0 x).q ≠ 2 := by
  unfold reductionMap
  split_ifs <;> try norm_num [fixedYes, fixedNo, fixedInput]
  exact primeScan_prime _

/-- Every output coordinate has exactly the dimension recorded in the output order. -/
theorem reductionMap_lengths (K0 C0 : ℕ) (x : X3CList) :
    (reductionMap K0 C0 x).m₁.1.length = (reductionMap K0 C0 x).q-1 ∧
    (reductionMap K0 C0 x).m₁.2.length = (reductionMap K0 C0 x).q-1 ∧
    (reductionMap K0 C0 x).m₂.1.length = (reductionMap K0 C0 x).q-1 ∧
    (reductionMap K0 C0 x).m₂.2.length = (reductionMap K0 C0 x).q-1 := by
  unfold reductionMap
  split_ifs <;> try norm_num [fixedYes, fixedNo, fixedInput]
  exact coreInput_lengths _ _ _ _

/-- The requested dyadic polynomial bound holds for every output order. -/
theorem reductionMap_q_le (K0 C0 : ℕ) (x : X3CList) (hC : 1 ≤ C0) :
    (reductionMap K0 C0 x).q ≤ 2*(2*max K0 ((x.2.length+2)^2))^C0 := by
  have hY := mapY_ge_two K0 C0 x hC
  have hq := (mapQ_spec K0 C0 x hC).2.2.2
  unfold reductionMap
  split_ifs <;> try exact hq
  all_goals change 3 ≤ 2*mapY K0 C0 x; omega

/-- The number of explicitly encoded triples is charged to the source bit length. -/
theorem triples_le_input_length (x : X3CList) : x.2.length ≤ (encX3C x).length :=
  (length_le_length_encList encX3CTriple x.2).trans
    (length_le_encPair_right encUnary (encList encX3CTriple) x)

/-- An explicit fixed-degree polynomial bounding all output dimensions. -/
noncomputable def dimensionPolynomial (K0 C0 : ℕ) : Polynomial ℕ :=
  2*(2*(Polynomial.C K0+(Polynomial.X+2)^2))^C0

theorem reductionMap_dimension_bound (K0 C0 : ℕ) (x : X3CList) (hC : 1 ≤ C0) :
    (reductionMap K0 C0 x).q ≤ (dimensionPolynomial K0 C0).eval (encX3C x).length := by
  apply (reductionMap_q_le K0 C0 x hC).trans
  simp only [dimensionPolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  gcongr
  apply max_le
  · omega
  · have ht := triples_le_input_length x
    have hp : (x.2.length+2)^2 ≤ ((encX3C x).length+2)^2 := by gcongr
    omega

end ReductionMap
end Rank2ModuleSVP
