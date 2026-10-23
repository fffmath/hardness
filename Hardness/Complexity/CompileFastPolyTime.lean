import Hardness.Complexity.CompileFastBridge
import Hardness.Complexity.Verifier
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-! # Native polynomial-time certificate for the cubic list compiler

All intermediate natural values have unary certificates. Closure under fixed
polynomial arithmetic, bounded logarithmic powers, and list counting supplies
both time and intermediate-size bounds, including on malformed inputs.
-/
namespace Hardness
open Turing.MultiTapeTM Cslib.Complexity
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

attribute [local irreducible] List.getD

namespace Fast

abbrev encIndex := encUnary
abbrev encEntry := encPair encIndex encIndex
abbrev encCross := encPair encEntry encIndex

@[fun_prop] theorem poly_cols : ComputableTidilyInPolyTime MaskedSys.cols encMasked encUnary := by
  unfold MaskedSys.cols encMasked
  fun_prop

@[fun_prop] theorem poly_rows : ComputableTidilyInPolyTime MaskedSys.rows encMasked
    (encList (encList encBool)) := by
  unfold MaskedSys.rows encMasked
  fun_prop

@[fun_prop] theorem poly_rhs : ComputableTidilyInPolyTime MaskedSys.rhs encMasked
    (encList encBool) := by
  unfold MaskedSys.rhs encMasked
  fun_prop

@[fun_prop] theorem poly_maskList : ComputableTidilyInPolyTime MaskedSys.mask encMasked
    (encList encBool) := by
  unfold MaskedSys.mask encMasked
  fun_prop

@[fun_prop] theorem poly_M : ComputableTidilyInPolyTime M encMasked encUnary := by
  unfold M
  fun_prop

@[fun_prop] theorem poly_n : ComputableTidilyInPolyTime n encMasked encUnary := by
  unfold n
  fun_prop

@[fun_prop] theorem poly_A : ComputableTidilyInPolyTime
    (fun p : MaskedSys × (ℕ × ℕ) => A p.1 p.2.1 p.2.2)
    (encPair encMasked encEntry) encBool := by
  have hrow : ComputableTidilyInPolyTime
      (fun p : MaskedSys × (ℕ × ℕ) => p.1.rows.getD (p.2.1-1) [])
      (encPair encMasked encEntry) (encList encBool) :=
    (listGetD (encA := encList encBool) (encL := encList (encList encBool)) []).comp
      ((poly_rows.comp (fst _ _)).prod (by fun_prop))
  have hentry : ComputableTidilyInPolyTime
      (fun p : MaskedSys × (ℕ × ℕ) => (p.1.rows.getD (p.2.1-1) []).getD (p.2.2-1) false)
      (encPair encMasked encEntry) encBool :=
    (listGetD (encA := encBool) (encL := encList encBool) false).comp
      (hrow.prod (by fun_prop))
  unfold A
  fun_prop

@[fun_prop] theorem poly_b : ComputableTidilyInPolyTime
    (fun p : MaskedSys × ℕ => b p.1 p.2) (encPair encMasked encUnary) encBool := by
  unfold b
  fun_prop

@[fun_prop] theorem poly_mask : ComputableTidilyInPolyTime
    (fun p : MaskedSys × ℕ => mask p.1 p.2) (encPair encMasked encUnary) encBool := by
  unfold mask
  fun_prop

@[fun_prop] theorem poly_alpha : ComputableTidilyInPolyTime
    (fun p : MaskedSys × ℕ => alpha p.1 p.2) (encPair encMasked encUnary) encUnary := by
  unfold alpha
  fun_prop

@[fun_prop] theorem poly_c : ComputableTidilyInPolyTime c encMasked encUnary := by
  unfold c
  fun_prop

@[fun_prop] theorem poly_L : ComputableTidilyInPolyTime L encMasked encUnary := by
  unfold L
  fun_prop

@[fun_prop] theorem poly_rho : ComputableTidilyInPolyTime
    (fun p : MaskedSys × ℕ => rho p.1 p.2) (encPair encMasked encUnary) encUnary := by
  unfold rho
  fun_prop

@[fun_prop] theorem poly_hExp : ComputableTidilyInPolyTime
    (fun p : MaskedSys × (ℕ × ℕ) => hExp p.1 p.2.1 p.2.2)
    (encPair encMasked encEntry) encUnary := by
  unfold hExp
  fun_prop

@[fun_prop] theorem poly_crossExp : ComputableTidilyInPolyTime
    (fun p : MaskedSys × ((ℕ × ℕ) × ℕ) => crossExp p.1 p.2.1.1 p.2.1.2 p.2.2)
    (encPair encMasked encCross) encUnary := by
  unfold crossExp
  fun_prop

@[fun_prop] theorem poly_N : ComputableTidilyInPolyTime N encMasked encUnary := by
  unfold N
  exact unary_pow_clog_const (by fun_prop) 2 2

@[fun_prop] theorem poly_entries : ComputableTidilyInPolyTime entries encMasked
    (encList encEntry) := by
  unfold entries List.product
  fun_prop

@[fun_prop] theorem poly_crosses : ComputableTidilyInPolyTime crosses encMasked
    (encList encCross) := by
  unfold crosses List.product
  fun_prop

@[fun_prop] theorem poly_W : ComputableTidilyInPolyTime W encMasked encUnary := by
  unfold W
  exact countPWithInput poly_entries poly_A

@[fun_prop] theorem poly_nu : ComputableTidilyInPolyTime nu encMasked encUnary := by
  unfold nu
  fun_prop

@[fun_prop] theorem poly_h : ComputableTidilyInPolyTime
    (fun p : MaskedSys × ℕ => h p.1 p.2) (encPair encMasked encUnary) encUnary := by
  unfold h
  apply countPWithInput (encA := encEntry) (by fun_prop)
  fun_prop

@[fun_prop] theorem poly_t : ComputableTidilyInPolyTime
    (fun p : MaskedSys × ℕ => t p.1 p.2) (encPair encMasked encUnary) encUnary := by
  have hrow : ComputableTidilyInPolyTime
      (fun p : MaskedSys × ℕ => (List.range (M p.1)).countP fun i =>
        b p.1 i && decide (p.2 = rho p.1 i))
      (encPair encMasked encUnary) encUnary := by
    apply countPWithInput (encA := encUnary) (by fun_prop)
    fun_prop
  have hcross : ComputableTidilyInPolyTime
      (fun p : MaskedSys × ℕ => (crosses p.1).countP fun e =>
        A p.1 e.1.1 e.1.2 && decide (e.2 ≠ e.1.2) &&
          decide (p.2 = crossExp p.1 e.1.1 e.1.2 e.2))
      (encPair encMasked encUnary) encUnary := by
    apply countPWithInput (encA := encCross) (by fun_prop)
    apply bool_and'
    · apply bool_and'
      · exact poly_A.comp (((fst (encPair encMasked encUnary) encCross).fst').prod
          ((snd (encPair encMasked encUnary) encCross).fst'))
      · exact decide_ne ((snd (encPair encMasked encUnary) encCross).snd')
          ((snd (encPair encMasked encUnary) encCross).fst'.snd')
    · exact (decide_eq encUnary).comp
        (((fst (encPair encMasked encUnary) encCross).snd').prod
          (poly_crossExp.comp (((fst (encPair encMasked encUnary) encCross).fst').prod
            (snd (encPair encMasked encUnary) encCross))))
  unfold t
  exact unary_add.comp ((unary_mul.comp ((const 2).prod hrow)).prod hcross)

@[fun_prop] theorem poly_u : ComputableTidilyInPolyTime
    (fun p : MaskedSys × ℕ => u p.1 p.2) (encPair encMasked encUnary) encUnary := by
  unfold u
  apply countPWithInput (encA := encUnary) (by fun_prop)
  fun_prop

@[fun_prop] theorem poly_sqrtCeil : ComputableTidilyInPolyTime sqrtCeil encUnary encUnary := by
  unfold sqrtCeil
  apply countPWithInput (encA := encUnary) (by fun_prop)
  fun_prop

@[fun_prop] theorem poly_P : ComputableTidilyInPolyTime P encMasked encUnary := by
  have hb : ComputableTidilyInPolyTime
      (fun S : MaskedSys => (List.range (M S)).countP (b S)) encMasked encUnary :=
    countPWithInput (encA := encUnary) (range.comp poly_M) poly_b
  have hs : ComputableTidilyInPolyTime (fun S : MaskedSys => sqrtCeil (n S + 4))
      encMasked encUnary := poly_sqrtCeil.comp (unary_add.comp (poly_n.prod (const 4)))
  have ht := poly_sqrtCeil.comp (unary_add.comp
    ((unary_mul.comp ((const 4).prod hb)).prod poly_nu))
  have hn := poly_sqrtCeil.comp (unary_add.comp (poly_nu.prod (const 4)))
  have hw := unary_mul.comp (hs.prod poly_W)
  have hsum := unary_add.comp ((unary_add.comp (hw.prod ht)).prod hn)
  exact unary_add.comp ((const 1).prod (unary_mul.comp (hs.prod hsum)))

@[fun_prop] theorem poly_weight : ComputableTidilyInPolyTime weight encMasked encUnary := by
  unfold weight
  apply countPWithInput (encA := encUnary) (by fun_prop)
  exact poly_mask

@[fun_prop] theorem poly_unary_int : ComputableTidilyInPolyTime
    (fun n : ℕ => (n : ℤ)) encUnary encIntBin :=
  intBin_natCast.comp unary_to_binary

@[fun_prop] theorem poly_gCoeff : ComputableTidilyInPolyTime
    (fun p : MaskedSys × ℕ => gCoeff p.1 p.2)
    (encPair encMasked encUnary) encIntBin := by
  unfold gCoeff
  fun_prop

@[fun_prop] theorem poly_TCoeff : ComputableTidilyInPolyTime
    (fun p : MaskedSys × ℕ => TCoeff p.1 p.2)
    (encPair encMasked encUnary) encIntBin := by
  unfold TCoeff
  fun_prop

@[fun_prop] theorem poly_wellFormed : ComputableTidilyInPolyTime wellFormed encMasked encBool := by
  unfold wellFormed
  fun_prop

@[fun_prop] theorem poly_compile : ComputableTidilyInPolyTime compile encMasked encCVP := by
  unfold compile encCVP
  fun_prop

/-- The explicit cubic position bound, in the program's counters. -/
theorem c_le (S : MaskedSys) : c S ≤ 3 * (n S)^3 + n S :=
  SidonPositions.cubic_size (n S)

/-- A numerical polynomial dimension bound in the padded row/column counts. -/
theorem dimension_le (S : MaskedSys) :
    2 * N S ≤ 4 * M S * (6 * (n S)^3 + 2 * n S + 1) := by
  change S.reductionDataCubic.d ≤ _
  calc
    _ ≤ 4 * M S * (2 * c S + 1) := S.reductionDataCubic.dimension_le
    _ ≤ _ := Nat.mul_le_mul_left _ (by have := c_le S; omega)

end Fast

/-- The actual total compiler, with no runtime or resource hypotheses. -/
@[fun_prop] theorem poly_compileFast :
    ComputableTidilyInPolyTime compileFast encMasked encCVP := by
  unfold compileFast
  exact Fast.poly_wellFormed.ite' Fast.poly_compile (const cvpNoInput)

end Hardness
