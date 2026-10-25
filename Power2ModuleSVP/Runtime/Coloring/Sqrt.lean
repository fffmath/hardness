module

public import Power2ModuleSVP.Runtime.Coloring.Arithmetic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold

/-!
# Sqrt

Binary square roots by a descending digit scan. The scan has one step
per input bit; it never enumerates the input's numerical value.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.ColoringRuntime

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open PartialColoringAlg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

def sqrtDigit (n a k : ℕ) : ℕ :=
  if (a + 2 ^ k) ^ 2 ≤ n then a + 2 ^ k else a

def sqrtBinary (n : ℕ) : ℕ :=
  ((List.range n.size).reverse).foldl (sqrtDigit n) 0

private theorem sqrtScan_eq (n k a : ℕ) (hlo : a ≤ Nat.sqrt n)
    (hhi : Nat.sqrt n < a + 2 ^ k) :
    ((List.range k).reverse).foldl (sqrtDigit n) a = Nat.sqrt n := by
  induction k generalizing a with
  | zero => simpa using (show a = Nat.sqrt n by simpa using (Nat.eq_of_le_of_lt_succ hlo hhi).symm)
  | succ k ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    apply ih
    · unfold sqrtDigit
      split_ifs with h
      · exact (Nat.le_sqrt').mpr h
      · exact hlo
    · unfold sqrtDigit
      split_ifs with h
      · rw [pow_succ] at hhi
        omega
      · have hn : ¬a + 2 ^ k ≤ Nat.sqrt n := by simpa only [Nat.le_sqrt'] using h
        omega

theorem sqrtBinary_eq (n : ℕ) : sqrtBinary n = Nat.sqrt n := by
  apply sqrtScan_eq n n.size 0 (Nat.zero_le _)
  simpa using (Nat.sqrt_le_self n).trans_lt (Nat.lt_size_self n)

@[fun_prop] theorem sqrtDigit_polytime :
    ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ => sqrtDigit p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) encUnary) encNat := by
  unfold sqrtDigit
  have hp : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.2 + 2 ^ p.2)
      (encPair (encPair encNat encNat) encUnary) encNat := by fun_prop
  have ht : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℕ =>
      decide ((p.1.2 + 2 ^ p.2) ^ 2 ≤ p.1.1))
      (encPair (encPair encNat encNat) encUnary) encBool := by fun_prop
  exact ht.ite_decide hp (by fun_prop)

/-- Every digit adds at most the input bit length plus two bits, even on
arbitrary accumulator values. This is the native bounded-fold obligation. -/
@[fun_prop] theorem sqrtBinary_polytime :
    ComputableTidilyInPolyTime sqrtBinary encNat encNat := by
  have hsize : ComputableTidilyInPolyTime Nat.size encNat encUnary :=
    (encoding_length encNat).of_enc_eq fun n => by simp [encNat_apply, Nat.size_eq_bits_len]
  unfold sqrtBinary
  apply foldlWith_of_bounded_growth (encP := encNat) (encA := encUnary)
    (encL := encList encUnary) (encB := encNat) (growth := fun n => n.size + 2)
    id' (by fun_prop) (const 0) sqrtDigit_polytime
    (hsize.polyBounded.add (.const 2))
  intro n a k hk
  have hk' : k < n.size := List.mem_range.mp (List.mem_reverse.mp hk)
  simp only [encNat_apply, Nat.size_eq_bits_len]
  unfold sqrtDigit
  split_ifs
  · have ha := Nat.size_add_le a (2 ^ k)
    have hp : (2 ^ k).size ≤ k + 1 := by
      apply Nat.size_le.mpr
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · omega

/-- Binary square root, including zero, in the canonical binary encoding. -/
@[fun_prop] theorem sqrt_polytime :
    ComputableTidilyInPolyTime Nat.sqrt encNat encNat :=
  sqrtBinary_polytime.of_enc_eq fun n => congrArg encNat (sqrtBinary_eq n).symm

@[fun_prop] theorem ceilSqrt_polytime :
    ComputableTidilyInPolyTime ceilSqrt encNat encNat := by
  unfold ceilSqrt
  fun_prop

@[fun_prop] theorem normScale_polytime :
    ComputableTidilyInPolyTime normScale encColoringRational encColoringRational := by
  have hn : ComputableTidilyInPolyTime (fun s : ℚ =>
      (ceilSqrt (s.num.natAbs * s.den) : ℤ)) encColoringRational encIntBin := by fun_prop
  have hd : ComputableTidilyInPolyTime (fun s : ℚ => (s.den : ℤ))
      encColoringRational encIntBin := by fun_prop
  exact rational_of_ints_polytime hn hd

end Power2ModuleSVP.ColoringRuntime
