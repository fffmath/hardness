import Power2ModuleSVP.ColoringNative2

/-! Size accounting for the data seen by a direction. Frozen coordinates
are represented by signs and zero, so their original fractions never enter
this encoding bound. -/
namespace Power2ModuleSVP.ColoringRuntime
open PartialColoringAlg ColoringNative
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open scoped BigOperators
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem weightBox_bits {r m k : ℕ} {s : State r m} (hs : WeightBox k s) (i : Fin m) :
    rationalBits (s.w i) ≤ 2 * (k + 1) + 1 + 2 * (precision r m + 2) := by
  have hq : s.w i ≤ (4 : ℚ) ^ (k + 1) := by
    have h := hs.2.2.1 i
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℚ) ≤ 4) k]
  have hn := numerator_bits_le_of_nonneg_le_pow (hs.2.1 i) hq
  have hd := Nat.size_le_size (Nat.le_of_dvd (by positivity : 0 < 2 ^ (precision r m + 1))
    (hs.2.2.2 i))
  rw [Nat.size_pow] at hd
  unfold rationalBits
  omega

/-- The indexed box is preserved by every stopped-walk prefix. -/
theorem weightBox_walk {r m k : ℕ} (hr : 0 < r) (a : Fin m → Row r)
    (hl : ∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ))
    (hn : ∀ i, dot (a i).a (a i).a ≤ 1) (fuel : ℕ) (s : State r m)
    (hs : WeightBox k s) : WeightBox (k + fuel) (walk a fuel s) := by
  induction fuel generalizing k s with
  | zero => simpa [walk] using hs
  | succ fuel ih =>
    rw [walk]
    split_ifs
    · exact weightBox_mono hs (by omega)
    · have h := ih (nextState a s) (weightBox_next hr a hl hn hs)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

theorem rational_encoding_le_bits (q : ℚ) :
    (encColoringRational q).length ≤ 2 * rationalBits q + 3 := by
  simp only [encColoringRational, Function.Embedding.coeFn_mk, length_encPair,
    length_encIntBin, encNat_apply, Nat.size_eq_bits_len, rationalBits]
  omega

/-- The weight list has a uniform encoding bound on the whole box, rather
than just on the terminal state of a walk. -/
theorem weightBox_encoding {r m k : ℕ} {s : State r m} (hs : WeightBox k s) :
    (encList encColoringRational (List.ofFn s.w)).length ≤
      (2 * (2 * (2 * (k + 1) + 1 + 2 * (precision r m + 2)) + 3) + 1) * m := by
  apply (length_encList_le encColoringRational _ (b :=
    2 * (2 * (k + 1) + 1 + 2 * (precision r m + 2)) + 3) ?_).trans
  · simp [Nat.mul_comm]
  · intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact (rational_encoding_le_bits _).trans (by have h := weightBox_bits hs i; omega)

/-- A point retaining precisely the frozen-coordinate information. -/
def frozenPoint {r : ℕ} (x : Vec r) : Vec r :=
  fun j => if x j = -1 then -1 else if x j = 1 then 1 else 0

theorem frozenPoint_fixed {r : ℕ} (x : Vec r) (j : Fin r) :
    (x j = -1 ∨ x j = 1) ↔ (frozenPoint x j = -1 ∨ frozenPoint x j = 1) := by
  unfold frozenPoint
  split_ifs <;> norm_num <;> tauto

theorem frozenPoint_encoding {r : ℕ} (x : Vec r) :
    (encList encColoringRational (List.ofFn (frozenPoint x))).length ≤ 13 * r := by
  apply (length_encList_le encColoringRational _ (b := 6) ?_).trans
  · simp [Nat.mul_comm]
  · intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    unfold frozenPoint
    split_ifs <;> norm_num [encColoringRational, length_encPair,
      length_encIntBin, encNat_apply, Nat.size_eq_bits_len]

theorem walkDirectionInput_frozen {r m : ℕ} (a : Fin m → Row r) (s : State r m) :
    walkDirectionInput a s = walkDirectionInput a ⟨frozenPoint s.x, s.w⟩ :=
  walkDirectionInput_eq_of_weights_and_fixed a s _ rfl (frozenPoint_fixed s.x)

end Power2ModuleSVP.ColoringRuntime
