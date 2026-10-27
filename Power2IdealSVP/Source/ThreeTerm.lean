import Mathlib.Tactic

/-!
# Three-term moment uniqueness

Elementary no-carry and Newton identities used by the source labels.

Paper: `Power2IdealSVP/paper/power2-ideal-svp.txt`, Section 1.1.
-/

namespace Power2IdealSVP.Source

/-- Three base-`b` digits determine their integer digits, when all digits are in `[0,b)`. -/
theorem three_digits_unique {b x y z u v w : ℤ} (hb : 0 < b)
    (hx : 0 ≤ x ∧ x < b) (hy : 0 ≤ y ∧ y < b) (_hz : 0 ≤ z ∧ z < b)
    (hu : 0 ≤ u ∧ u < b) (hv : 0 ≤ v ∧ v < b) (_hw : 0 ≤ w ∧ w < b)
    (h : x + b * y + b ^ 2 * z = u + b * v + b ^ 2 * w) :
    x = u ∧ y = v ∧ z = w := by
  have hx' : x % b = x := Int.emod_eq_of_lt hx.1 hx.2
  have hu' : u % b = u := Int.emod_eq_of_lt hu.1 hu.2
  have he : x + b * (y + b * z) = u + b * (v + b * w) := by nlinarith only [h]
  have hxu : x = u := by
    have hm := congrArg (· % b) he
    simpa only [Int.add_mul_emod_self_left, hx', hu'] using hm
  have hm : b * (y + b * z) = b * (v + b * w) := by linarith only [he, hxu]
  have hrest : y + b * z = v + b * w := mul_left_cancel₀ (ne_of_gt hb) hm
  have hy' : y % b = y := Int.emod_eq_of_lt hy.1 hy.2
  have hv' : v % b = v := Int.emod_eq_of_lt hv.1 hv.2
  have hyv : y = v := by
    have hm := congrArg (· % b) hrest
    simpa only [Int.add_mul_emod_self_left, hy', hv'] using hm
  have hzw : b * z = b * w := by linarith only [hrest, hyv]
  exact ⟨hxu, hyv, mul_left_cancel₀ (ne_of_gt hb) hzw⟩

private theorem pair_eq_of_moments {a b x y : ℤ}
    (h₁ : a + b = x + y) (h₂ : a ^ 2 + b ^ 2 = x ^ 2 + y ^ 2) :
    ({a, b} : Multiset ℤ) = {x, y} := by
  have hp : a * b = x * y := by nlinarith [congrArg (· ^ 2) h₁]
  have ha : (a - x) * (a - y) = 0 := calc
    _ = a ^ 2 - (x + y) * a + x * y := by ring
    _ = a ^ 2 - (a + b) * a + a * b := by rw [← h₁, ← hp]
    _ = 0 := by ring
  rcases mul_eq_zero.mp ha with ha | ha
  · have : a = x := sub_eq_zero.mp ha
    subst x
    have : b = y := by omega
    subst y
    rfl
  · have : a = y := sub_eq_zero.mp ha
    subst y
    have : b = x := by omega
    subst x
    exact Multiset.pair_comm _ _

/-- The first three power sums recover a triple of integers with multiplicity. -/
theorem multiset_triple_eq_of_moments {a b c x y z : ℤ}
    (h₁ : a + b + c = x + y + z)
    (h₂ : a ^ 2 + b ^ 2 + c ^ 2 = x ^ 2 + y ^ 2 + z ^ 2)
    (h₃ : a ^ 3 + b ^ 3 + c ^ 3 = x ^ 3 + y ^ 3 + z ^ 3) :
    ({a, b, c} : Multiset ℤ) = {x, y, z} := by
  have he₂ : a * b + a * c + b * c = x * y + x * z + y * z := by
    nlinarith [congrArg (· ^ 2) h₁]
  have he₃ : a * b * c = x * y * z := by
    have h : 3 * (a * b * c) = 3 * (x * y * z) := calc
      _ = (a ^ 3 + b ^ 3 + c ^ 3) - (a + b + c) ^ 3 +
          3 * (a + b + c) * (a * b + a * c + b * c) := by ring
      _ = (x ^ 3 + y ^ 3 + z ^ 3) - (x + y + z) ^ 3 +
          3 * (x + y + z) * (x * y + x * z + y * z) := by rw [h₁, h₃, he₂]
      _ = _ := by ring
    omega
  have ha : (a - x) * (a - y) * (a - z) = 0 := by
    calc
      _ = a ^ 3 - (x + y + z) * a ^ 2 +
          (x * y + x * z + y * z) * a - x * y * z := by ring
      _ = a ^ 3 - (a + b + c) * a ^ 2 +
          (a * b + a * c + b * c) * a - a * b * c := by rw [← h₁, ← he₂, ← he₃]
      _ = 0 := by ring
  rcases mul_eq_zero.mp ha with ha | ha
  · rcases mul_eq_zero.mp ha with ha | ha
    · have hax : a = x := sub_eq_zero.mp ha
      subst x
      have hp := pair_eq_of_moments (a := b) (b := c) (x := y) (y := z)
        (by omega) (by nlinarith only [h₂])
      exact congrArg (Multiset.cons a) hp
    · have hay : a = y := sub_eq_zero.mp ha
      subst y
      have hp := pair_eq_of_moments (a := b) (b := c) (x := x) (y := z)
        (by omega) (by nlinarith only [h₂])
      rw [show ({x, a, z} : Multiset ℤ) = {a, x, z} from Multiset.cons_swap _ _ _]
      exact congrArg (Multiset.cons a) hp
  · have haz : a = z := sub_eq_zero.mp ha
    subst z
    have hp := pair_eq_of_moments (a := b) (b := c) (x := x) (y := y)
      (by omega) (by nlinarith only [h₂])
    have hs : ({x, y, a} : Multiset ℤ) = {a, x, y} := by
      change x ::ₘ y ::ₘ a ::ₘ 0 = a ::ₘ x ::ₘ y ::ₘ 0
      rw [Multiset.cons_swap y a, Multiset.cons_swap x a]
    rw [hs]
    exact congrArg (Multiset.cons a) hp

end Power2IdealSVP.Source
