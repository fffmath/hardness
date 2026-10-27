import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Short lifts of pairwise close circular supports

The separation `3R < n` ensures that representatives in `[-R,R]` have ordinary pairwise
separation at most `R`. Choosing the least representative cuts the circle into `[t,t+R]`.
No coefficient signs are involved in this geometric statement.

Paper: `paper/power2-ideal-svp.txt`, Section 1.3; audit Section 7.
-/

namespace Power2IdealSVP.Spin

/-- A close circular difference of magnitude at most `2R` is already close on the line. -/
theorem short_difference_unwrap {n R z k : ℤ} (hR : 0 ≤ R) (hn : 3 * R < n)
    (hz : |z| ≤ 2 * R) (hk : |z + k * n| ≤ R) : |z| ≤ R := by
  have hnpos : 0 < n := by omega
  obtain ⟨hzlo, hzhi⟩ := abs_le.mp hz
  obtain ⟨hklo, hkhi⟩ := abs_le.mp hk
  by_cases hk0 : k = 0
  · simpa [hk0] using hk
  · rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · have hmul : k * n ≤ -n := by
        nlinarith [mul_nonneg (show 0 ≤ -k - 1 by omega) hnpos.le]
      omega
    · have hmul : n ≤ k * n := by
        nlinarith [mul_nonneg (show 0 ≤ k - 1 by omega) hnpos.le]
      omega

/-- Pairwise circular distances at most `R` have a common integer interval of length `R`.

The integer `k` in the conclusion is allowed to depend on the support point. Thus the theorem
specifies a single cut, with all wraps made explicit rather than silently using cyclic indexing.
-/
theorem short_arc_integer {n R : ℤ} {W : Finset ℤ} (hW : W.Nonempty)
    (hR : 0 ≤ R) (hn : 3 * R < n)
    (hclose : ∀ x ∈ W, ∀ y ∈ W, ∃ k : ℤ, |x - y + k * n| ≤ R) :
    ∃ t : ℤ, ∀ x ∈ W, ∃ k : ℤ, t ≤ x + k * n ∧ x + k * n ≤ t + R := by
  classical
  obtain ⟨a, ha⟩ := hW
  have hrep : ∀ x : ℤ, ∃ k : ℤ, x ∈ W → |x - a + k * n| ≤ R := by
    intro x
    by_cases hx : x ∈ W
    · obtain ⟨k, hk⟩ := hclose x hx a ha
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => (hx h).elim⟩
  choose k hk using hrep
  let r : ℤ → ℤ := fun x => x - a + k x * n
  have hr : ∀ x ∈ W, |r x| ≤ R := fun x hx => hk x hx
  have hpair : ∀ x ∈ W, ∀ y ∈ W, |r x - r y| ≤ R := by
    intro x hx y hy
    obtain ⟨m, hm⟩ := hclose x hx y hy
    have hx' := abs_le.mp (hr x hx)
    have hy' := abs_le.mp (hr y hy)
    apply short_difference_unwrap hR hn (show |r x - r y| ≤ 2 * R by
      apply abs_le.mpr
      omega) (k := m - k x + k y)
    convert hm using 1
    congr 1
    dsimp [r]
    ring
  let V := W.image r
  have hV : V.Nonempty := ⟨r a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  let b := V.min' hV
  obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp (Finset.min'_mem V hV)
  refine ⟨a + b, ?_⟩
  intro x hx
  refine ⟨k x, ?_, ?_⟩
  · have hmin : b ≤ r x := Finset.min'_le V (r x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    dsimp [r] at hmin
    omega
  · have hsep := (abs_le.mp (hpair x hx y hy)).2
    change r y = b at hyb
    rw [hyb] at hsep
    dsimp [r] at hsep
    omega

/-- The usual minimum formula for circular distance supplies an explicit signed wrap. -/
theorem circular_min_close {N R : ℕ} {x y : ℤ}
    (hx : 0 ≤ x ∧ x < N) (hy : 0 ≤ y ∧ y < N)
    (hclose : min (x - y).natAbs (N - (x - y).natAbs) ≤ R) :
    ∃ k : ℤ, |x - y + k * N| ≤ R := by
  have habs : ((x - y).natAbs : ℤ) = |x - y| := Int.natCast_natAbs _
  by_cases hd : (x - y).natAbs ≤ R
  · refine ⟨0, ?_⟩
    simp only [zero_mul, add_zero]
    omega
  · have hother : N - (x - y).natAbs ≤ R := by omega
    by_cases hxy : y ≤ x
    · have ha : |x - y| = x - y := abs_of_nonneg (by omega)
      refine ⟨-1, ?_⟩
      rw [abs_of_nonpos (by omega)]
      omega
    · have ha : |x - y| = -(x - y) := abs_of_nonpos (by omega)
      refine ⟨1, ?_⟩
      rw [abs_of_nonneg (by omega)]
      omega

end Power2IdealSVP.Spin
