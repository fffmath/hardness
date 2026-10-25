import Power2ModuleSVP.Runtime.FlatFrontend.Taylor

/-!
# Chebyshev

A common-denominator integer implementation certifies the rational
Chebyshev recurrence without assuming a bound on canonical rational states.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP.FlatFrontend
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
open ColoringRuntime
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

private def chebStep (q : ℚ) (s : ℤ × ℤ) : ℤ × ℤ :=
  (s.2, 2 * q.num * s.2 - (q.den : ℤ) ^ 2 * s.1)

private def chebIntegers (n : ℕ) (q : ℚ) : ℤ × ℤ :=
  (chebStep q)^[n] (1, q.num)

private def chebGrowth (q : ℚ) : ℕ :=
  2 * q.num.natAbs.size + 2 * q.den.size + 10

private theorem chebStep_size (q : ℚ) (s : ℤ × ℤ) :
    max (chebStep q s).1.natAbs.size (chebStep q s).2.natAbs.size ≤
      max s.1.natAbs.size s.2.natAbs.size + chebGrowth q := by
  have h₁ := Int.size_natAbs_mul_le (2 * q.num) s.2
  have h₂ := Int.size_natAbs_mul_le (2 : ℤ) q.num
  have h₃ := Int.size_natAbs_mul_le ((q.den : ℤ) ^ 2) s.1
  have h₄ := Int.size_natAbs_mul_le (q.den : ℤ) (q.den : ℤ)
  have h₅ := Int.size_natAbs_add_le (2 * q.num * s.2) (-((q.den : ℤ) ^ 2 * s.1))
  simp only [Int.natAbs_neg, Int.natAbs_natCast, ← pow_two] at h₄ h₅
  have ht : (2 : ℤ).natAbs.size = 2 := by decide
  rw [ht] at h₂
  unfold chebStep chebGrowth
  simp only at *
  simp only [sub_eq_add_neg]
  omega

@[fun_prop] private theorem chebStep_polytime : ComputableTidilyInPolyTime
    (fun a : ℚ × (ℤ × ℤ) => chebStep a.1 a.2)
    (encPair encColoringRational (encPair encIntBin encIntBin))
    (encPair encIntBin encIntBin) := by
  unfold chebStep
  fun_prop

@[fun_prop] private theorem chebIntegers_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℚ => chebIntegers a.1 a.2)
    (encPair encUnary encColoringRational) (encPair encIntBin encIntBin) := by
  let B (a : ℕ × ℚ) := a.2.num.natAbs.size + 1 + a.1 * chebGrowth a.2
  have hg : PolyBounded (fun a : ℕ × ℚ => (encPair encUnary encColoringRational a).length)
      (fun a => chebGrowth a.2) := by
    have hn : ComputableTidilyInPolyTime (fun a : ℕ × ℚ => a.2.num.natAbs.size)
        (encPair encUnary encColoringRational) encUnary := by fun_prop
    have hd : ComputableTidilyInPolyTime (fun a : ℕ × ℚ => a.2.den.size)
        (encPair encUnary encColoringRational) encUnary := by fun_prop
    exact ((PolyBounded.const 2).mul hn.polyBounded |>.add
      ((PolyBounded.const 2).mul hd.polyBounded)).add (.const 10)
  have hn : ComputableTidilyInPolyTime (fun a : ℕ × ℚ => a.2.num.natAbs.size)
      (encPair encUnary encColoringRational) encUnary := by fun_prop
  have hb : PolyBounded (fun a : ℕ × ℚ => (encPair encUnary encColoringRational a).length) B :=
    (hn.polyBounded.add (.const 1)).add ((fst encUnary encColoringRational).polyBounded.mul hg)
  unfold chebIntegers
  apply iterateWith (encPar := encColoringRational)
    (snd _ _) (fst _ _) (by fun_prop) chebStep_polytime
    (bound := fun a => 6 * B a + 5) (((PolyBounded.const 6).mul hb).add (.const 5))
  intro a i hi
  have hsize : ∀ i, max ((chebStep a.2)^[i] (1, a.2.num)).1.natAbs.size
      ((chebStep a.2)^[i] (1, a.2.num)).2.natAbs.size ≤
        a.2.num.natAbs.size + 1 + i * chebGrowth a.2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h := chebStep_size a.2 ((chebStep a.2)^[k] (1, a.2.num))
      rw [Nat.add_mul]
      omega
  have h := hsize i
  have hm : i * chebGrowth a.2 ≤ a.1 * chebGrowth a.2 := Nat.mul_le_mul_right _ hi
  simp only [length_encPair, length_encIntBin]
  dsimp [B]
  omega

private theorem chebIntegers_spec (n : ℕ) (q : ℚ) :
    chebyshevPair n q =
      (((chebIntegers n q).1 : ℚ) / (q.den : ℚ) ^ n,
       ((chebIntegers n q).2 : ℚ) / (q.den : ℚ) ^ (n + 1)) := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  induction n with
  | zero => simp [chebyshevPair, chebIntegers, q.num_div_den]
  | succ n ih =>
    have hs : chebIntegers (n + 1) q = chebStep q (chebIntegers n q) := by
      simp only [chebIntegers, Function.iterate_succ_apply']
    rw [chebyshevPair, ih, hs]
    simp only [chebStep, Int.cast_sub, Int.cast_mul,
      Int.cast_ofNat, Int.cast_pow, Int.cast_natCast]
    congr 1
    generalize (chebIntegers n q).1 = a
    generalize (chebIntegers n q).2 = b
    have hq := q.num_div_den
    generalize q.den = D at *
    generalize q.num = Z at *
    rw [← hq]
    field_simp
    ring

/-- The `chebyshevPair` program admits a native polynomial-time implementation. -/
@[fun_prop] theorem chebyshevPair_polytime : ComputableTidilyInPolyTime
    (fun a : ℕ × ℚ => chebyshevPair a.1 a.2)
    (encPair encUnary encColoringRational)
    (encPair encColoringRational encColoringRational) := by
  have h : ComputableTidilyInPolyTime (fun a : ℕ × ℚ =>
      (((chebIntegers a.1 a.2).1 : ℚ) / (a.2.den : ℚ) ^ a.1,
       ((chebIntegers a.1 a.2).2 : ℚ) / (a.2.den : ℚ) ^ (a.1 + 1)))
      (encPair encUnary encColoringRational)
      (encPair encColoringRational encColoringRational) := by fun_prop
  exact h.of_enc_eq fun a => congrArg _ (chebIntegers_spec a.1 a.2)

end Power2ModuleSVP.FlatFrontend
