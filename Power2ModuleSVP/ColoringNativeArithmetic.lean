import Power2ModuleSVP.ColoringNativeSqrt
import Power2ModuleSVP.RepairRuntime

/-!
Native certificates for the exact Taylor initialization and grid operations
in the coloring walk. Rational list sums use the common-denominator repair
routine, so their certificate includes intermediate bit lengths.
-/

namespace Power2ModuleSVP.ColoringRuntime

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open PartialColoringAlg AnchorRepairRuntime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

@[fun_prop] theorem intCast_polytime :
    ComputableTidilyInPolyTime (fun z : ℤ => (z : ℚ)) encIntBin encColoringRational := by
  simpa using rational_of_ints_polytime (id' (encIn := encIntBin)) (const 1)

@[fun_prop] theorem natCast_polytime :
    ComputableTidilyInPolyTime (fun n : ℕ => (n : ℚ)) encNat encColoringRational :=
  intCast_polytime.comp intBin_natCast

variable {α : Type} {enc : α ↪ List Bool} {a b : α → ℚ}

@[fun_prop] theorem add_polytime'
    (ha : ComputableTidilyInPolyTime a enc encColoringRational)
    (hb : ComputableTidilyInPolyTime b enc encColoringRational) :
    ComputableTidilyInPolyTime (fun x => a x + b x) enc encColoringRational :=
  (add_polytime.comp (ha.prod hb)).of_enc_eq fun _ => rfl

@[fun_prop] theorem mul_polytime'
    (ha : ComputableTidilyInPolyTime a enc encColoringRational)
    (hb : ComputableTidilyInPolyTime b enc encColoringRational) :
    ComputableTidilyInPolyTime (fun x => a x * b x) enc encColoringRational :=
  (mul_polytime.comp (ha.prod hb)).of_enc_eq fun _ => rfl

@[fun_prop] theorem div_polytime'
    (ha : ComputableTidilyInPolyTime a enc encColoringRational)
    (hb : ComputableTidilyInPolyTime b enc encColoringRational) :
    ComputableTidilyInPolyTime (fun x => a x / b x) enc encColoringRational :=
  (div_polytime.comp (ha.prod hb)).of_enc_eq fun _ => rfl

@[fun_prop] theorem intCast_polytime' {z : α → ℤ}
    (hz : ComputableTidilyInPolyTime z enc encIntBin) :
    ComputableTidilyInPolyTime (fun x => (z x : ℚ)) enc encColoringRational :=
  intCast_polytime.comp hz

@[fun_prop] theorem natCast_polytime' {z : α → ℕ}
    (hz : ComputableTidilyInPolyTime z enc encNat) :
    ComputableTidilyInPolyTime (fun x => (z x : ℚ)) enc encColoringRational :=
  natCast_polytime.comp hz

/-- A unary exponent permits polynomially many output bits. -/
@[fun_prop] theorem pow_polytime :
    ComputableTidilyInPolyTime (fun p : ℚ × ℕ => p.1 ^ p.2)
      (encPair encColoringRational encUnary) encColoringRational := by
  have hn : ComputableTidilyInPolyTime (fun p : ℚ × ℕ => p.1.num ^ p.2)
      (encPair encColoringRational encUnary) encIntBin := by fun_prop
  have hd : ComputableTidilyInPolyTime (fun p : ℚ × ℕ => (p.1.den : ℤ) ^ p.2)
      (encPair encColoringRational encUnary) encIntBin := by fun_prop
  exact (rational_of_ints_polytime hn hd).of_enc_eq fun p => by
    apply congrArg encColoringRational
    push_cast
    rw [← div_pow, p.1.num_div_den]

@[fun_prop] theorem pow_polytime' {α : Type} {enc : α ↪ List Bool}
    {q : α → ℚ} {k : α → ℕ}
    (hq : ComputableTidilyInPolyTime q enc encColoringRational)
    (hk : ComputableTidilyInPolyTime k enc encUnary) :
    ComputableTidilyInPolyTime (fun a => q a ^ k a) enc encColoringRational :=
  (pow_polytime.comp (hq.prod hk)).of_enc_eq fun _ => rfl

private def canonicalFraction (q : ℚ) : Fraction := (q.num, q.den)

@[fun_prop] private theorem canonicalFraction_polytime :
    ComputableTidilyInPolyTime canonicalFraction encColoringRational encFraction := by
  unfold canonicalFraction encFraction
  fun_prop

private theorem canonicalFraction_spec (q : ℚ) :
    0 < (canonicalFraction q).2 ∧ fractionValue (canonicalFraction q) = q :=
  ⟨by change (0 : ℤ) < (q.den : ℤ); exact_mod_cast q.den_pos, q.num_div_den⟩

/-- Exact common-denominator summation, followed by canonical reduction. -/
@[fun_prop] theorem sum_polytime :
    ComputableTidilyInPolyTime (fun xs : List ℚ => xs.sum)
      (encList encColoringRational) encColoringRational := by
  let f := fun xs : List ℚ => AnchorRepairRuntime.fractionSum (xs.map canonicalFraction)
  have hf : ComputableTidilyInPolyTime f (encList encColoringRational) encFraction := by
    dsimp [f]
    fun_prop
  have h := rational_of_ints_polytime hf.fst' hf.snd'
  exact h.of_enc_eq fun xs => by
    apply congrArg encColoringRational
    have hs := (AnchorRepairRuntime.fractionSum_spec (xs.map canonicalFraction) (by
      intro a ha
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
      exact (canonicalFraction_spec q).1)).2
    change xs.sum = fractionValue (f xs)
    rw [hs, List.map_map]
    simp only [Function.comp_def, (canonicalFraction_spec _).2]
    exact congrArg List.sum (List.map_id xs).symm

@[fun_prop] theorem prod_polytime :
    ComputableTidilyInPolyTime (fun xs : List ℚ => xs.prod)
      (encList encColoringRational) encColoringRational := by
  let f := fun xs : List ℚ => AnchorRepairRuntime.fractionProd (xs.map canonicalFraction)
  have hf : ComputableTidilyInPolyTime f (encList encColoringRational) encFraction := by
    dsimp [f]
    fun_prop
  have h := rational_of_ints_polytime hf.fst' hf.snd'
  exact h.of_enc_eq fun xs => by
    apply congrArg encColoringRational
    have hs := (AnchorRepairRuntime.fractionProd_spec (xs.map canonicalFraction) (by
      intro a ha
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha
      exact (canonicalFraction_spec q).1)).2
    change xs.prod = fractionValue (f xs)
    rw [hs, List.map_map]
    simp only [Function.comp_def, (canonicalFraction_spec _).2]
    exact congrArg List.prod (List.map_id xs).symm

private theorem floor_eq (q : ℚ) :
    ⌊q⌋ = if q.num < 0 then -(((q.num.natAbs - 1) / q.den : ℕ) : ℤ) - 1
      else ((q.num.natAbs / q.den : ℕ) : ℤ) := by
  rw [Rat.floor_def']
  cases hn : q.num with
  | ofNat n => simp
  | negSucc n =>
    obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero q.den_ne_zero
    rw [hd]
    simp only [Int.negSucc_lt_zero, ↓reduceIte, Int.natAbs_negSucc, Nat.succ_sub_one]
    change Int.negSucc (n / (d + 1)) = -((n / (d + 1) : ℕ) : ℤ) - 1
    omega

@[fun_prop] theorem floor_polytime :
    ComputableTidilyInPolyTime (fun q : ℚ => ⌊q⌋) encColoringRational encIntBin := by
  have h : ComputableTidilyInPolyTime (fun q : ℚ =>
      if q.num < 0 then -(((q.num.natAbs - 1) / q.den : ℕ) : ℤ) - 1
      else ((q.num.natAbs / q.den : ℕ) : ℤ)) encColoringRational encIntBin := by fun_prop
  exact h.of_enc_eq fun q => congrArg encIntBin (floor_eq q)

@[fun_prop] theorem ceil_polytime :
    ComputableTidilyInPolyTime (fun q : ℚ => ⌈q⌉) encColoringRational encIntBin := by
  have h : ComputableTidilyInPolyTime (fun q : ℚ => -⌊-q⌋)
      encColoringRational encIntBin := by fun_prop
  exact h.of_enc_eq fun q => congrArg encIntBin (by simp only [Int.floor_neg, neg_neg])

@[fun_prop] theorem roundUp_polytime :
    ComputableTidilyInPolyTime (fun p : ℚ × ℚ => roundUp p.1 p.2)
      (encPair encColoringRational encColoringRational) encColoringRational := by
  unfold roundUp
  fun_prop

@[fun_prop] theorem size_polytime :
    ComputableTidilyInPolyTime Nat.size encNat encUnary :=
  (encoding_length encNat).of_enc_eq fun n => by simp [encNat_apply, Nat.size_eq_bits_len]

@[fun_prop] theorem stepBudget_polytime :
    ComputableTidilyInPolyTime stepBudget encUnary encUnary := by
  unfold stepBudget
  fun_prop

@[fun_prop] theorem precision_polytime :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => precision p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  unfold precision
  apply size_polytime.comp
  apply unary_to_binary.comp
  fun_prop

@[fun_prop] theorem mesh_polytime :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => mesh p.1 p.2)
      (encPair encUnary encUnary) encColoringRational := by
  unfold mesh
  fun_prop

/-- Reuse the certified binary integer list product to compute the unary
factorial. No additional dependency artifact or numerical-size scan is
needed for the Taylor denominators. -/
@[fun_prop] theorem factorial_polytime :
    ComputableTidilyInPolyTime Nat.factorial encUnary encNat := by
  have hprod (n : ℕ) :
      ((List.range n).map fun k => ((k + 1 : ℕ) : ℤ)).prod = (n.factorial : ℤ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih]
      simp [Nat.factorial_succ, mul_comm]
  have h : ComputableTidilyInPolyTime (fun n : ℕ =>
      (((List.range n).map fun k => ((k + 1 : ℕ) : ℤ)).prod).toNat) encUnary encNat := by
    fun_prop
  exact h.of_enc_eq fun n => congrArg encNat (by rw [hprod]; simp)

/-- The rational Taylor sum uses the original term count, in unary. -/
@[fun_prop] theorem expSum_polytime :
    ComputableTidilyInPolyTime (fun p : ℚ × ℕ => expSum p.1 p.2)
      (encPair encColoringRational encUnary) encColoringRational := by
  unfold expSum
  apply sum_polytime.comp
  apply mapWithInput (range.comp (snd _ _))
  have hfac := natCast_polytime.comp (factorial_polytime.comp
    (snd (encPair encColoringRational encUnary) encUnary))
  exact (div_polytime.comp ((pow_polytime.comp
    (((fst encColoringRational encUnary).comp (fst _ _)).prod (snd _ _))).prod hfac)).of_enc_eq
      fun _ => rfl

@[fun_prop] theorem initialWeight_polytime :
    ComputableTidilyInPolyTime (fun p : (ℕ × ℕ) × ℚ => initialWeight p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encColoringRational) encColoringRational := by
  unfold initialWeight
  fun_prop

/-- Native certificates also give polynomial bounds for both canonical
components of the Taylor result, including all normalization costs. -/
theorem expSum_bits_polyBounded :
    PolyBounded (fun p : ℚ × ℕ => (encPair encColoringRational encUnary p).length)
      (fun p => rationalBits (expSum p.1 p.2)) := by
  apply expSum_polytime.polyBounded_length.mono
  intro p
  simp only [rationalBits, encColoringRational, Function.Embedding.coeFn_mk,
    length_encPair, length_encIntBin, encNat_apply, ← Nat.size_eq_bits_len]
  omega

end Power2ModuleSVP.ColoringRuntime
