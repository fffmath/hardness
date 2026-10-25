module

public import Power2ModuleSVP.Coloring.Partial.Walk
public import Complexity.Computability.Circuit.Rational.Runtime.Encode

/-!
# Arithmetic

Native multitape-machine certificates for canonical rational primitives in
the coloring encoding. These use binary integer arithmetic and gcd from
complexitylib. They do not certify the coloring loops or their intermediate
bit bounds.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.ColoringRuntime

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

@[fun_prop] theorem components_polytime :
    ComputableTidilyInPolyTime (fun q : ℚ => (q.num, q.den)) encColoringRational
      (encPair encIntBin encNat) :=
  ComputableTidilyInPolyTime.of_eq fun _ => rfl

@[fun_prop] theorem numerator_polytime :
    ComputableTidilyInPolyTime Rat.num encColoringRational encIntBin :=
  components_polytime.fst'

@[fun_prop] theorem denominator_polytime :
    ComputableTidilyInPolyTime Rat.den encColoringRational encNat :=
  components_polytime.snd'

private theorem signMagnitude_eq (z : ℤ) :
    (if z < 0 then -(z.natAbs : ℤ) else (z.natAbs : ℤ)) = z := by
  rw [Int.natCast_natAbs]
  split_ifs with h
  · rw [abs_of_neg h, neg_neg]
  · exact abs_of_nonneg (le_of_not_gt h)

/-- Canonical numerator/denominator normalization, in the exact encoding
used by `DeterministicPartialColoringHypothesis`. -/
@[fun_prop] theorem divInt_polytime :
    ComputableTidilyInPolyTime (fun p : ℤ × ℤ => Rat.divInt p.1 p.2)
      (encPair encIntBin encIntBin) encColoringRational := by
  let mag := fun p : ℤ × ℤ =>
    if p.2 = 0 then 0 else p.1.natAbs / Nat.gcd p.1.natAbs p.2.natAbs
  let den := fun p : ℤ × ℤ =>
    if p.2 = 0 then 1 else p.2.natAbs / Nat.gcd p.1.natAbs p.2.natAbs
  let sign := fun p : ℤ × ℤ =>
    if p.1 = 0 then false else if p.2 = 0 then false
    else decide (p.1 < 0) ^^ decide (p.2 < 0)
  have hz : ComputableTidilyInPolyTime (fun p : ℤ × ℤ => decide (p.2 = 0))
      (encPair encIntBin encIntBin) encBool := by fun_prop
  have hm : ComputableTidilyInPolyTime mag (encPair encIntBin encIntBin) encNat := by
    dsimp [mag]
    exact hz.ite_decide (.const 0) (by fun_prop)
  have hd : ComputableTidilyInPolyTime den (encPair encIntBin encIntBin) encNat := by
    dsimp [den]
    exact hz.ite_decide (.const 1) (by fun_prop)
  have hs : ComputableTidilyInPolyTime sign (encPair encIntBin encIntBin) encBool := by
    dsimp [sign]
    fun_prop
  have hn := intBin_signMagnitude.comp (hs.prod hm)
  exact (hn.prod hd).of_enc_eq fun p => by
    change encPair encIntBin encNat ((Rat.divInt p.1 p.2).num, (Rat.divInt p.1 p.2).den) = _
    apply congrArg (encPair encIntBin encNat)
    apply Prod.ext
    · dsimp only
      have hm' := Cslib.Circuits.Rational.divInt_num_abs_eq p.1 p.2
      have hs' := Cslib.Circuits.Rational.divInt_sign_eq p.1 p.2
      change (Rat.divInt p.1 p.2).num.natAbs = mag p at hm'
      change (Rat.divInt p.1 p.2).num = if sign p then -(mag p : ℤ) else (mag p : ℤ)
      rw [← hm']
      have hsign : sign p = decide ((Rat.divInt p.1 p.2).num < 0) := hs'.symm
      rw [hsign]
      simpa only [decide_eq_true_eq] using (signMagnitude_eq (Rat.divInt p.1 p.2).num).symm
    · exact Cslib.Circuits.Rational.divInt_den_eq p.1 p.2

variable {α : Type} {enc : α ↪ List Bool}

@[fun_prop] theorem rational_of_ints_polytime {a b : α → ℤ}
    (ha : ComputableTidilyInPolyTime a enc encIntBin)
    (hb : ComputableTidilyInPolyTime b enc encIntBin) :
    ComputableTidilyInPolyTime (fun x => (a x : ℚ) / (b x : ℚ)) enc encColoringRational :=
  (divInt_polytime.comp (ha.prod hb)).of_enc_eq fun x =>
    congrArg encColoringRational (Rat.divInt_eq_div (a x) (b x)).symm

@[fun_prop] theorem neg_polytime :
    ComputableTidilyInPolyTime (fun q : ℚ => -q) encColoringRational encColoringRational := by
  have h : ComputableTidilyInPolyTime (fun q : ℚ => (-(q.num : ℤ) : ℚ) / (q.den : ℚ))
      encColoringRational encColoringRational := by fun_prop
  exact h.of_enc_eq fun q => congrArg encColoringRational (by simp [neg_div, q.num_div_den])

@[fun_prop] theorem add_polytime :
    ComputableTidilyInPolyTime (fun p : ℚ × ℚ => p.1 + p.2)
      (encPair encColoringRational encColoringRational) encColoringRational := by
  have hn : ComputableTidilyInPolyTime (fun p : ℚ × ℚ =>
      p.1.num * (p.2.den : ℤ) + p.2.num * (p.1.den : ℤ))
      (encPair encColoringRational encColoringRational) encIntBin := by fun_prop
  have hd : ComputableTidilyInPolyTime (fun p : ℚ × ℚ =>
      (p.1.den : ℤ) * (p.2.den : ℤ))
      (encPair encColoringRational encColoringRational) encIntBin := by fun_prop
  have h := rational_of_ints_polytime hn hd
  exact h.of_enc_eq fun p => congrArg encColoringRational (by
    push_cast
    symm
    calc
      _ = (p.1.num : ℚ) / (p.1.den : ℚ) + (p.2.num : ℚ) / (p.2.den : ℚ) := by
        field_simp
      _ = _ := by rw [p.1.num_div_den, p.2.num_div_den])

@[fun_prop] theorem mul_polytime :
    ComputableTidilyInPolyTime (fun p : ℚ × ℚ => p.1 * p.2)
      (encPair encColoringRational encColoringRational) encColoringRational := by
  have hn : ComputableTidilyInPolyTime (fun p : ℚ × ℚ => p.1.num * p.2.num)
      (encPair encColoringRational encColoringRational) encIntBin := by fun_prop
  have hd : ComputableTidilyInPolyTime (fun p : ℚ × ℚ =>
      (p.1.den : ℤ) * (p.2.den : ℤ))
      (encPair encColoringRational encColoringRational) encIntBin := by fun_prop
  have h := rational_of_ints_polytime hn hd
  exact h.of_enc_eq fun p => congrArg encColoringRational (by
    push_cast
    rw [← div_mul_div_comm, p.1.num_div_den, p.2.num_div_den])

@[fun_prop] theorem inv_polytime :
    ComputableTidilyInPolyTime (fun q : ℚ => q⁻¹) encColoringRational encColoringRational := by
  have h : ComputableTidilyInPolyTime (fun q : ℚ => (q.den : ℚ) / (q.num : ℚ))
      encColoringRational encColoringRational := by fun_prop
  exact h.of_enc_eq fun q => congrArg encColoringRational (by rw [← inv_div, q.num_div_den])

@[fun_prop] theorem sub_polytime :
    ComputableTidilyInPolyTime (fun p : ℚ × ℚ => p.1 - p.2)
      (encPair encColoringRational encColoringRational) encColoringRational := by
  simpa only [sub_eq_add_neg, Function.comp_def] using add_polytime.comp
    ((fst encColoringRational encColoringRational).prod
      (neg_polytime.comp (snd encColoringRational encColoringRational)))

@[fun_prop] theorem div_polytime :
    ComputableTidilyInPolyTime (fun p : ℚ × ℚ => p.1 / p.2)
      (encPair encColoringRational encColoringRational) encColoringRational := by
  simpa only [div_eq_mul_inv, Function.comp_def] using mul_polytime.comp
    ((fst encColoringRational encColoringRational).prod
      (inv_polytime.comp (snd encColoringRational encColoringRational)))

@[fun_prop] theorem le_polytime :
    ComputableTidilyInPolyTime (fun p : ℚ × ℚ => decide (p.1 ≤ p.2))
      (encPair encColoringRational encColoringRational) encBool := by
  have h : ComputableTidilyInPolyTime (fun p : ℚ × ℚ =>
      decide (p.1.num * (p.2.den : ℤ) ≤ p.2.num * (p.1.den : ℤ)))
      (encPair encColoringRational encColoringRational) encBool := by fun_prop
  exact h.of_enc_eq fun p => by
    apply congrArg encBool
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have hi : ((p.1.num : ℚ) / (p.1.den : ℚ) ≤ (p.2.num : ℚ) / (p.2.den : ℚ)) ↔
        p.1.num * (p.2.den : ℤ) ≤ p.2.num * (p.1.den : ℤ) := by
      rw [div_le_div_iff₀ (by exact_mod_cast p.1.den_pos) (by exact_mod_cast p.2.den_pos)]
      norm_cast
    simpa only [Rat.num_div_den] using hi

@[fun_prop] theorem le_polytime' {a b : α → ℚ}
    (ha : ComputableTidilyInPolyTime a enc encColoringRational)
    (hb : ComputableTidilyInPolyTime b enc encColoringRational) :
    ComputableTidilyInPolyTime (fun x => decide (a x ≤ b x)) enc encBool :=
  le_polytime.comp (ha.prod hb)

@[fun_prop] theorem lt_polytime :
    ComputableTidilyInPolyTime (fun p : ℚ × ℚ => decide (p.1 < p.2))
      (encPair encColoringRational encColoringRational) encBool := by
  have h := bool_not.comp (le_polytime.comp
    ((snd encColoringRational encColoringRational).prod (fst encColoringRational encColoringRational)))
  exact h.of_enc_eq fun p => by
    apply congrArg encBool
    simp only [Function.comp_apply]
    apply Bool.eq_iff_iff.mpr
    simp [not_le]

@[fun_prop] theorem cubeCoordinate_polytime :
    ComputableTidilyInPolyTime (fun q : ℚ => decide (|q| ≤ 1)) encColoringRational encBool := by
  have hl : ComputableTidilyInPolyTime (fun q : ℚ => decide (-1 ≤ q))
      encColoringRational encBool := by fun_prop
  have hh : ComputableTidilyInPolyTime (fun q : ℚ => decide (q ≤ 1))
      encColoringRational encBool := by fun_prop
  exact (decide_and hl hh).of_enc_eq fun q => by
    apply congrArg encBool
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, abs_le]

@[fun_prop] theorem nearestSign_polytime :
    ComputableTidilyInPolyTime nearestRationalSign encColoringRational encColoringRational := by
  unfold nearestRationalSign
  have h : ComputableTidilyInPolyTime (fun q : ℚ => decide (0 ≤ q))
      encColoringRational encBool := by fun_prop
  exact h.ite_decide (.const 1) (.const (-1))

@[fun_prop] theorem validInput_polytime :
    ComputableTidilyInPolyTime PartialColoringAlg.validInput encPartialColoring encBool := by
  have hV : ComputableTidilyInPolyTime (fun p : PartialColoringInput => p.1)
      encPartialColoring (encList (encList encColoringRational)) := by
    unfold encPartialColoring
    fun_prop
  have hx : ComputableTidilyInPolyTime (fun p : PartialColoringInput => p.2.1)
      encPartialColoring (encList encColoringRational) := by
    unfold encPartialColoring
    fun_prop
  have hc : ComputableTidilyInPolyTime (fun p : PartialColoringInput => p.2.2)
      encPartialColoring (encList encColoringRational) := by
    unfold encPartialColoring
    fun_prop
  have hr := (length_list encColoringRational).comp hx
  have hm := (length_list (encList encColoringRational)).comp hV
  have hrowTest : ComputableTidilyInPolyTime
      (fun p : PartialColoringInput × List ℚ => decide (p.2.length = p.1.2.1.length))
      (encPair encPartialColoring (encList encColoringRational)) encBool :=
    decide_eq' ((length_list encColoringRational).comp (snd _ _)) (hr.comp (fst _ _))
  have hshape := allWithInput (test := fun (input : PartialColoringInput) (row : List ℚ) =>
    decide (row.length = input.2.1.length)) hV hrowTest
  have hlength := decide_eq' ((length_list encColoringRational).comp hc) hm
  have hcube := allWithInput (test := fun (_ : PartialColoringInput) (q : ℚ) => decide (|q| ≤ 1)) hx
    (cubeCoordinate_polytime.comp (snd encPartialColoring encColoringRational))
  have hnonneg : ComputableTidilyInPolyTime (fun q : ℚ => decide (0 ≤ q))
      encColoringRational encBool := by fun_prop
  have hnon := allWithInput (test := fun (_ : PartialColoringInput) (q : ℚ) => decide (0 ≤ q)) hc
    (hnonneg.comp (snd encPartialColoring encColoringRational))
  have h := bool_and.comp ((bool_and.comp ((bool_and.comp (hshape.prod hlength)).prod hcube)).prod hnon)
  exact h.of_enc_eq fun _ => rfl

@[fun_prop] theorem malformedFallback_polytime :
    ComputableTidilyInPolyTime (fun input : PartialColoringInput => input.2.1.map nearestRationalSign)
      encPartialColoring (encList encColoringRational) := by
  unfold encPartialColoring
  fun_prop

def rationalBits (q : ℚ) : ℕ := q.num.natAbs.size + q.den.size

/-- Normalization itself does not increase either magnitude's binary size;
the extra one covers division by zero, whose canonical value is zero. -/
theorem divInt_bits_le (a b : ℤ) :
    rationalBits (Rat.divInt a b) ≤ a.natAbs.size + b.natAbs.size + 1 := by
  by_cases hb : b = 0
  · subst b
    simp [rationalBits]
  · have hn := Cslib.Circuits.Rational.divInt_num_abs a b hb
    have hd := Cslib.Circuits.Rational.divInt_den a b hb
    unfold rationalBits
    rw [hn, hd]
    have h₁ := Nat.size_le_size (Nat.div_le_self a.natAbs (Nat.gcd a.natAbs b.natAbs))
    have h₂ := Nat.size_le_size (Nat.div_le_self b.natAbs (Nat.gcd a.natAbs b.natAbs))
    omega

end Power2ModuleSVP.ColoringRuntime
