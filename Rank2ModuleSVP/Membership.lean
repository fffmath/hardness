import Rank2ModuleSVP.MembershipAux

/-! Polynomial-time verification for the prime-cyclotomic SVP language. -/
namespace Rank2ModuleSVP.Membership
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Turing.MultiTapeTM Cslib.Complexity IdealCVP
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

attribute [local irreducible] List.getD

@[fun_prop] theorem poly_coeff : ComputableTidilyInPolyTime
    (fun p : (ℕ × List ℤ) × ℕ => coeff p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary (encList encIntBin)) encUnary) encIntBin := by
  unfold coeff
  fun_prop

@[fun_prop] theorem poly_cyclicCoeff : ComputableTidilyInPolyTime
    (fun p : RingArgs × ℕ => cyclicCoeff p.1.1 p.1.2.1 p.1.2.2 p.2)
    (encPair encRingArgs encUnary) encIntBin := by
  unfold cyclicCoeff
  apply intBin_sum.comp
  apply mapWithInput (encA := encUnary)
  · unfold encRingArgs
    fun_prop
  let encIn := encPair (encPair encRingArgs encUnary) encUnary
  have hq : ComputableTidilyInPolyTime
      (fun p : (RingArgs × ℕ) × ℕ => p.1.1.1) encIn encUnary := by
    unfold encIn encRingArgs
    fun_prop
  have ha : ComputableTidilyInPolyTime
      (fun p : (RingArgs × ℕ) × ℕ => p.1.1.2.1) encIn (encList encIntBin) := by
    unfold encIn encRingArgs
    fun_prop
  have hb : ComputableTidilyInPolyTime
      (fun p : (RingArgs × ℕ) × ℕ => p.1.1.2.2) encIn (encList encIntBin) := by
    unfold encIn encRingArgs
    fun_prop
  have hr : ComputableTidilyInPolyTime
      (fun p : (RingArgs × ℕ) × ℕ => p.1.2) encIn encUnary := by
    unfold encIn encRingArgs
    fun_prop
  have hi : ComputableTidilyInPolyTime
      (fun p : (RingArgs × ℕ) × ℕ => p.2) encIn encUnary := snd _ _
  have hindex := unary_mod.comp
    ((unary_sub.comp ((unary_add.comp (hr.prod hq)).prod hi)).prod hq)
  exact intBin_mul.comp ((poly_coeff.comp ((hq.prod ha).prod hi)).prod
    (poly_coeff.comp ((hq.prod hb).prod hindex)))

@[fun_prop] theorem poly_mul : ComputableTidilyInPolyTime
    (fun p : RingArgs => mul p.1 p.2.1 p.2.2) encRingArgs (encList encIntBin) := by
  unfold mul encRingArgs
  apply mapWithInput (encA := encUnary) (by fun_prop)
  have hl : ComputableTidilyInPolyTime
      (fun p : RingArgs × ℕ => p.1.1-1)
      (encPair encRingArgs encUnary) encUnary := by
    unfold encRingArgs
    fun_prop
  exact intBin_sub.comp (poly_cyclicCoeff.prod
    (poly_cyclicCoeff.comp ((fst encRingArgs encUnary).prod hl)))

@[fun_prop] theorem poly_add : ComputableTidilyInPolyTime
    (fun p : RingArgs => add p.1 p.2.1 p.2.2) encRingArgs (encList encIntBin) := by
  unfold add encRingArgs
  fun_prop

@[fun_prop] theorem poly_sub : ComputableTidilyInPolyTime
    (fun p : RingArgs => sub p.1 p.2.1 p.2.2) encRingArgs (encList encIntBin) := by
  unfold sub encRingArgs
  fun_prop

@[fun_prop] theorem poly_norm : ComputableTidilyInPolyTime
    (fun p : ℕ × List ℤ => norm p.1 p.2)
    (encPair encUnary (encList encIntBin)) encIntBin := by
  have hs : ComputableTidilyInPolyTime
      (fun p : ℕ × List ℤ => ((List.range p.1).map fun i => coeff p.1 p.2 i).sum)
      (encPair encUnary (encList encIntBin)) encIntBin := by
    apply intBin_sum.comp
    apply mapWithInput (encA := encUnary) (by fun_prop)
    exact poly_coeff
  have ht : ComputableTidilyInPolyTime
      (fun p : ℕ × List ℤ => ((List.range p.1).map fun i => (coeff p.1 p.2 i)^2).sum)
      (encPair encUnary (encList encIntBin)) encIntBin := by
    apply intBin_sum.comp
    apply mapWithInput (encA := encUnary) (by fun_prop)
    exact intBin_pow.comp (poly_coeff.prod (const 2))
  unfold norm
  fun_prop

@[fun_prop] theorem poly_pairNorm : ComputableTidilyInPolyTime
    (fun p : ℕ × (List ℤ × List ℤ) => pairNorm p.1 p.2)
    (encPair encUnary (encPair (encList encIntBin) (encList encIntBin))) encIntBin := by
  unfold pairNorm
  fun_prop

@[fun_prop] theorem poly_primeCheck : ComputableTidilyInPolyTime primeCheck encUnary encBool := by
  unfold primeCheck
  fun_prop

@[fun_prop] theorem poly_det : ComputableTidilyInPolyTime
    (fun p : PairRingArgs => det p.1 p.2.1 p.2.2) encPairRingArgs (encList encIntBin) := by
  unfold det encPairRingArgs
  fun_prop

@[fun_prop] theorem poly_wellFormedCheck : ComputableTidilyInPolyTime
    wellFormedCheck encSVP encBool := by
  unfold wellFormedCheck encSVP encModuleSIVP
  fun_prop

/-- Encoding of the two integral ring multipliers. -/
def encCertificate : (List ℤ × List ℤ) ↪ List Bool :=
  encPair (encList encIntBin) (encList encIntBin)

@[fun_prop] theorem poly_product : ComputableTidilyInPolyTime
    (fun p : SVPInput × (List ℤ × List ℤ) => product p.1 p.2)
    (encPair encSVP encCertificate) encCertificate := by
  unfold product encSVP encModuleSIVP encCertificate
  fun_prop

/-- The actual arithmetic verifier runs in polynomial time, with unary `q`. -/
@[fun_prop] theorem poly_verifier : ComputableTidilyInPolyTime
    verifier (encPair encSVP encCertificate) encBool := by
  unfold verifier encSVP encModuleSIVP encCertificate
  fun_prop

/-- Framing, signs, and the unary dimension are charged explicitly. -/
noncomputable def witnessPolynomial (B : Polynomial ℕ) : Polynomial ℕ :=
  3 * Polynomial.X * (2 * (B + 1) + 1) + 1

/-- The input encoding pays for the unary cyclotomic order. -/
theorem dimension_le_input_length (x : SVPInput) : x.q ≤ (encSVP x).length := by
  change x.1 ≤ (encSVP x).length
  simp only [encSVP, encModuleSIVP, length_encPair, encUnary_apply, List.length_replicate]
  omega

end Rank2ModuleSVP.Membership

namespace Rank2ModuleSVP
open Membership IdealCVP Turing.MultiTapeTM Cslib.Complexity

/-- Polynomial coefficient bits suffice; verifier compilation is unconditional.
The remaining premise is an arithmetic small-preimage theorem, not an NP assumption. -/
theorem moduleSVP_mem_NP_of_resource_bounds (B : Polynomial ℕ)
    (hcertificateBits : ∀ x : SVPInput, x ∈ ModuleSVPLang →
      ∃ c : List ℤ × List ℤ, verifier (x,c) = true ∧
        ∀ z ∈ c.1 ++ c.2, z.natAbs.size ≤ B.eval (encSVP x).length) :
    ModuleSVPLang ∈ NP encSVP := by
  have he : ModuleSVPLang = {x | ∃ c, verifier (x,c) = true} := by
    ext x
    exact moduleSVP_iff_exists_check x
  rw [he]
  apply mem_NP_of_witness (p := Membership.witnessPolynomial B)
    (intBinDecoder.list.pair intBinDecoder.list) poly_verifier (fun _ _ => Iff.rfl)
  intro x c hc
  have hx := (moduleSVP_iff_exists_check x).mpr ⟨c,hc⟩
  obtain ⟨c', hc', hb⟩ := hcertificateBits x hx
  obtain ⟨hl,hr,_,_⟩ := (verifier_spec x hx.1 c').mp hc'
  have hlen (l : List ℤ) (h : ∀ z ∈ l, z.natAbs.size ≤ B.eval (encSVP x).length) :
      (encList encIntBin l).length ≤ l.length * (2 * (B.eval (encSVP x).length + 1) + 1) := by
    apply length_encList_le
    intro z hz
    rw [length_encIntBin]
    have := h z hz
    omega
  have h₁ := hlen c'.1 (fun z hz => hb z (List.mem_append_left _ hz))
  have h₂ := hlen c'.2 (fun z hz => hb z (List.mem_append_right _ hz))
  have hd := dimension_le_input_length x
  refine ⟨c', hc', ?_⟩
  change (encPair (encList encIntBin) (encList encIntBin) c').length ≤ _
  rw [length_encPair]
  simp only [Membership.witnessPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  rw [hl] at h₁
  rw [hr] at h₂
  have hd' : x.q-1 ≤ (encSVP x).length := by omega
  have hm := Nat.mul_le_mul_right (2 * (B.eval (encSVP x).length + 1) + 1) hd'
  nlinarith

end Rank2ModuleSVP
