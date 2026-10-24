import IdealCVP.Complexity.ListRing
import IdealCVP.CertificateBound
import Complexity.Computability.Complexity.Classes.NP.Witness

/-! # Bounded integer-list certificates for principal CVP

The mathematical certificate theorem includes the zero-generator case. The NP
bridge separates the resource certificates discharged in `CertificateBits` and
`Verifier`.
-/
namespace IdealCVP
open Cslib.Complexity Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- The existing Cramer bound applied to the multiplication basis. -/
def cvpCertificateBound (x : CVPInput) : ℤ :=
  certificateBound (multiplicationMatrix (ofList (d := x.1) x.2.1))
    (ofList x.2.2.1) x.2.2.2

theorem cvpCertificateBound_nonneg (x : CVPInput) : 0 ≤ cvpCertificateBound x := by
  unfold cvpCertificateBound certificateBound
  apply mul_nonneg (by positivity)
  apply pow_nonneg
  have := basisMagnitude_nonneg (multiplicationMatrix (ofList (d := x.1) x.2.1))
  have := targetMagnitude_nonneg (ofList (d := x.1) x.2.2.1)
  have := abs_nonneg x.2.2.2
  omega

/-- Every YES instance has a bounded list certificate. If `g=0`, take `q=0`. -/
theorem principalCVP_bounded_list (x : CVPInput) (hx : x ∈ PrincipalCVP) :
    ∃ q : List ℤ, cvpCheck (x, q) = true ∧ ∀ z ∈ q, |z| ≤ cvpCertificateBound x := by
  obtain ⟨hw, hcvp⟩ := (principalCVP_iff x).mp hx
  by_cases hg : ofList (d := x.1) x.2.1 = 0
  · obtain ⟨q, hq⟩ := hx.2
    have hz : sqNorm (Cyclotomic.mul (ofList (d := x.1) x.2.1) 0 -
        ofList x.2.2.1) ≤ x.2.2.2 := by
      simpa [hg, Cyclotomic.mul_comm 0] using hq
    refine ⟨toList (0 : Coeff x.1), (cvpCheck_eq x _).mpr ⟨hw, length_toList _, ?_⟩, ?_⟩
    · simpa using hz
    · intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact cvpCertificateBound_nonneg x
  · obtain ⟨q, hbound, hq⟩ := (principal_cvp_iff_bounded_certificate hw.1 _ hg _ _).mp hcvp
    refine ⟨toList q, (cvpCheck_eq x _).mpr ⟨hw, length_toList _, ?_⟩, ?_⟩
    · rw [verify_eq_true, multiplicationMatrix_mulVec] at hq
      simpa using hq
    · intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact hbound i

/-- Framing costs are included in this integer-list encoding bound. -/
theorem intList_encoding_length_le (q : List ℤ) (B : ℤ) (hB : 0 ≤ B)
    (hq : ∀ z ∈ q, |z| ≤ B) :
    (encList encIntBin q).length ≤ q.length * (2 * (B.toNat.size + 1) + 1) := by
  apply length_encList_le
  intro z hz
  rw [length_encIntBin]
  apply Nat.add_le_add_right
  apply Nat.size_le_size
  have h := hq z hz
  have hcast := Int.natCast_natAbs z
  have hcastB := Int.toNat_of_nonneg hB
  omega

/-- Total signed-binary decoder, including malformed words. -/
def decodeIntBin (w : List Bool) : ℤ :=
  if w.headD false then -(Decoder.nat.decode w.tail : ℤ)
  else (Decoder.nat.decode w.tail : ℤ)

@[fun_prop] theorem poly_decodeIntBin :
    ComputableTidilyInPolyTime decodeIntBin encBits encIntBin := by
  unfold decodeIntBin
  have hn := Decoder.nat.computableTidilyInPolyTime
  fun_prop

def intBinDecoder : Decoder encIntBin where
  decode := decodeIntBin
  decode_enc z := by
    cases z with
    | ofNat n =>
      change decodeIntBin (encIntBin (n : ℤ)) = (n : ℤ)
      simp only [encIntBin_natCast, decodeIntBin, List.headD_cons, Bool.false_eq_true,
        ↓reduceIte, List.tail_cons, ← encNat_apply, Decoder.decode_enc]
    | negSucc n =>
      simp only [encIntBin_negSucc, decodeIntBin, List.headD_cons, ↓reduceIte,
        List.tail_cons, ← encNat_apply, Decoder.decode_enc]
      omega
  computable := poly_decodeIntBin.exists_degree

/-- Target bit bound, proved in `CertificateBits.lean`. All integer-list
framing and sign bits are then absorbed by `witnessPolynomial`. -/
def certificateBitBound (N : ℕ) : ℕ := 7 * (N + 1)^2

noncomputable def witnessPolynomial : Polynomial ℕ :=
  Polynomial.X * (2 * (7 * (Polynomial.X + 1)^2 + 1) + 1)

/-- NP membership from checker and bit-size certificates.
No complexity-class membership is itself assumed. -/
theorem principalCVP_mem_NP_of_resource_bounds
    (hcheckPoly : ComputableTidilyInPolyTime cvpCheck
      (encPair encCVP (encList encIntBin)) encBool)
    (hcertificateBits : ∀ x : CVPInput, x.WellFormed →
      (cvpCertificateBound x).toNat.size ≤ certificateBitBound (encCVP x).length) :
    PrincipalCVP ∈ NP encCVP := by
  have hlang : PrincipalCVP = {x | ∃ q : List ℤ, cvpCheck (x, q) = true} := by
    ext x
    exact principalCVP_iff_exists_check x
  rw [hlang]
  apply mem_NP_of_witness (p := witnessPolynomial) intBinDecoder.list hcheckPoly
    (fun _ _ => Iff.rfl)
  intro x q hq
  have hx : x ∈ PrincipalCVP := (principalCVP_iff_exists_check x).mpr ⟨q, hq⟩
  obtain ⟨q', hq', hb⟩ := principalCVP_bounded_list x hx
  have hlen := intList_encoding_length_le q' _ (cvpCertificateBound_nonneg x) hb
  have hbits := hcertificateBits x hx.1
  have hd : x.1 ≤ (encCVP x).length := by
    have h := length_le_encPair_left encUnary
      (encPair (encList encIntBin) (encPair (encList encIntBin) encIntBin)) x
    simpa only [encCVP, encUnary_apply, List.length_replicate] using h
  have hq'len := ((cvpCheck_eq x q').mp hq').2.1
  refine ⟨q', hq', ?_⟩
  simp only [witnessPolynomial, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]
  rw [hq'len] at hlen
  exact hlen.trans (Nat.mul_le_mul hd (by unfold certificateBitBound at hbits; omega))

end IdealCVP
