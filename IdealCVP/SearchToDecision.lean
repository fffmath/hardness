import IdealCVP.Main

/-! # Extracting exact covers from closest-vector oracles

The decoder reads one odd-block coefficient per indexed triple. It is total
and computable on arbitrary integer vectors, and agrees with the inverse of
`exactCoverEquivClosest` at distance Δ. An oracle is assumed only to return
a lattice vector with minimal squared distance.
-/
namespace IdealCVP
open IdealCVP.Cyclotomic

namespace ReductionData
variable {M n : ℕ} (D : ReductionData M n)

/-- The odd coordinate containing the Boolean coefficient for index j. -/
def selectionCoordinate (j : Fin n) : Fin D.d :=
  ⟨2 * (D.alpha j).val + 1, by
    change 2 * (D.alpha j).val + 1 < 2 * D.N
    have := (D.alpha j).isLt
    omega⟩

/-- Read the unshifted product's odd block; selected entries are exactly `2 * P`. -/
def decodeBits (v : R D.d) : Fin n → Bool :=
  fun j => decide (v (D.selectionCoordinate j) = 2 * (D.P : ℤ))

/-- Decoding an encoded lattice product recovers its Boolean selection. -/
theorem decodeBits_encoded_product (ξ : Fin n → Bool) :
    D.decodeBits (mul D.g (D.encode ξ)) = ξ := by
  funext j
  unfold decodeBits selectionCoordinate
  rw [encode, D.generator_product, interleave_odd]
  simp only [mul_zero, smul_zero, zero_add, Pi.smul_apply, smul_eq_mul, D.a_at]
  have hp : (2 * (D.P : ℤ)) ≠ 0 := by
    have := D.P_pos
    omega
  cases ξ j <;> simp [bit, Ne.symm hp]

end ReductionData

namespace X3CInstance

/-- Total extraction of an indexed collection from any returned lattice vector. -/
def decode (I : X3CInstance) (v : Coeff (x3cToCVP I).d) : Finset (Fin I.n) :=
  I.selectionEquiv.symm (I.reductionData.decodeBits v)

theorem decode_encoded_product (I : X3CInstance) (s : Finset (Fin I.n)) :
    I.decode (mul (x3cToCVP I).g (I.reductionData.encode (I.selectionEquiv s))) = s := by
  change I.selectionEquiv.symm
    (I.reductionData.decodeBits (mul I.reductionData.g
      (I.reductionData.encode (I.selectionEquiv s)))) = s
  rw [I.reductionData.decodeBits_encoded_product, Equiv.symm_apply_apply]

/-- The explicit coefficient decoder is the inverse of the established bijection. -/
theorem decode_exactCoverEquivClosest (I : X3CInstance) (s : {s // I.IsExactCover s}) :
    I.decode (exactCoverEquivClosest I s).val = s.val := by
  rw [exactCoverEquivClosest_apply]
  exact I.decode_encoded_product s.val

/-- A lattice vector at the exact threshold decodes to an indexed exact cover. -/
theorem decode_isExactCover_of_distance_eq (I : X3CInstance)
    (v : Coeff (x3cToCVP I).d)
    (hv : v ∈ principalIdealLattice (x3cToCVP I).g)
    (hd : sqNorm (v - (x3cToCVP I).T) = (x3cToCVP I).Δ) :
    I.IsExactCover (I.decode v) := by
  let w : {v : R (x3cToCVP I).d // v ∈ principalIdealLattice (x3cToCVP I).g ∧
      sqNorm (v - (x3cToCVP I).T) = (x3cToCVP I).Δ} := ⟨v, hv, hd⟩
  let s := (exactCoverEquivClosest I).symm w
  have he : (exactCoverEquivClosest I s).val = v :=
    congrArg Subtype.val ((exactCoverEquivClosest I).apply_symm_apply w)
  have hs := I.decode_exactCoverEquivClosest s
  rw [he] at hs
  rw [hs]
  exact s.property

/-- Any minimizer decodes to a cover on YES inputs, regardless of tie breaking. -/
theorem decode_closest_isExactCover (I : X3CInstance)
    (v : Coeff (x3cToCVP I).d)
    (hv : v ∈ principalIdealLattice (x3cToCVP I).g)
    (hmin : ∀ w ∈ principalIdealLattice (x3cToCVP I).g,
      sqNorm (v - (x3cToCVP I).T) ≤ sqNorm (w - (x3cToCVP I).T))
    (hy : I.HasExactCover) : I.IsExactCover (I.decode v) := by
  obtain ⟨w, hw, hd⟩ := (x3c_yes_gap I hy).1
  have hupper := hmin w hw
  rw [hd] at hupper
  exact I.decode_isExactCover_of_distance_eq v hv
    (le_antisymm hupper ((x3c_yes_gap I hy).2 v hv))

instance decidableIsExactCover (I : X3CInstance) (s : Finset (Fin I.n)) :
    Decidable (I.IsExactCover s) :=
  inferInstanceAs (Decidable (∀ i, (s.filter fun j => i ∈ I.triples j).card = 1))

/-- A finite, computable check of the extracted collection. -/
def checkDecoded (I : X3CInstance) (v : Coeff (x3cToCVP I).d) : Bool :=
  decide (I.IsExactCover (I.decode v))

theorem checkDecoded_eq_true (I : X3CInstance) (v : Coeff (x3cToCVP I).d) :
    I.checkDecoded v = true ↔ I.IsExactCover (I.decode v) := decide_eq_true_iff

end X3CInstance

/-- Mathematical closest-vector oracle on the reduction's instance family. -/
structure ClosestVectorOracle where
  vector : (I : X3CInstance) → Coeff (x3cToCVP I).d
  mem_lattice : ∀ I, vector I ∈ principalIdealLattice (x3cToCVP I).g
  minimal : ∀ I w, w ∈ principalIdealLattice (x3cToCVP I).g →
    sqNorm (vector I - (x3cToCVP I).T) ≤ sqNorm (w - (x3cToCVP I).T)

/-- A closest-vector oracle solves indexed exact-cover search on YES inputs. -/
theorem decode_oracle_isExactCover (oracle : ClosestVectorOracle)
    (I : X3CInstance) (hy : I.HasExactCover) :
    I.IsExactCover (I.decode (oracle.vector I)) :=
  I.decode_closest_isExactCover _ (oracle.mem_lattice I) (oracle.minimal I) hy

/-- Checking the extracted set decides X3C, including NO inputs. -/
theorem x3c_iff_decode_oracle (oracle : ClosestVectorOracle) (I : X3CInstance) :
    I.HasExactCover ↔ I.IsExactCover (I.decode (oracle.vector I)) :=
  ⟨decode_oracle_isExactCover oracle I, fun hs => ⟨_, hs⟩⟩

/-- A closest-vector oracle decides indexed X3C through the computable cover checker. -/
theorem x3c_iff_checkDecoded_oracle (oracle : ClosestVectorOracle) (I : X3CInstance) :
    I.HasExactCover ↔ I.checkDecoded (oracle.vector I) = true :=
  (x3c_iff_decode_oracle oracle I).trans (I.checkDecoded_eq_true _).symm

end IdealCVP
