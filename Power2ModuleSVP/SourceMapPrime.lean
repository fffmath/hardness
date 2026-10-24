import Power2ModuleSVP.SidonEncoding
import Rank2ModuleSVP.ReductionMap

/-! Bounded prime scans for the two searches in the sparse source. -/
namespace Power2ModuleSVP.SourceRuntime
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
open Rank2ModuleSVP.ReductionMap

/-- The first odd prime strictly above both the variable count and two. -/
def positionPrime (v : ℕ) : ℕ := primeScan (max v 2 + 1)

theorem positionPrime_eq (v : ℕ) : positionPrime v = SparseEncoding.positionPrime v := by
  have hs := SparseEncoding.positionPrime_spec v
  have hp := primeScan_prime (max v 2 + 1)
  have hi := primeScan_interval (max v 2 + 1) (by omega)
  have hle : positionPrime v ≤ SparseEncoding.positionPrime v :=
    primeScan_le _ _ (by omega) hs.1 (by omega) (by omega) (by omega)
  change primeScan (max v 2 + 1) ≤ _ at hle
  apply Nat.le_antisymm hle
  apply Nat.find_min' (SparseEncoding.existsPositionPrime v)
  change (positionPrime v).Prime ∧ _
  change _ ∧ _ ∧ v < primeScan (max v 2 + 1) ∧ _
  exact ⟨hp.1, by omega, by omega, by omega⟩

/-- Scan at most `8t+2` candidates, each tested by the imported trial division. -/
def exponentPrime (t : ℕ) : ℕ := primeScan (8*t + 1)

theorem exponentPrime_eq (ell v r : ℕ) :
    exponentPrime (SparseEncoding.T ell v r) = SparseEncoding.exponentPrime ell v r := by
  have ht := SparseEncoding.T_pos ell v r
  have hs := SparseEncoding.exponentPrime_spec ell v r
  have hp := primeScan_prime (8*SparseEncoding.T ell v r + 1)
  have hi := primeScan_interval (8*SparseEncoding.T ell v r + 1) (by omega)
  have hle : exponentPrime (SparseEncoding.T ell v r) ≤ SparseEncoding.exponentPrime ell v r :=
    primeScan_le _ _ (by omega) hs.1 (by omega) (by omega) (by omega)
  change primeScan (8*SparseEncoding.T ell v r + 1) ≤ _ at hle
  apply Nat.le_antisymm hle
  apply Nat.find_min' (SparseEncoding.existsExponentPrime ht)
  exact ⟨hp.1, by omega, by omega⟩

@[fun_prop] theorem poly_positionPrime :
    ComputableTidilyInPolyTime positionPrime encUnary encUnary := by
  unfold positionPrime
  fun_prop

@[fun_prop] theorem poly_exponentPrime :
    ComputableTidilyInPolyTime exponentPrime encUnary encUnary := by
  unfold exponentPrime
  fun_prop

end Power2ModuleSVP.SourceRuntime
