import IdealCVP.FixedIndexed
import IdealCVP.Certificates

/-! # Abstract preprocessing and advice for the fixed family

The advice is a function of the universe size alone. No bound on preprocessing,
decision time, or advice length is assumed or asserted.
-/
noncomputable section
namespace IdealCVP

/-- An exact CVP preprocessing scheme, allowing arbitrary advice. -/
structure CVPPScheme (Advice : Type*) where
  Pre : {m n : ℕ} → Matrix (Fin m) (Fin n) ℤ → Advice
  Dec : {m : ℕ} → Advice → Coeff m → ℤ → Bool
  spec : ∀ {m n} (B : Matrix (Fin m) (Fin n) ℤ) (t : Coeff m) (Δ : ℤ),
    Dec (Pre B) t Δ = true ↔ CVPYes (matrixLattice B) t Δ

/-- The fixed multiplication basis, presented as an integer matrix. -/
def fixedBasisMatrix (m : ℕ) (hm : 3 ≤ m) :
    Matrix (Fin (Fixed.baseData m hm).d) (Fin (Fixed.baseData m hm).d) ℤ :=
  multiplicationMatrix (Fixed.generator m hm)

/-- The fixed matrix generates exactly the fixed principal ideal lattice. -/
theorem matrixLattice_fixedBasisMatrix (m : ℕ) (hm : 3 ≤ m) :
    matrixLattice (fixedBasisMatrix m hm) = Fixed.lattice m hm :=
  matrixLattice_multiplication _

/-- Each column of the fixed matrix is the corresponding multiplication basis vector. -/
theorem fixedBasisMatrix_column (m : ℕ) (hm : 3 ≤ m)
    (j : Fin (Fixed.baseData m hm).d) :
    (fun i => fixedBasisMatrix m hm i j) = (Fixed.basis m hm j).val := by
  symm
  exact Cyclotomic.principalMultiplicationBasis_apply _ _ _ j

namespace CVPPScheme
variable {Advice : Type*} (S : CVPPScheme Advice)

/-- Total advice, also defined for universe sizes below three. -/
def advice (m : ℕ) : Advice :=
  if hm : 3 ≤ m then S.Pre (fixedBasisMatrix m hm)
  else S.Pre (0 : Matrix (Fin 0) (Fin 0) ℤ)

/-- This definition has no collection argument. -/
theorem advice_def (m : ℕ) :
    S.advice m = (if hm : 3 ≤ m then S.Pre (fixedBasisMatrix m hm)
      else S.Pre (0 : Matrix (Fin 0) (Fin 0) ℤ)) := rfl

/-- For a valid universe size, advice is preprocessing of its fixed basis matrix. -/
theorem advice_eq (m : ℕ) (hm : 3 ≤ m) :
    S.advice m = S.Pre (fixedBasisMatrix m hm) := dite_eq_left hm

/-- Preprocessing the basis for any mask gives the same advice. -/
theorem advice_collection (m : ℕ) (hm : 3 ≤ m) (C : Finset (Fixed.Triple m)) :
    S.Pre (multiplicationMatrix (Fixed.data m hm C).g) = S.advice m := by
  rw [Fixed.generator_independent, advice_eq S m hm]
  rfl

/-- Two collections over the same universe use identical preprocessing. -/
theorem advice_collections_eq (m : ℕ) (hm : 3 ≤ m)
    (C C' : Finset (Fixed.Triple m)) :
    S.Pre (multiplicationMatrix (Fixed.data m hm C).g) =
      S.Pre (multiplicationMatrix (Fixed.data m hm C').g) :=
  (S.advice_collection m hm C).trans (S.advice_collection m hm C').symm

end CVPPScheme

/-- The combinatorial CVPP-to-advice implication for the fixed family. -/
theorem cvpp_advice_decides {Advice : Type*} (S : CVPPScheme Advice)
    (m : ℕ) (hm : 3 ≤ m) (C : Finset (Fixed.Triple m)) :
    Fixed.HasExactCover C ↔
      S.Dec (S.advice m) (Fixed.target m hm C) (Fixed.threshold m hm C) = true := by
  rw [S.advice_eq m hm, S.spec, matrixLattice_fixedBasisMatrix]
  exact Fixed.fixed_family_correct m hm C

/-- Indexed X3C, including inputs with repeated triples, uses advice for `3 * q`. -/
theorem cvpp_advice_decides_indexed {Advice : Type*} (S : CVPPScheme Advice)
    (I : X3CInstance) :
    I.HasExactCover ↔ S.Dec (S.advice (3 * I.q))
      (Fixed.target (3 * I.q) I.fixed_universe_ge_three I.toTripleSet)
      (Fixed.threshold (3 * I.q) I.fixed_universe_ge_three I.toTripleSet) = true :=
  I.hasExactCover_iff_toTripleSet.trans
    (cvpp_advice_decides S _ I.fixed_universe_ge_three I.toTripleSet)

end IdealCVP
