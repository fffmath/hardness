import Power2ModuleSVP.Source.Boolean.Basic
import Power2ModuleSVP.Source.Boolean.Normalize
import Power2ModuleSVP.Source.Boolean.Affine

/-!
# The Boolean-to-sparse affine reduction

Compose the positive exactly-one gadget with the sparse Sidon encoding, reusing complexitylib’s
disjunctive exact-three SAT semantics. This file proves semantic correctness and size bounds;
runtime certificates are in Runtime/Source.

Paper: `paper/power2svp.pdf`, Section 4 (Proposition 2 and Lemmas 5–6).
-/
namespace Power2ModuleSVP
namespace BooleanSource
open scoped BigOperators

/-- Forget tuple order after the freshness proof; number the variables finitely. -/
def clauseFinset {v r : ℕ} (c : Triple (GadgetVar v r)) : Finset (Fin (4+2*v+6*r)) :=
  {variableFin c.1,variableFin c.2.1,variableFin c.2.2}

theorem clauseFinset_card {v r : ℕ} (c : Triple (GadgetVar v r)) (hc : Distinct c) :
    (clauseFinset c).card = 3 := by
  apply Finset.card_triple_eq_three_iff.mpr
  exact ⟨variableFin_injective.ne hc.1,variableFin_injective.ne hc.2.1,
    variableFin_injective.ne hc.2.2⟩

/-- The clause matrix consumed by the sparse polynomial construction. -/
def finiteClauses {v r : ℕ} (f : ThreeFormula v r) :
    SparseEncoding.Clauses (4+2*v+6*r) (positiveEncoding f).length :=
  fun j => clauseFinset ((positiveEncoding f)[j.val])

theorem finiteClauses_wellFormed {v r : ℕ} (f : ThreeFormula v r) :
    SparseEncoding.WellFormed (finiteClauses f) := by
  intro j
  exact clauseFinset_card _ (positiveEncoding_distinct f _ (List.getElem_mem j.isLt))

/-- Summing over the numbered clause agrees with counting the three tuple bits. -/
theorem clauseFinset_sum {v r : ℕ} (c : Triple (GadgetVar v r)) (hc : Distinct c)
    (a : Fin (4+2*v+6*r) → Bool) :
    (∑ i ∈ clauseFinset c, (if a i then (1 : ℤ) else 0)) =
      (bit (a (variableFin c.1)) + bit (a (variableFin c.2.1)) +
        bit (a (variableFin c.2.2)) : ℕ) := by
  have h1 := variableFin_injective.ne hc.1
  have h2 := variableFin_injective.ne hc.2.1
  have h3 := variableFin_injective.ne hc.2.2
  simp only [clauseFinset, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    h1,h2,h3,or_self,not_false_eq_true,Finset.sum_singleton]
  cases a (variableFin c.1) <;> cases a (variableFin c.2.1) <;>
    cases a (variableFin c.2.2) <;> norm_num

theorem finiteClauses_satisfiable_iff {v r : ℕ} (f : ThreeFormula v r) :
    SparseEncoding.Satisfiable (finiteClauses f) ↔ Satisfiable (positiveEncoding f) := by
  classical
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨fun u => a (variableFin u),fun c hc => ?_⟩
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hc
    have hh := ha ⟨j,hj⟩
    change (∑ i ∈ clauseFinset ((positiveEncoding f)[j]),
      (if a i then (1 : ℤ) else 0)) = 1 at hh
    rw [clauseFinset_sum _ (positiveEncoding_distinct f _ (List.getElem_mem hj))] at hh
    subst c
    exact_mod_cast hh
  · rintro ⟨a,ha⟩
    let extension : Fin (4+2*v+6*r) → Bool := Function.extend variableFin a (fun _ => false)
    refine ⟨extension,fun j => ?_⟩
    have hc := positiveEncoding_distinct f _ (List.getElem_mem j.isLt)
    change (∑ i ∈ clauseFinset ((positiveEncoding f)[j.val]),
      (if extension i then (1 : ℤ) else 0)) = 1
    rw [clauseFinset_sum _ hc]
    have h := ha _ (List.getElem_mem j.isLt)
    simp only [extension,variableFin_injective.extend_apply]
    exact_mod_cast h

/-- End-to-end, pure-mathematical correctness for a normalized three-literal CNF. -/
theorem boolean_affine_correct {v r : ℕ} (f : ThreeFormula v r) :
    ThreeSatisfiable f ↔ ∃ x y,
      SparseEncoding.AffineSolution (finiteClauses f)
        (SparseEncoding.positionPrime (4+2*v+6*r)) x y := by
  have hp := SparseEncoding.positionPrime_spec (4+2*v+6*r)
  exact (positiveEncoding_correct f).trans ((finiteClauses_satisfiable_iff f).symm.trans
    (SparseEncoding.affine_correct (finiteClauses f) hp.1 hp.2.1 hp.2.2.1
      (finiteClauses_wellFormed f)))

/-- The same correctness statement using the established NP-complete source's
language, with no ambiguity about the word “exact”. -/
theorem exactThreeSAT_affine_correct {v r : ℕ} (f : ThreeFormula v r) :
    toCNF f ∈ Cslib.Complexity.ExactThreeSAT ↔ ∃ x y,
      SparseEncoding.AffineSolution (finiteClauses f)
        (SparseEncoding.positionPrime (4+2*v+6*r)) x y :=
  (toCNF_mem_ExactThreeSAT_iff f).trans (boolean_affine_correct f)

/-- Every composed output has the dimension cutoff in `prop:sidon-source`. -/
theorem boolean_source_dimension {v r : ℕ} (f : ThreeFormula v r) :
    64 ≤ SparseEncoding.L (SparseEncoding.positionPrime (4+2*v+6*r))
      (4+2*v+6*r) (positiveEncoding f).length := by
  apply SparseEncoding.L_ge_64
  have hp := SparseEncoding.positionPrime_spec (4+2*v+6*r)
  have hn : 4 ≤ 4+2*v+6*r := by omega
  have hm := Nat.mul_le_mul (show 3 ≤ SparseEncoding.positionPrime (4+2*v+6*r) by omega) hn
  dsimp [SparseEncoding.B,Sidon.bound,IdealCVP.SidonPositions.erdosTuranAlpha]
  calc
    4 ≤ 2*(SparseEncoding.positionPrime (4+2*v+6*r)*(4+2*v+6*r)) := by omega
    _ = 2*SparseEncoding.positionPrime (4+2*v+6*r)*(4+2*v+6*r) := by ring
    _ ≤ _ := Nat.le_add_right _ _

/-- A concrete cubic bound in the sizes of the normalized input formula. -/
theorem boolean_source_size {v r : ℕ} (f : ThreeFormula v r) :
    SparseEncoding.L (SparseEncoding.positionPrime (4+2*v+6*r))
      (4+2*v+6*r) (positiveEncoding f).length ≤
      1125*(3+v+4*r)*(4+2*v+6*r)^2 := by
  have hp := SparseEncoding.positionPrime_spec (4+2*v+6*r)
  have hlt : SparseEncoding.positionPrime (4+2*v+6*r) < 2*(4+2*v+6*r) := by
    simpa [max_eq_left (show 2 ≤ 4+2*v+6*r by omega)] using hp.2.2.2
  have h := SparseEncoding.size_bound_nonempty hp.1.pos hlt
    (show 1 ≤ 4+2*v+6*r by omega)
    (show 1 ≤ (positiveEncoding f).length by rw [positiveEncoding_length]; omega)
  simpa [positiveEncoding_length] using h

/-- All algebraic promises, with the explicit finite-data source map. -/
theorem boolean_source_promises {v r : ℕ} (f : ThreeFormula v r) :
    let C := finiteClauses f
    let ell := SparseEncoding.positionPrime (4+2*v+6*r)
    let t := SparseEncoding.T ell (4+2*v+6*r) (positiveEncoding f).length
    let len := SparseEncoding.L ell (4+2*v+6*r) (positiveEncoding f).length
    (SparseEncoding.P C ell).natDegree = t ∧
    (SparseEncoding.P C ell).coeff 0 = 1 ∧
    (∀ z, (SparseEncoding.P C ell).coeff z = 0 ∨ (SparseEncoding.P C ell).coeff z = 1) ∧
    (SparseEncoding.P C ell).reflect t = SparseEncoding.P C ell ∧
    64 ≤ len ∧ 4*t < len ∧
    (∀ z, SparseEncoding.translation C ell z = -1 ∨
      SparseEncoding.translation C ell z = 0 ∨ SparseEncoding.translation C ell z = 1) ∧
    ∀ a : ℂ, ¬ (Polynomial.aeval a (Sidon.modulus (SparseEncoding.rationalP C ell) len) = 0 ∧
      Polynomial.aeval a (Sidon.modulus (SparseEncoding.rationalP C ell) len).reverse = 0) := by
  dsimp only
  have hp := SparseEncoding.positionPrime_spec (4+2*v+6*r)
  exact ⟨SparseEncoding.degree_P _ hp.1.pos,SparseEncoding.constant_coeff _ _,
    SparseEncoding.coeff_P_bit _ _,SparseEncoding.P_reciprocal _ hp.1.pos,
    boolean_source_dimension f,(SparseEncoding.L_spec _ _ _).1,
    SparseEncoding.translation_alphabet _ _,SparseEncoding.encoding_no_common_root _ hp.1.pos⟩

/-- The total, explicit finite-data reduction on the original 3SAT input type.
The target's polynomial is represented by its exponent set. -/
def threeSATEncode (f : Cslib.Logic.PL.CNF ℕ) : SparseEncoding.EncodedSource :=
  SparseEncoding.encode (finiteClauses (fromThreeSAT f).formula)

/-- Pure semantic reduction from complexitylib's original `ThreeSAT` language. -/
theorem threeSAT_affine_correct (f : Cslib.Logic.PL.CNF ℕ) :
    f ∈ Cslib.Complexity.ThreeSAT ↔ ∃ x y,
      SparseEncoding.AffineSolution (finiteClauses (fromThreeSAT f).formula)
        (SparseEncoding.positionPrime (4+2*(fromThreeSAT f).varCount+6*(fromThreeSAT f).rowCount)) x y :=
  (fromThreeSAT_correct f).trans (boolean_affine_correct (fromThreeSAT f).formula)

/-- Uniform cubic output dimension, independent of binary variable labels. -/
theorem threeSATEncode_size (f : Cslib.Logic.PL.CNF ℕ) :
    (threeSATEncode f).dimension ≤ 1125*(7*f.length+17)*(12*f.length+28)^2 := by
  have hc := fromThreeSAT_counts f
  have h1 : 3+(fromThreeSAT f).varCount+4*(fromThreeSAT f).rowCount ≤ 7*f.length+17 := by omega
  have h2 : 4+2*(fromThreeSAT f).varCount+6*(fromThreeSAT f).rowCount ≤ 12*f.length+28 := by omega
  calc
    _ ≤ 1125*(3+(fromThreeSAT f).varCount+4*(fromThreeSAT f).rowCount)*
        (4+2*(fromThreeSAT f).varCount+6*(fromThreeSAT f).rowCount)^2 :=
      boolean_source_size (fromThreeSAT f).formula
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left 1125 h1) (Nat.pow_le_pow_left h2 2)

end BooleanSource
end Power2ModuleSVP
