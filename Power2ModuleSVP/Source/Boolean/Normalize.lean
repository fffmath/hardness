import Power2ModuleSVP.Source.Boolean.Basic

/-!
# Normalization of the disjunctive source

Compress variables to positions in the occurrence list, so the variable count is bounded by
three times the row count. The native runtime certificate for this semantic normalization is
developed in Runtime/Source/Normalize.lean.

Paper: `paper/power2svp.pdf`, Section 4 (Proposition 2 and Lemmas 5–6).
-/
namespace Power2ModuleSVP
namespace BooleanSource
open Cslib.Logic.PL

def literalAt (f : CNF ℕ) (hw : ∀ c ∈ f, c.length = 3)
    (j : Fin f.length) (k : Fin 3) : Literal ℕ :=
  f[j.val][k.val]'(by rw [hw _ (List.getElem_mem j.isLt)]; exact k.isLt)

theorem literalAt_mem (f : CNF ℕ) (hw : ∀ c ∈ f, c.length = 3)
    (j : Fin f.length) (k : Fin 3) : literalAt f hw j k ∈ f[j.val] :=
  List.getElem_mem _

theorem literalAt_var_mem (f : CNF ℕ) (hw : ∀ c ∈ f, c.length = 3)
    (j : Fin f.length) (k : Fin 3) : (literalAt f hw j k).1 ∈ f.vars :=
  CNF.mem_vars.mpr ⟨_,List.getElem_mem j.isLt,_,literalAt_mem f hw j k⟩

/-- Finite search through the occurrence list; repeated variable labels get the
same first-occurrence index. -/
def normalize (f : CNF ℕ) (hw : ∀ c ∈ f, c.length = 3) : ThreeFormula f.vars.length f.length :=
  fun j k => (⟨f.vars.idxOf (literalAt f hw j k).1,
    List.idxOf_lt_length_iff.mpr (literalAt_var_mem f hw j k)⟩,(literalAt f hw j k).2)

theorem normalize_get (f : CNF ℕ) (hw : ∀ c ∈ f, c.length = 3)
    (j : Fin f.length) (k : Fin 3) :
    f.vars[(normalize f hw j k).1.val] = (literalAt f hw j k).1 := by
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (literalAt_var_mem f hw j k))

/-- Both directions of variable compression, with the original CNF semantics. -/
theorem normalize_correct (f : CNF ℕ) (hw : ∀ c ∈ f, c.length = 3) :
    f.Satisfiable ↔ ThreeSatisfiable (normalize f hw) := by
  classical
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨fun i => a f.vars[i.val],fun j => ?_⟩
    have hj := (CNF.eval_eq_true_iff a f).mp ha _ (List.getElem_mem j.isLt)
    obtain ⟨l,hl,he⟩ := (Clause.eval_eq_true_iff a _).mp hj
    obtain ⟨k,hk,hkl⟩ := List.mem_iff_getElem.mp hl
    have hk3 : k < 3 := by rw [← hw _ (List.getElem_mem j.isLt)]; exact hk
    refine ⟨⟨k,hk3⟩,?_⟩
    have hat : literalAt f hw j ⟨k,hk3⟩ = l := hkl
    simp only [literalValue,normalize_get]
    change (a (literalAt f hw j ⟨k,hk3⟩).1 == (literalAt f hw j ⟨k,hk3⟩).2) = true
    simpa [hat] using he
  · rintro ⟨a,ha⟩
    let extension : ℕ → Bool := fun i => if hi : i ∈ f.vars then
      a ⟨f.vars.idxOf i,List.idxOf_lt_length_iff.mpr hi⟩ else false
    refine ⟨extension,(CNF.eval_eq_true_iff extension f).mpr ?_⟩
    intro c hc
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hc
    obtain ⟨k,hk⟩ := ha ⟨j,hj⟩
    apply (Clause.eval_eq_true_iff extension _).mpr
    refine ⟨literalAt f hw ⟨j,hj⟩ k,literalAt_mem _ _ _ _,?_⟩
    simpa [literalValue,normalize,extension,literalAt_var_mem] using hk

/-- The finite size does not depend on the magnitudes of binary variable labels. -/
theorem normalize_variables_bound (f : CNF ℕ) (hw : ∀ c ∈ f, c.length = 3) :
    f.vars.length ≤ 3*f.length :=
  CNF.length_vars_le_mul_length (fun c hc => (hw c hc).le)

/-- Direct use of complexitylib's existing exact-three disjunctive source. -/
theorem normalize_mem_ExactThreeSAT_iff (f : CNF ℕ) (hw : ∀ c ∈ f, c.length = 3) :
    f ∈ Cslib.Complexity.ExactThreeSAT ↔ ThreeSatisfiable (normalize f hw) :=
  (and_iff_right hw).trans (normalize_correct f hw)

/-- A finite formula with two contradictory rows, used on malformed sources. -/
def unsatisfiableThreeFormula : ThreeFormula 1 2 := fun j _ => (0,decide (j = 0))

theorem unsatisfiableThreeFormula_not_satisfiable :
    ¬ ThreeSatisfiable unsatisfiableThreeFormula := by
  rintro ⟨a,ha⟩
  obtain ⟨i,hi⟩ := ha 0
  obtain ⟨j,hj⟩ := ha 1
  simp [literalValue,unsatisfiableThreeFormula] at hi hj
  simp_all

/-- The dimensions are carried explicitly, so normalization is a total map. -/
structure FiniteThreeFormula where
  varCount : ℕ
  rowCount : ℕ
  formula : ThreeFormula varCount rowCount

/-- Package the dependent dimensions before rewriting a total normalization. -/
def FiniteThreeFormula.Satisfiable (f : FiniteThreeFormula) : Prop := ThreeSatisfiable f.formula

/-- Every input is handled, including short or empty clauses. -/
def normalizeTotal (f : CNF ℕ) : FiniteThreeFormula :=
  if hw : ∀ c ∈ f, c.length = 3 then ⟨f.vars.length,f.length,normalize f hw⟩
  else ⟨1,2,unsatisfiableThreeFormula⟩

theorem normalizeTotal_correct (f : CNF ℕ) :
    f ∈ Cslib.Complexity.ExactThreeSAT ↔ ThreeSatisfiable (normalizeTotal f).formula := by
  change f ∈ Cslib.Complexity.ExactThreeSAT ↔ (normalizeTotal f).Satisfiable
  by_cases hw : ∀ c ∈ f, c.length = 3
  · rw [normalizeTotal,dite_eq_left hw]
    exact normalize_mem_ExactThreeSAT_iff f hw
  · rw [normalizeTotal,dite_eq_right hw]
    change (_ ∧ _) ↔ ThreeSatisfiable unsatisfiableThreeFormula
    simp [hw,unsatisfiableThreeFormula_not_satisfiable]

/-- The source has a linear number of finite variables, even on malformed inputs. -/
theorem normalizeTotal_variables_bound (f : CNF ℕ) :
    (normalizeTotal f).varCount ≤ 3*(normalizeTotal f).rowCount := by
  by_cases hw : ∀ c ∈ f, c.length = 3
  · simpa only [normalizeTotal,dite_eq_left hw] using normalize_variables_bound f hw
  · simp [normalizeTotal,hw]

/-- Reuse complexitylib's existing clause-padding reduction from `ThreeSAT`. -/
def fromThreeSAT (f : CNF ℕ) : FiniteThreeFormula :=
  normalizeTotal (Cslib.Complexity.toExactThreeSAT f)

/-- Pure semantic reduction from the established three-SAT language. -/
theorem fromThreeSAT_correct (f : CNF ℕ) :
    f ∈ Cslib.Complexity.ThreeSAT ↔ ThreeSatisfiable (fromThreeSAT f).formula :=
  (Cslib.Complexity.mem_ExactThreeSAT_toExactThreeSAT_iff f).symm.trans
    (normalizeTotal_correct (Cslib.Complexity.toExactThreeSAT f))

/-- Total normalization increases the row count only on the fixed malformed branch. -/
theorem fromThreeSAT_counts (f : CNF ℕ) :
    (fromThreeSAT f).rowCount ≤ f.length+2 ∧
    (fromThreeSAT f).varCount ≤ 3*(fromThreeSAT f).rowCount := by
  constructor
  · by_cases hw : ∀ c ∈ Cslib.Complexity.toExactThreeSAT f, c.length = 3
    · change (normalizeTotal (Cslib.Complexity.toExactThreeSAT f)).rowCount ≤ _
      rw [normalizeTotal,dite_eq_left hw]
      simp [Cslib.Complexity.toExactThreeSAT]
    · change (normalizeTotal (Cslib.Complexity.toExactThreeSAT f)).rowCount ≤ _
      rw [normalizeTotal,dite_eq_right hw]
      simp

  · exact normalizeTotal_variables_bound _

end BooleanSource
end Power2ModuleSVP
