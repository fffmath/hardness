import Power2ModuleSVP.Source.Boolean.Reduction
import Power2ModuleSVP.Runtime.Source.PrimeSearch

/-!
# Normalize

List normalization and the numbered positive exactly-one gadget.

Paper: `paper/power2svp.pdf`, Section 4 (Proposition 2 and Lemmas 5–6).
-/
namespace Power2ModuleSVP.SourceRuntime
open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM
open BooleanSource
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Unary variable labels paired with Boolean literal signs. -/
abbrev encLiteral := encPair encUnary encBool
/-- List encoding of clauses with unary variable labels. -/
abbrev encFormula := encList (encList encLiteral)
/-- A variable count paired with its normalized clause list. -/
abbrev NormalizedInput := ℕ × CNF ℕ
/-- Encoding of the variable count and normalized clauses. -/
abbrev encNormalized := encPair encUnary encFormula
/-- A variable count paired with positive exactly-one triples. -/
abbrev PositiveInput := ℕ × List (Triple ℕ)
/-- Unary encoding of a numbered exactly-one triple. -/
abbrev encTriple := encPair encUnary (encPair encUnary encUnary)
/-- Encoding of the positive exactly-one source instance. -/
abbrev encPositive := encPair encUnary (encList encTriple)

/-- First-occurrence indices are unary; original variable labels remain binary. -/
def compact (f : CNF ℕ) : CNF ℕ :=
  f.map fun c => c.map fun l => (f.vars.idxOf l.1, l.2)

/-- The malformed branch is the same contradictory two-row formula as the semantics. -/
def normalizeData (f : CNF ℕ) : NormalizedInput :=
  if (f.all fun c => c.length == 3) then (f.vars.length, compact f)
  else (1, [[(0, true), (0, true), (0, true)], [(0, false), (0, false), (0, false)]])

/-- The executable normalization agrees with the Boolean source normalization. -/
theorem normalizeData_eq (f : CNF ℕ) :
    normalizeData f = ((normalizeTotal f).varCount, toCNF (normalizeTotal f).formula) := by
  have htest : (f.all fun c => c.length == 3) = true ↔ ∀ c ∈ f, c.length = 3 := by
    simp
  by_cases hw : ∀ c ∈ f, c.length = 3
  · have hn : normalizeTotal f = ⟨f.vars.length, f.length, BooleanSource.normalize f hw⟩ := by
      rw [normalizeTotal, dite_eq_left hw]
    rw [hn]
    simp only [normalizeData, htest.mpr hw, ↓reduceIte, Prod.mk.injEq, true_and]
    apply List.ext_getElem
    · simp [compact, toCNF]
    · intro j hj hj'
      simp only [compact, List.getElem_map, toCNF, List.getElem_ofFn]
      apply List.ext_getElem
      · simp [hw _ (List.getElem_mem (by simpa [compact] using hj))]
      · intro k hk hk'
        simp only [List.getElem_map, List.getElem_ofFn]
        rfl
  · have hf : (f.all fun c => c.length == 3) = false := Bool.eq_false_iff.mpr
      (fun h => hw (htest.mp h))
    have hn : normalizeTotal f = ⟨1, 2, unsatisfiableThreeFormula⟩ := by
      rw [normalizeTotal, dite_eq_right hw]
    rw [hn]
    simp only [normalizeData, hf, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- Numbered code of an original variable with the given Boolean value. -/
def xCode (i : ℕ) (b : Bool) := 4 + 2 * i + (if b then 1 else 0)
/-- Numbered code of an auxiliary selector variable and its Boolean value. -/
def auxCode (v j k : ℕ) (b : Bool) := 4 + 2 * v + 6 * j + 2 * k + (if b then 1 else 0)
/-- Replace the gadget variables of a triple by their numbered codes. -/
def codeTriple {v r : ℕ} (c : Triple (GadgetVar v r)) : Triple ℕ :=
  (variableCode c.1, variableCode c.2.1, variableCode c.2.2)

/-- Ordinary range loops implement the previously proved selector gadget. -/
def positiveRows (p : NormalizedInput) : List (Triple ℕ) :=
  [(0, 1, 2), (0, 1, 3), (0, 2, 3)] ++
  (List.range p.1).map (fun i => (xCode i true, xCode i false, 1)) ++
  (List.range p.2.length).map (fun j =>
    (auxCode p.1 j 0 true, auxCode p.1 j 1 true, auxCode p.1 j 2 true)) ++
  ((List.range p.2.length).map fun j => (List.range 3).map fun k =>
    let l := (p.2.getD j []).getD k (0, false)
    (auxCode p.1 j k true, xCode l.1 (!l.2), auxCode p.1 j k false)).flatten

/-- Attach the selector gadget variable count to its positive rows. -/
def positiveData (p : NormalizedInput) : PositiveInput :=
  (4 + 2 * p.1 + 6 * p.2.length, positiveRows p)

theorem range_map_eq_ofFn {α : Type*} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem <;> simp

/-- The numbered rows are exactly the codes of the semantic selector gadget. -/
theorem positiveRows_eq {v r : ℕ} (f : ThreeFormula v r) :
    positiveRows (v, toCNF f) = (positiveEncoding f).map codeTriple := by
  simp only [positiveRows, toCNF, List.length_ofFn, range_map_eq_ofFn,
    positiveEncoding, List.map_append, List.map_ofFn, List.map_flatten]
  congr 2
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply, List.map_ofFn]
  apply congrArg List.ofFn
  funext k
  rw [List.getD_eq_getElem (List.ofFn fun j : Fin r =>
    List.ofFn fun k : Fin 3 => ((f j k).1.val, (f j k).2)) []
      (by simpa only [List.length_ofFn] using j.isLt)]
  simp only [List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using k.isLt)]
  simp only [List.getElem_ofFn]
  rfl

/-- The executable positive instance agrees with the semantic gadget instance. -/
theorem positiveData_eq {v r : ℕ} (f : ThreeFormula v r) :
    positiveData (v, toCNF f) =
      (4 + 2 * v + 6 * r, (positiveEncoding f).map codeTriple) := by
  change (4 + 2 * v + 6 * (toCNF f).length, positiveRows (v, toCNF f)) = _
  rw [positiveRows_eq]
  simp only [toCNF, List.length_ofFn]

end Power2ModuleSVP.SourceRuntime
