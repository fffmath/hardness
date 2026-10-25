module

public import Power2ModuleSVP.Coloring.Partial.Projector

/-!
# Projector Table

Materialized rational projector tables. Unlike the recursive semantic
`project`, each elimination stage stores its matrix and residual vector in
lists. Reusing those stored entries avoids an exponential expansion of the
recursive definition when evaluating many projector columns. Polynomial bit
bounds for the entries remain a separate obligation.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

open scoped BigOperators

def tableEntry (T : List (List ℚ)) (j k : ℕ) : ℚ := (T.getD j []).getD k 0

def tableApply {r : ℕ} (T : List (List ℚ)) (v : Vec r) : Vec r :=
  fun j => ∑ k : Fin r, tableEntry T j k * v k

def projectorTable {r : ℕ} : List (Vec r) → List (List ℚ)
  | [] => List.ofFn fun j : Fin r => List.ofFn (coordinate j)
  | a :: C =>
    let T := projectorTable C
    let q := List.ofFn (tableApply T a)
    let v : Vec r := fun j => q.getD j 0
    let den := dot v v
    List.ofFn fun j : Fin r => List.ofFn fun k : Fin r =>
      tableEntry T j k - v j * v k / den

private theorem getD_ofFn {α : Type} {r : ℕ} (f : Fin r → α) (j : Fin r) (d : α) :
    (List.ofFn f).getD j d = f j := by
  simp [List.getD_eq_getElem?_getD]

theorem projectorTable_spec {r : ℕ} (C : List (Vec r)) (j k : Fin r) :
    tableEntry (projectorTable C) j k = project C (coordinate j) k := by
  induction C generalizing j k with
  | nil => simp [projectorTable, tableEntry, project]
  | cons a C ih =>
    have happ (j : Fin r) : tableApply (projectorTable C) a j = project C a j := by
      unfold tableApply
      simp_rw [ih]
      change dot (project C (coordinate j)) a = project C a j
      rw [← project_selfAdjoint, dot_coordinate]
    simp only [projectorTable, tableEntry, getD_ofFn]
    simp_rw [happ]
    change tableEntry (projectorTable C) j k - project C a j * project C a k /
        dot (project C a) (project C a) = project (a :: C) (coordinate j) k
    rw [ih]
    have hd : dot (project C a) (project C (coordinate j)) = project C a j := by
      rw [dot_project_of_orthogonal C _ _ (project_orthogonal C a), dot_comm, dot_coordinate]
    simp only [project, reject, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hd]
    ring

theorem tableApply_projectorTable {r : ℕ} (C : List (Vec r)) (v : Vec r) :
    tableApply (projectorTable C) v = project C v := by
  funext j
  unfold tableApply
  simp_rw [projectorTable_spec]
  change dot (project C (coordinate j)) v = project C v j
  rw [← project_selfAdjoint, dot_coordinate]

/-- Candidate columns read from a single computed table. Symmetry of the
orthogonal projector lets its rows serve as columns. -/
def cachedColumns {r : ℕ} (C : List (Vec r)) : List (Vec r) :=
  let T := projectorTable C
  List.ofFn fun j : Fin r => fun k : Fin r => tableEntry T j k

theorem cachedColumns_eq {r : ℕ} (C : List (Vec r)) : cachedColumns C = columns C := by
  dsimp only [cachedColumns, columns]
  apply congrArg List.ofFn
  funext j k
  exact projectorTable_spec C j k

end Power2ModuleSVP.PartialColoringAlg
