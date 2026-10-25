module

public import Power2ModuleSVP.Coloring.Partial.Specification

/-!
# Projector

Exact rational linear algebra for the coloring walk.  `project` removes the
span of an arbitrary list of constraints, including dependent and zero rows.
Its definition uses only rational field operations and a finite recursion;
neither real comparison nor a choice of a basis occurs in the program.
This file makes no machine-time claim about that recursion.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

open scoped BigOperators

/-- A finite rational vector with `r` coordinates. -/
abbrev Vec (r : ℕ) := Fin r → ℚ

/-- The rational dot product of two finite vectors. -/
def dot {r : ℕ} (u v : Vec r) : ℚ := ∑ j, u j * v j

theorem dot_comm {r : ℕ} (u v : Vec r) : dot u v = dot v u := by
  unfold dot
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

@[simp] theorem dot_zero_left {r : ℕ} (v : Vec r) : dot 0 v = 0 := by
  simp [dot]

@[simp] theorem dot_zero_right {r : ℕ} (v : Vec r) : dot v 0 = 0 := by
  simp [dot]

theorem dot_sub_right {r : ℕ} (u v w : Vec r) :
    dot u (v - w) = dot u v - dot u w := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

theorem dot_sub_left {r : ℕ} (u v w : Vec r) :
    dot (u - v) w = dot u w - dot v w := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

theorem dot_smul_right {r : ℕ} (u v : Vec r) (c : ℚ) :
    dot u (c • v) = c * dot u v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dot_smul_left {r : ℕ} (u v : Vec r) (c : ℚ) :
    dot (c • u) v = c * dot u v := by
  rw [dot_comm, dot_smul_right, dot_comm]

theorem dot_self_nonneg {r : ℕ} (v : Vec r) : 0 ≤ dot v v := by
  exact Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)

@[simp] theorem dot_self_eq_zero {r : ℕ} (v : Vec r) : dot v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext j
    have hj : v j * v j ≤ dot v v :=
      Finset.single_le_sum (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
    have : v j = 0 := by nlinarith
    exact this
  · rintro rfl
    simp

/-- Remove one rational direction. Division by zero has its field meaning;
the zero direction therefore leaves the argument unchanged. -/
def reject {r : ℕ} (q v : Vec r) : Vec r :=
  v - (dot q v / dot q q) • q

theorem dot_reject_self {r : ℕ} (q v : Vec r) : dot q (reject q v) = 0 := by
  by_cases hq : q = 0
  · simp [hq]
  · have hn : dot q q ≠ 0 := by simpa using hq
    rw [reject, dot_sub_right, dot_smul_right, div_mul_cancel₀ _ hn, sub_self]

/-- Recursive rank-one elimination. The tail is eliminated first so that
the new constraint and argument are in the same orthogonal complement. -/
def project {r : ℕ} : List (Vec r) → Vec r → Vec r
  | [], v => v
  | a :: C, v => reject (project C a) (project C v)

/-- The vector is orthogonal to every constraint in the list. -/
def OrthogonalTo {r : ℕ} (C : List (Vec r)) (v : Vec r) : Prop :=
  ∀ a ∈ C, dot a v = 0

theorem dot_project_of_orthogonal {r : ℕ} (C : List (Vec r)) (u v : Vec r)
    (hu : OrthogonalTo C u) : dot u (project C v) = dot u v := by
  induction C generalizing v with
  | nil => rfl
  | cons a C ih =>
    have ht : OrthogonalTo C u := fun b hb => hu b (List.mem_cons_of_mem a hb)
    have ha : dot u a = 0 := by rw [dot_comm]; exact hu a (by simp)
    simp only [project, reject, dot_sub_right, dot_smul_right, ih _ ht, ha, mul_zero,
      sub_zero]

theorem project_orthogonal {r : ℕ} (C : List (Vec r)) (v : Vec r) :
    OrthogonalTo C (project C v) := by
  induction C generalizing v with
  | nil => simp [OrthogonalTo]
  | cons a C ih =>
    have ht : OrthogonalTo C (project (a :: C) v) := by
      intro b hb
      simp only [project, reject, dot_sub_right, dot_smul_right,
        ih v b hb, ih a b hb, mul_zero, sub_self]
    intro b hb
    rcases List.mem_cons.mp hb with he | hb
    · subst b
      rw [dot_comm, ← dot_project_of_orthogonal C _ a ht, dot_comm]
      exact dot_reject_self (project C a) (project C v)
    · exact ht b hb

theorem project_eq_self {r : ℕ} (C : List (Vec r)) (v : Vec r)
    (hv : OrthogonalTo C v) : project C v = v := by
  induction C with
  | nil => rfl
  | cons a C ih =>
    have ht : OrthogonalTo C v := fun b hb => hv b (List.mem_cons_of_mem a hb)
    have ha : dot v a = 0 := by rw [dot_comm]; exact hv a (by simp)
    have hq : dot (project C a) v = 0 := by
      rw [dot_comm, dot_project_of_orthogonal C _ a ht, ha]
    simp only [project, ih ht, reject, hq, zero_div, zero_smul, sub_zero]

theorem project_idempotent {r : ℕ} (C : List (Vec r)) (v : Vec r) :
    project C (project C v) = project C v :=
  project_eq_self C _ (project_orthogonal C v)

theorem project_selfAdjoint {r : ℕ} (C : List (Vec r)) (u v : Vec r) :
    dot u (project C v) = dot (project C u) v := by
  calc
    dot u (project C v) = dot (project C v) u := dot_comm _ _
    _ = dot (project C v) (project C u) :=
      (dot_project_of_orthogonal C _ u (project_orthogonal C v)).symm
    _ = dot (project C u) (project C v) := dot_comm _ _
    _ = dot (project C u) v :=
      dot_project_of_orthogonal C _ v (project_orthogonal C u)

/-- The coordinate unit vector at index `j`. -/
def coordinate {r : ℕ} (j : Fin r) : Vec r := fun k => if k = j then 1 else 0

@[simp] theorem dot_coordinate {r : ℕ} (v : Vec r) (j : Fin r) :
    dot (coordinate j) v = v j := by
  simp [dot, coordinate]

/-- All columns of the exact orthogonal projector, in coordinate order. -/
def columns {r : ℕ} (C : List (Vec r)) : List (Vec r) :=
  List.ofFn fun j => project C (coordinate j)

theorem columns_orthogonal {r : ℕ} (C : List (Vec r)) (q : Vec r)
    (hq : q ∈ columns C) : OrthogonalTo C q := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  exact project_orthogonal C _

/-- The quadratic form of the weighted row matrix; no matrix inversion is
needed to evaluate a candidate's Rayleigh quotient. -/
def energy {r : ℕ} (a : List (ℚ × Vec r)) (v : Vec r) : ℚ :=
  (a.map fun row => row.1 * dot row.2 v ^ 2).sum

/-- The weighted quadratic energy divided by the squared vector norm. -/
def score {r : ℕ} (a : List (ℚ × Vec r)) (v : Vec r) : ℚ :=
  energy a v / dot v v

/-- Stable, exact minimum over the nonzero candidates. The all-zero case
returns zero and is deliberately total. -/
def bestColumn {r : ℕ} (a : List (ℚ × Vec r)) : List (Vec r) → Vec r
  | [] => 0
  | q :: qs =>
    let b := bestColumn a qs
    if dot q q = 0 then b
    else if dot b b = 0 ∨ score a q ≤ score a b then q else b

theorem bestColumn_mem_or_zero {r : ℕ} (a : List (ℚ × Vec r)) (qs : List (Vec r)) :
    bestColumn a qs ∈ qs ∨ bestColumn a qs = 0 := by
  induction qs with
  | nil => simp [bestColumn]
  | cons q qs ih =>
    simp only [bestColumn]
    split_ifs <;> aesop

theorem bestColumn_ne_zero {r : ℕ} (a : List (ℚ × Vec r)) (qs : List (Vec r))
    (hex : ∃ q ∈ qs, q ≠ 0) : bestColumn a qs ≠ 0 := by
  induction qs with
  | nil => simp at hex
  | cons q qs ih =>
    simp only [bestColumn]
    split_ifs with hq hb
    · apply ih
      rcases hex with ⟨v, hv, hn⟩
      rcases List.mem_cons.mp hv with he | hv
      · subst v
        exact False.elim (hn ((dot_self_eq_zero q).mp hq))
      · exact ⟨v, hv, hn⟩
    · exact (dot_self_eq_zero q).not.mp hq
    · exact (dot_self_eq_zero _).not.mp (not_or.mp hb).1

theorem bestColumn_min {r : ℕ} (a : List (ℚ × Vec r)) (qs : List (Vec r))
    (v : Vec r) (hv : v ∈ qs) (hn : v ≠ 0) :
    score a (bestColumn a qs) ≤ score a v := by
  induction qs with
  | nil => simp at hv
  | cons q qs ih =>
    simp only [bestColumn]
    by_cases hq : dot q q = 0
    · simp only [hq, ↓reduceIte]
      apply ih
      rcases List.mem_cons.mp hv with he | hv
      · subst v
        exact False.elim (hn ((dot_self_eq_zero q).mp hq))
      · exact hv
    · simp only [hq, ↓reduceIte]
      by_cases hb : dot (bestColumn a qs) (bestColumn a qs) = 0 ∨
          score a q ≤ score a (bestColumn a qs)
      · simp only [hb, ↓reduceIte]
        rcases List.mem_cons.mp hv with rfl | hv
        · exact le_rfl
        · have hn' := bestColumn_ne_zero a qs ⟨v, hv, hn⟩
          have hh : score a q ≤ score a (bestColumn a qs) :=
            hb.resolve_left ((dot_self_eq_zero _).not.mpr hn')
          exact hh.trans (ih hv)
      · simp only [hb, ↓reduceIte]
        rcases List.mem_cons.mp hv with rfl | hv
        · exact le_of_lt (lt_of_not_ge (not_or.mp hb).2)
        · exact ih hv

theorem bestColumn_orthogonal {r : ℕ} (a : List (ℚ × Vec r)) (C : List (Vec r)) :
    OrthogonalTo C (bestColumn a (columns C)) := by
  rcases bestColumn_mem_or_zero a (columns C) with h | h
  · exact columns_orthogonal C _ h
  · simp [h, OrthogonalTo]

end Power2ModuleSVP.PartialColoringAlg
