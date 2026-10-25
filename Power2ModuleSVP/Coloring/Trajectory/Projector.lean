module

public import Power2ModuleSVP.Coloring.Partial.Correct

/-!
# Projector

Rational trace estimates for the concrete coloring projector.  Counting
constraints, rather than choosing a basis, also covers dependent constraints.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/

@[expose] public section

namespace Power2ModuleSVP.PartialColoringAlg

open scoped BigOperators

theorem dot_add_right {r : ℕ} (u v w : Vec r) :
    dot u (v + w) = dot u v + dot u w := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_add_left {r : ℕ} (u v w : Vec r) :
    dot (u + v) w = dot u w + dot v w := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem project_norm_identity {r : ℕ} (C : List (Vec r)) (v : Vec r) :
    dot (project C v) (project C v) = dot v (project C v) := by
  rw [project_selfAdjoint, project_idempotent]
  exact dot_comm _ _

theorem project_norm_le {r : ℕ} (C : List (Vec r)) (v : Vec r) :
    dot (project C v) (project C v) ≤ dot v v := by
  have h := dot_self_nonneg (v - project C v)
  rw [dot_sub_left, dot_sub_right, dot_sub_right, dot_comm (project C v) v,
    ← project_norm_identity] at h
  linarith

/-- The sum of squared norms of the projected coordinate vectors. -/
def projectorTrace {r : ℕ} (C : List (Vec r)) : ℚ :=
  ∑ j, dot (project C (coordinate j)) (project C (coordinate j))

theorem projectorTrace_eq {r : ℕ} (C : List (Vec r)) :
    projectorTrace C = ∑ j, project C (coordinate j) j := by
  unfold projectorTrace
  simp_rw [project_norm_identity, dot_coordinate]

theorem projectorTrace_lower {r : ℕ} (C : List (Vec r)) :
    (r : ℚ) - C.length ≤ projectorTrace C := by
  induction C with
  | nil => simp [projectorTrace, project, coordinate, dot]
  | cons a C ih =>
    let q := project C a
    have hd (j : Fin r) : dot q (project C (coordinate j)) = q j := by
      rw [dot_project_of_orthogonal C _ _ (project_orthogonal C a), dot_comm,
        dot_coordinate]
    have ht : projectorTrace (a :: C) = projectorTrace C - dot q q / dot q q := by
      rw [projectorTrace_eq, projectorTrace_eq]
      change (∑ j, (project C (coordinate j) j - (dot q (project C (coordinate j)) /
        dot q q) * q j)) = _
      simp_rw [hd]
      rw [Finset.sum_sub_distrib]
      congr 1
      simp only [dot, div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [ht]
    have hdiv : dot q q / dot q q ≤ 1 := div_self_le_one _
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem projector_column_sq_sum {r : ℕ} (C : List (Vec r)) (v : Vec r) :
    (∑ j, dot v (project C (coordinate j)) ^ 2) ≤ dot v v := by
  have h (j : Fin r) : dot v (project C (coordinate j)) = project C v j := by
    rw [project_selfAdjoint, dot_comm, dot_coordinate]
  simp_rw [h]
  simpa only [dot, pow_two] using project_norm_le C v

theorem energy_quadraticRows {r m : ℕ} (a : Fin m → Row r) (s : State r m)
    (v : Vec r) :
    energy (quadraticRows a s) v = ∑ i, s.w i * (a i).threshold ^ 2 * dot (a i).a v ^ 2 := by
  simp [energy, quadraticRows, List.map_ofFn, List.sum_ofFn]

theorem quadraticRows_energy_nonneg {r m : ℕ} (a : Fin m → Row r) (s : State r m)
    (hw : ∀ i, 0 ≤ s.w i) (v : Vec r) : 0 ≤ energy (quadraticRows a s) v := by
  rw [energy_quadraticRows]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hw i) (sq_nonneg _))
    (sq_nonneg _)

theorem projector_energy_sum_le {r m : ℕ} (a : Fin m → Row r) (s : State r m)
    (C : List (Vec r)) (hw : ∀ i, 0 ≤ s.w i)
    (ha : ∀ i, dot (a i).a (a i).a ≤ 1) :
    (∑ j, energy (quadraticRows a s) (project C (coordinate j))) ≤
      ∑ i, s.w i * (a i).threshold ^ 2 := by
  simp_rw [energy_quadraticRows]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.mul_sum]
  have h := (projector_column_sq_sum C (a i).a).trans (ha i)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h
    (mul_nonneg (hw i) (sq_nonneg _))

/-- Minimum-score selection gives a trace bound without division by an
individual column's norm in the final statement. -/
theorem bestColumn_trace_bound {r m : ℕ} (a : Fin m → Row r) (s : State r m)
    (C : List (Vec r)) (hw : ∀ i, 0 ≤ s.w i)
    (ha : ∀ i, dot (a i).a (a i).a ≤ 1) :
    score (quadraticRows a s) (bestColumn (quadraticRows a s) (columns C)) *
      projectorTrace C ≤ ∑ i, s.w i * (a i).threshold ^ 2 := by
  apply le_trans _ (projector_energy_sum_le a s C hw ha)
  rw [projectorTrace, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hz : project C (coordinate j) = 0
  · simp [hz, energy_quadraticRows]
  · have hd : 0 < dot (project C (coordinate j)) (project C (coordinate j)) :=
      lt_of_le_of_ne (dot_self_nonneg _) (Ne.symm ((dot_self_eq_zero _).not.mpr hz))
    have h := bestColumn_min (quadraticRows a s) (columns C) _ (by simp [columns]) hz
    exact (le_div_iff₀ hd).mp h

theorem bestColumn_nonzero_of_trace {r : ℕ} (b : List (ℚ × Vec r))
    (C : List (Vec r)) (ht : 0 < projectorTrace C) : bestColumn b (columns C) ≠ 0 := by
  apply bestColumn_ne_zero
  by_contra hn
  push Not at hn
  have hz (j : Fin r) : project C (coordinate j) = 0 := hn _ (by simp [columns])
  simp [projectorTrace, hz] at ht

end Power2ModuleSVP.PartialColoringAlg
