import Power2ModuleSVP.FlatFrontend.Geometry.Polynomial
import Power2ModuleSVP.FlatFrontend.Geometry.Scan

/-!
# Count

A component-count transfer for the actual inclusive cell scan.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend
open scoped BigOperators
noncomputable section

/-- Monotonicity suffices: strict ordering of the perturbed samples is not
needed to count runs. The separating *unmarked cell* gives the contradiction
if two run witnesses occupy the same closed polynomial sublevel component. -/
theorem intervals_count_le_degree {N R : ℕ} (_hR : 0 < R)
    (p : Polynomial ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hminus : τ < |p.eval (-1)|) (hplus : τ < |p.eval 1|)
    (node : ℕ → ℝ)
    (hrange : ∀ r ≤ (N / 2) * R, node r ∈ Set.Icc (-1) 1)
    (hanti : AntitoneOn node (Set.Icc 0 ((N / 2) * R)))
    (hmark : ∀ j, j < N / 2 → (markedCell N j = true ↔
      ∃ r, j * R ≤ r ∧ r ≤ (j + 1) * R ∧ |p.eval (node r)| ≤ τ)) :
    (intervals N).length ≤ p.natDegree := by
  classical
  let J := (intervals N).length
  let run (i : Fin J) := (intervals N).getD i (0, 0)
  have hmem (i : Fin J) : run i ∈ intervals N := getD_mem _ _ i.isLt
  have hb (i : Fin J) := intervals_bounds (hmem i)
  have hw (i : Fin J) : ∃ r, (run i).1 * R ≤ r ∧ r ≤ ((run i).1 + 1) * R ∧
      |p.eval (node r)| ≤ τ :=
    (hmark _ (by have := hb i; omega)).mp
      ((intervals_cells (hmem i)).1 _ le_rfl (hb i).1)
  choose witness hwleft hwright hwsmall using hw
  have hwend (i : Fin J) : witness i ≤ (N / 2) * R := by
    have hi : (run i).1 + 1 ≤ N / 2 := by have := hb i; omega
    exact (hwright i).trans (Nat.mul_le_mul_right R hi)
  obtain ⟨k, left, right, hk, hbounds, _, hcover⟩ :=
    polynomialSublevelComponentsHypothesis_holds.components p τ hτ hminus hplus
  have hc (i : Fin J) : ∃ c : Fin k, node (witness i) ∈ Set.Icc (left c) (right c) :=
    (hcover _ (hrange _ (hwend i))).mp (hwsmall i)
  choose component hcomponent using hc
  have hdifferent (i j : Fin J) (hsep : (run i).2 + 1 ≤ (run j).1) :
      component i ≠ component j := by
    intro heq
    have hscan : (run i).2 < N / 2 := by have := hb j; omega
    have hfalse := (intervals_cells (hmem i)).2 hscan
    have hsEnd : (run i).2 * R ≤ (N / 2) * R :=
      Nat.mul_le_mul_right R (by omega)
    have hiw : witness i ≤ (run i).2 * R :=
      (hwright i).trans (Nat.mul_le_mul_right R (by have := hb i; omega))
    have hjw : (run i).2 * R ≤ witness j :=
      (Nat.mul_le_mul_right R (by omega)).trans (hwleft j)
    have hlo := hanti ⟨Nat.zero_le _, hwend i⟩ ⟨Nat.zero_le _, hsEnd⟩ hiw
    have hhi := hanti ⟨Nat.zero_le _, hsEnd⟩ ⟨Nat.zero_le _, hwend j⟩ hjw
    have hcomp : node ((run i).2 * R) ∈ Set.Icc (left (component i)) (right (component i)) := by
      have hi := hcomponent i
      have hj := hcomponent j
      rw [← heq] at hj
      exact ⟨hj.1.trans hhi, hlo.trans hi.2⟩
    have hsmall := (hcover _ (hrange _ hsEnd)).mpr ⟨component i, hcomp⟩
    have htrue := (hmark _ hscan).mpr
      ⟨(run i).2 * R, le_rfl, Nat.mul_le_mul_right R (by omega), hsmall⟩
    rw [hfalse] at htrue
    contradiction
  have hinj : Function.Injective component := by
    intro i j heq
    by_contra hij
    rcases intervals_separated i j hij with h | h
    · exact hdifferent i j h heq
    · exact hdifferent j i h heq.symm
  have hc : J ≤ k := by
    simpa using Fintype.card_le_of_injective component hinj
  exact hc.trans hk

end
end FlatFrontend
end Power2ModuleSVP
