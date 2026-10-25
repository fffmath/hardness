module

public import Power2ModuleSVP.Seed.Intervals
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Counting polynomial sublevel runs

Prove finite interval and sampled-run counting bounds for polynomial sublevel sets. Raising the
threshold accounts for isolated tangencies without assuming simple polynomial roots.

Paper: `paper/power2svp.pdf`, Appendix A.1 (Lemma 9, Rudin–Shapiro waves and small intervals).
-/

@[expose] public section

namespace Power2ModuleSVP

open Polynomial Set

noncomputable section

/-- Alternating nonpositive witnesses and positive separators consume two
polynomial degrees per witness. All separators, including the two outer
ones, are required. -/
theorem polynomial_nonpositive_islands_bound (p : ℝ[X]) (k : ℕ)
    (inside : Fin k → ℝ) (outside : Fin (k + 1) → ℝ)
    (hmono : StrictMono outside)
    (hleft : ∀ i, outside i.castSucc < inside i)
    (hright : ∀ i, inside i < outside i.succ)
    (hinside : ∀ i, p.eval (inside i) ≤ 0)
    (houtside : ∀ i, 0 < p.eval (outside i)) :
    2 * k ≤ p.natDegree := by
  classical
  let s : Finset ℝ := Finset.univ.image (fun i => p.eval (outside i))
  have hs : s.Nonempty := ⟨p.eval (outside 0), by simp [s]⟩
  let ε : ℝ := s.min' hs / 2
  have hmin : 0 < s.min' hs := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
    rw [← hi]
    exact houtside i
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsep : ∀ i, ε < p.eval (outside i) := by
    intro i
    have hb := Finset.min'_le s (p.eval (outside i)) (by simp [s])
    dsimp [ε]
    linarith
  let q : ℝ[X] := p - C ε
  have hqin : ∀ i, q.eval (inside i) < 0 := by
    intro i
    dsimp [q]
    simp only [eval_sub, eval_C]
    linarith [hinside i]
  have hqout : ∀ i, 0 < q.eval (outside i) := by
    intro i
    simpa [q, sub_pos] using hsep i
  have hqne : q ≠ 0 := by
    intro h
    simpa [h] using hqout 0
  have hlroot : ∀ i, ∃ x ∈ Ioo (outside i.castSucc) (inside i), q.eval x = 0 := by
    intro i
    obtain ⟨x, hx, he⟩ := intermediate_value_Icc' (hleft i).le q.continuousOn
      (show (0 : ℝ) ∈ Icc (q.eval (inside i)) (q.eval (outside i.castSucc)) from
        ⟨(hqin i).le, (hqout i.castSucc).le⟩)
    change q.eval x = 0 at he
    refine ⟨x, ⟨?_, ?_⟩, he⟩
    · apply lt_of_le_of_ne hx.1
      intro h
      have := hqout i.castSucc
      rw [h, he] at this
      exact (lt_irrefl 0) this
    · apply lt_of_le_of_ne hx.2
      intro h
      have := hqin i
      rw [← h, he] at this
      exact (lt_irrefl 0) this
  have hrroot : ∀ i, ∃ x ∈ Ioo (inside i) (outside i.succ), q.eval x = 0 := by
    intro i
    obtain ⟨x, hx, he⟩ := intermediate_value_Icc (hright i).le q.continuousOn
      (show (0 : ℝ) ∈ Icc (q.eval (inside i)) (q.eval (outside i.succ)) from
        ⟨(hqin i).le, (hqout i.succ).le⟩)
    change q.eval x = 0 at he
    refine ⟨x, ⟨?_, ?_⟩, he⟩
    · apply lt_of_le_of_ne hx.1
      intro h
      have := hqin i
      rw [h, he] at this
      exact (lt_irrefl 0) this
    · apply lt_of_le_of_ne hx.2
      intro h
      have := hqout i.succ
      rw [← h, he] at this
      exact (lt_irrefl 0) this
  choose l hl hlzero using hlroot
  choose r hr hrzero using hrroot
  let root : Fin k × Bool → ℝ := fun a => if a.2 then r a.1 else l a.1
  have hroot_left : ∀ a, outside a.1.castSucc < root a := by
    intro ⟨i, b⟩
    cases b <;> simp only [root, Bool.false_eq_true, ↓reduceIte]
    · exact (hl i).1
    · exact (hleft i).trans (hr i).1
  have hroot_right : ∀ a, root a < outside a.1.succ := by
    intro ⟨i, b⟩
    cases b <;> simp only [root, Bool.false_eq_true, ↓reduceIte]
    · exact (hl i).2.trans (hright i)
    · exact (hr i).2
  have hordered : ∀ a b, a.1 < b.1 → root a < root b := by
    intro a b hab
    have hij : a.1.succ ≤ b.1.castSucc := by simpa using hab
    exact (hroot_right a).trans_le ((hmono.monotone hij).trans (hroot_left b).le)
  have hinj : Function.Injective root := by
    intro a b hab
    have hi : a.1 = b.1 := by
      rcases lt_trichotomy a.1 b.1 with h | h | h
      · exact False.elim ((ne_of_lt (hordered a b h)) hab)
      · exact h
      · exact False.elim ((ne_of_lt (hordered b a h)) hab.symm)
    rcases a with ⟨i, a⟩
    rcases b with ⟨j, b⟩
    dsimp at hi
    subst j
    have habool : a = b := by
      cases a <;> cases b <;> try rfl
      · have he : l i = r i := by simpa [root] using hab
        exact False.elim ((ne_of_lt ((hl i).2.trans (hr i).1)) he)
      · have he : r i = l i := by simpa [root] using hab
        exact False.elim ((ne_of_lt ((hl i).2.trans (hr i).1)) he.symm)
    cases habool
    rfl
  have hzero : ∀ a, q.eval (root a) = 0 := by
    intro ⟨i, b⟩
    cases b <;> simp [root, hlzero, hrzero]
  have hdegree : Fintype.card (Fin k × Bool) ≤ q.natDegree := by
    by_contra h
    exact hqne (eq_zero_of_natDegree_lt_card_of_eval_eq_zero q hinj hzero (by omega))
  have hdeg : q.natDegree = p.natDegree := by simp [q]
  simpa [hdeg, Nat.mul_comm] using hdegree

/-- A closed sublevel witness between every pair of strict separators costs
one degree of `p`. This includes witnesses attained only at tangencies. -/
theorem polynomial_sublevel_islands_bound (p : ℝ[X]) {τ : ℝ} (hτ : 0 ≤ τ)
    (k : ℕ) (inside : Fin k → ℝ) (outside : Fin (k + 1) → ℝ)
    (hmono : StrictMono outside)
    (hleft : ∀ i, outside i.castSucc < inside i)
    (hright : ∀ i, inside i < outside i.succ)
    (hinside : ∀ i, |p.eval (inside i)| ≤ τ)
    (houtside : ∀ i, τ < |p.eval (outside i)|) :
    k ≤ p.natDegree := by
  let q : ℝ[X] := p ^ 2 - C (τ ^ 2)
  have hin : ∀ i, q.eval (inside i) ≤ 0 := by
    intro i
    have hs := sq_le_sq₀ (abs_nonneg (p.eval (inside i))) hτ |>.mpr (hinside i)
    simpa [q, sq_abs, sub_nonpos] using hs
  have hout : ∀ i, 0 < q.eval (outside i) := by
    intro i
    have hs := sq_lt_sq₀ hτ (abs_nonneg (p.eval (outside i))) |>.mpr (houtside i)
    simpa [q, sq_abs, sub_pos] using hs
  have hb := polynomial_nonpositive_islands_bound q k inside outside
    hmono hleft hright hin hout
  have hdeg : q.natDegree = 2 * p.natDegree := by
    change (p ^ 2 - C (τ ^ 2)).natDegree = _
    rw [natDegree_sub_C, natDegree_pow]
  rw [hdeg] at hb
  omega


/-- Ordered rational samples can be used directly to bound the number of
marked runs. One marked witness per run and strict unmarked separators
suffice; no algebraic root-finding or genericity assumption is needed. -/
theorem polynomial_sampled_sublevel_runs_bound (p : ℝ[X]) {τ : ℝ} (hτ : 0 ≤ τ)
    {M k : ℕ} (sample : Fin M → ℝ) (hsample : StrictAnti sample)
    (marked : Fin k → Fin M) (separator : Fin (k + 1) → Fin M)
    (hleft : ∀ i, separator i.castSucc < marked i)
    (hright : ∀ i, marked i < separator i.succ)
    (hmarked : ∀ i, |p.eval (sample (marked i))| ≤ τ)
    (hseparator : ∀ i, τ < |p.eval (sample (separator i))|) :
    k ≤ p.natDegree := by
  let q : ℝ[X] := p.comp (-X)
  have hsepmono : StrictMono separator :=
    Fin.strictMono_iff_lt_succ.mpr fun i => (hleft i).trans (hright i)
  have hb := polynomial_sublevel_islands_bound q hτ k
    (fun i => -sample (marked i)) (fun i => -sample (separator i))
    (fun _ _ hij => neg_lt_neg (hsample (hsepmono hij)))
    (fun i => neg_lt_neg (hsample (hleft i)))
    (fun i => neg_lt_neg (hsample (hright i)))
    (by simpa [q] using hmarked) (by simpa [q] using hseparator)
  have hd : q.natDegree ≤ p.natDegree := by
    calc
      q.natDegree ≤ p.natDegree * (-X : ℝ[X]).natDegree := natDegree_comp_le
      _ = p.natDegree := by simp
  exact hb.trans hd

end

end Power2ModuleSVP
