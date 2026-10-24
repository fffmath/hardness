import Power2ModuleSVP.FlatFrontendMain

/-! Structural facts about the actual one-pass marked-run computation.
These do not require a trigonometric estimate or a sampling hypothesis. -/
namespace Power2ModuleSVP
namespace FlatFrontend

theorem scanCells_bounds (bs : List Bool) (p lo : ℕ) (s : Option ℕ)
    (hp : lo ≤ p) (hs : ∀ a, s = some a → lo ≤ a ∧ a < p) :
    ∀ I ∈ scanCells p s bs, lo ≤ I.1 ∧ I.1 < I.2 ∧ I.2 ≤ p + bs.length := by
  induction bs generalizing p lo s with
  | nil =>
    cases s with
    | none => simp [scanCells]
    | some a =>
      intro I hI
      simp only [scanCells, List.mem_singleton] at hI
      subst I
      exact ⟨(hs a rfl).1, (hs a rfl).2, by simp⟩
  | cons b bs ih =>
    intro I hI
    cases s with
    | none =>
      cases b with
      | false =>
        simp only [scanCells, Bool.false_eq_true, ↓reduceIte] at hI
        have hb := ih (p + 1) lo none (by omega) (by simp) I hI
        exact ⟨hb.1, hb.2.1, by simp only [List.length_cons]; omega⟩
      | true =>
        simp only [scanCells, ↓reduceIte] at hI
        have hb := ih (p + 1) lo (some p) (by omega)
          (by intro a ha; cases ha; exact ⟨hp, by omega⟩) I hI
        exact ⟨hb.1, hb.2.1, by simp only [List.length_cons]; omega⟩
    | some a =>
      have ha := hs a rfl
      cases b with
      | false =>
        simp only [scanCells, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hI
        rcases hI with hI | hI
        · subst I
          exact ⟨ha.1, ha.2, by simp⟩
        · have hb := ih (p + 1) lo none (by omega) (by simp) I hI
          exact ⟨hb.1, hb.2.1, by simp only [List.length_cons]; omega⟩
      | true =>
        simp only [scanCells, ↓reduceIte] at hI
        have hb := ih (p + 1) lo (some a) (by omega)
          (by intro a' ha'; cases ha'; exact ⟨ha.1, by omega⟩) I hI
        exact ⟨hb.1, hb.2.1, by simp only [List.length_cons]; omega⟩

theorem scanCells_pairwise (bs : List Bool) (p : ℕ) (s : Option ℕ) :
    (scanCells p s bs).Pairwise (fun I J => I.2 + 1 ≤ J.1) := by
  induction bs generalizing p s with
  | nil => cases s <;> simp [scanCells]
  | cons b bs ih =>
    cases s with
    | none =>
      cases b with
      | false => simpa [scanCells] using ih (p + 1) none
      | true => simpa [scanCells] using ih (p + 1) (some p)
    | some a =>
      cases b with
      | true => simpa [scanCells] using ih (p + 1) (some a)
      | false =>
        simp only [scanCells, Bool.false_eq_true, ↓reduceIte, List.pairwise_cons]
        constructor
        · intro J hJ
          exact (scanCells_bounds bs (p + 1) (p + 1) none le_rfl (by simp) J hJ).1
        · exact ih (p + 1) none

theorem intervals_bounds {N : ℕ} {I : ℕ × ℕ} (hI : I ∈ intervals N) :
    I.1 < I.2 ∧ I.2 ≤ N / 2 := by
  have hh := scanCells_bounds ((List.range (N / 2)).map (markedCell N)) 0 0 none
    le_rfl (by simp) I hI
  simpa only [List.length_map, List.length_range, Nat.zero_add] using hh.2

theorem intervals_pairwise (N : ℕ) :
    (intervals N).Pairwise (fun I J => I.2 + 1 ≤ J.1) :=
  scanCells_pairwise _ _ _

/-- Both structural fields needed by `SeedKernelIntervals` hold for the
computed runs before any analytic width or clearance estimate. -/
theorem intervals_separated {N : ℕ} (i j : Fin (intervals N).length) (hij : i ≠ j) :
    ((intervals N).getD i (0, 0)).2 + 1 ≤ ((intervals N).getD j (0, 0)).1 ∨
      ((intervals N).getD j (0, 0)).2 + 1 ≤ ((intervals N).getD i (0, 0)).1 := by
  have hp := intervals_pairwise N
  have hlt : i.val < j.val ∨ j.val < i.val := by
    have hn : i.val ≠ j.val := fun h => hij (Fin.ext h)
    omega
  rw [List.pairwise_iff_getElem] at hp
  rcases hlt with h | h
  · left
    simpa [List.getD_eq_getElem?_getD, i.isLt, j.isLt] using hp i.val j.val i.isLt j.isLt h
  · right
    simpa [List.getD_eq_getElem?_getD, i.isLt, j.isLt] using hp j.val i.val j.isLt i.isLt h

/-- Canonical endpoints: there is no choice of a real interval family. -/
def runLeft (d : ℕ) (i : Fin (intervalCount d)) : ℕ :=
  ((intervals (seedN d)).getD i (0, 0)).1

def runRight (d : ℕ) (i : Fin (intervalCount d)) : ℕ :=
  ((intervals (seedN d)).getD i (0, 0)).2

def runContains (d : ℕ) (θ : ℝ) : Prop :=
  ∃ i : Fin (intervalCount d), θ ∈ Set.Icc
    (runLeft d i * Real.pi / seedN d) (runRight d i * Real.pi / seedN d)

/-- Precisely the analytic/combinatorial estimates still needed for the
computed runs. Positivity, endpoint range and separation have been proved
above and are deliberately absent from this residual hypothesis. -/
structure MarkedRunEstimates (d : ℕ) : Prop where
  width : ∀ i, runRight d i ≤ runLeft d i + 6
  left_clearance : ∀ i, 100 ≤ runLeft d i
  right_clearance : ∀ i, 2 * (runRight d i + 100) ≤ seedN d
  count : intervalCount d * 2 ^ 66 ≤ seedN d
  cosine_good : ∀ θ, ¬ runContains d (foldAngle θ) →
    seedCosineMargin * Real.sqrt (seedN d) ≤ |cosine d θ|
  even_bound : ∀ θ, |evenPart d θ| ≤ 6 * Real.sqrt (seedN d)

/-- The integer scan supplies the interval data. Only the listed analytic
estimates remain as premises. -/
def markedKernelIntervals {d : ℕ} (h : MarkedRunEstimates d) :
    SeedKernelIntervals (seedN d) (intervalCount d) where
  left := runLeft d
  right := runRight d
  width_pos := fun i => (intervals_bounds
    (getD_mem (intervals (seedN d)) (0, 0) i.isLt)).1
  width_le := h.width
  left_clearance := h.left_clearance
  right_clearance := h.right_clearance
  separated := intervals_separated

/-- Geometry data now constructed from the actual list of marked runs. -/
def geometryCertificate_of_estimates {d : ℕ} (h : MarkedRunEstimates d) :
    GeometryCertificate d where
  kernelIntervals := markedKernelIntervals h
  left_eq := fun _ => rfl
  right_eq := fun _ => rfl
  count := h.count
  cosine_good := h.cosine_good
  even_bound := h.even_bound

end FlatFrontend
end Power2ModuleSVP
