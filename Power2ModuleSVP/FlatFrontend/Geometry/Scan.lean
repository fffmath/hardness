import Power2ModuleSVP.FlatFrontend.Enclosure.Runs

/-!
# Scan

Cell semantics of the one-pass run merger, independent of analysis.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend

/-- Every interior cell is marked, and a run ends at an unmarked cell
unless it reaches the end of the scan. The initial open run is accounted
for explicitly. -/
theorem scanCells_cells (f : ℕ → Bool) (bs : List Bool) (p : ℕ) (s : Option ℕ)
    (hvals : ∀ k (_hk : k < bs.length), bs.getD k false = f (p + k))
    (hs : ∀ a, s = some a → a < p ∧ ∀ k, a ≤ k → k < p → f k = true) :
    ∀ I ∈ scanCells p s bs,
      (∀ k, I.1 ≤ k → k < I.2 → f k = true) ∧
      (I.2 < p + bs.length → f I.2 = false) := by
  induction bs generalizing p s with
  | nil =>
    intro I hI
    cases s with
    | none => simp [scanCells] at hI
    | some a =>
      simp only [scanCells, List.mem_singleton] at hI
      subst I
      exact ⟨(hs a rfl).2, by simp⟩
  | cons b bs ih =>
    have hb : b = f p := by
      have hh := hvals 0 (by simp)
      simpa only [List.getD_cons_zero, Nat.add_zero] using hh
    have ht : ∀ k (hk : k < bs.length), bs.getD k false = f (p + 1 + k) := by
      intro k hk
      simpa only [List.getD_cons_succ, show p + (k + 1) = p + 1 + k by omega]
        using hvals (k + 1) (by simp; omega)
    have htrue (a : ℕ) (ha : a ≤ p)
        (hprev : ∀ k, a ≤ k → k < p → f k = true) (hbp : f p = true) :
        a < p + 1 ∧ ∀ k, a ≤ k → k < p + 1 → f k = true := by
      refine ⟨by omega, ?_⟩
      intro k hk hk'
      by_cases hkp : k < p
      · exact hprev k hk hkp
      · have : k = p := by omega
        simpa [this] using hbp
    intro I hI
    cases s with
    | none =>
      cases b with
      | false =>
        simp only [scanCells, Bool.false_eq_true, ↓reduceIte] at hI
        simpa only [List.length_cons, show p + (bs.length + 1) = p + 1 + bs.length by omega]
          using ih (p + 1) none ht (by simp) I hI
      | true =>
        simp only [scanCells, ↓reduceIte] at hI
        have hh := ih (p + 1) (some p) ht
          (by intro a ha; cases ha; exact htrue p le_rfl (by intro k hk hk'; omega) hb.symm) I hI
        simpa only [List.length_cons, show p + (bs.length + 1) = p + 1 + bs.length by omega] using hh
    | some a =>
      have ha := hs a rfl
      cases b with
      | true =>
        simp only [scanCells, ↓reduceIte] at hI
        have hh := ih (p + 1) (some a) ht
          (by intro a' ha'; cases ha'; exact htrue a ha.1.le ha.2 hb.symm) I hI
        simpa only [List.length_cons, show p + (bs.length + 1) = p + 1 + bs.length by omega] using hh
      | false =>
        simp only [scanCells, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hI
        rcases hI with hI | hI
        · subst I
          exact ⟨ha.2, fun _ => hb.symm⟩
        · simpa only [List.length_cons, show p + (bs.length + 1) = p + 1 + bs.length by omega]
            using ih (p + 1) none ht (by simp) I hI

/-- Every marked location in the remaining input belongs to an output run. -/
theorem scanCells_covers (f : ℕ → Bool) (bs : List Bool) (p : ℕ) (s : Option ℕ)
    (hvals : ∀ k (_hk : k < bs.length), bs.getD k false = f (p + k))
    (hs : ∀ a, s = some a → a < p) :
    ∀ k, p ≤ k → k < p + bs.length → f k = true →
      ∃ I ∈ scanCells p s bs, I.1 ≤ k ∧ k < I.2 := by
  induction bs generalizing p s with
  | nil => intro k hkp hkl _; simp only [List.length_nil, Nat.add_zero] at hkl; omega
  | cons b bs ih =>
    have hb : b = f p := by
      have hh := hvals 0 (by simp)
      simpa only [List.getD_cons_zero, Nat.add_zero] using hh
    have ht : ∀ k (hk : k < bs.length), bs.getD k false = f (p + 1 + k) := by
      intro k hk
      simpa only [List.getD_cons_succ, show p + (k + 1) = p + 1 + k by omega]
        using hvals (k + 1) (by simp; omega)
    intro k hkp hkl hmark
    cases s with
    | none =>
      cases b with
      | false =>
        have hp : p + 1 ≤ k := by
          by_contra h
          have he : k = p := by omega
          subst k
          rw [← hb] at hmark
          contradiction
        simpa only [scanCells, Bool.false_eq_true, ↓reduceIte] using
          ih (p + 1) none ht (by simp) k hp (by simp only [List.length_cons] at hkl; omega) hmark
      | true =>
        simp only [scanCells, ↓reduceIte]
        by_cases hp : p + 1 ≤ k
        · exact ih (p + 1) (some p) ht (by intro a ha; cases ha; omega)
            k hp (by simp only [List.length_cons] at hkl; omega) hmark
        · have hke : k = p := by omega
          subst k
          -- An open run persists to the next false cell or to the end.
          have aux : ∀ (cs : List Bool) (q a : ℕ), a < q →
              ∃ I ∈ scanCells q (some a) cs, I.1 = a ∧ q ≤ I.2 := by
            intro cs
            induction cs with
            | nil => intro q a ha; exact ⟨(a,q), by simp [scanCells], rfl, le_rfl⟩
            | cons c cs ih =>
              intro q a ha
              cases c with
              | false => exact ⟨(a,q), by simp [scanCells], rfl, le_rfl⟩
              | true =>
                obtain ⟨I, hI, hl, hr⟩ := ih (q + 1) a (by omega)
                exact ⟨I, by simpa [scanCells] using hI, hl, by omega⟩
          obtain ⟨I, hI, hl, hr⟩ := aux bs (p + 1) p (by omega)
          exact ⟨I, hI, by omega, by omega⟩
    | some a =>
      have ha := hs a rfl
      cases b with
      | false =>
        have hp : p + 1 ≤ k := by
          by_contra h
          have he : k = p := by omega
          subst k
          rw [← hb] at hmark
          contradiction
        obtain ⟨I, hI, hl, hr⟩ := ih (p + 1) none ht (by simp)
          k hp (by simp only [List.length_cons] at hkl; omega) hmark
        exact ⟨I, by simp [scanCells, hI], hl, hr⟩
      | true =>
        by_cases hp : p + 1 ≤ k
        · simpa only [scanCells, ↓reduceIte] using
            ih (p + 1) (some a) ht (by intro a' ha'; cases ha'; omega)
              k hp (by simp only [List.length_cons] at hkl; omega) hmark
        · have hke : k = p := by omega
          subst k
          have aux : ∀ (cs : List Bool) (q a : ℕ), a < q →
              ∃ I ∈ scanCells q (some a) cs, I.1 = a ∧ q ≤ I.2 := by
            intro cs
            induction cs with
            | nil => intro q a ha; exact ⟨(a,q), by simp [scanCells], rfl, le_rfl⟩
            | cons c cs ih =>
              intro q a ha
              cases c with
              | false => exact ⟨(a,q), by simp [scanCells], rfl, le_rfl⟩
              | true =>
                obtain ⟨I, hI, hl, hr⟩ := ih (q + 1) a (by omega)
                exact ⟨I, by simpa [scanCells] using hI, hl, by omega⟩
          obtain ⟨I, hI, hl, hr⟩ := aux bs (p + 1) a (by omega)
          exact ⟨I, by simpa [scanCells] using hI, by omega, by omega⟩

theorem intervals_cells {N : ℕ} {I : ℕ × ℕ} (hI : I ∈ intervals N) :
    (∀ k, I.1 ≤ k → k < I.2 → markedCell N k = true) ∧
    (I.2 < N / 2 → markedCell N I.2 = false) := by
  have hh := scanCells_cells (markedCell N)
    ((List.range (N / 2)).map (markedCell N)) 0 none
    (by intro k hk; simp only [List.length_map, List.length_range] at hk
        simp [List.getD_eq_getElem?_getD, hk]) (by simp) I hI
  simpa using hh

theorem intervals_cover {N k : ℕ} (hk : k < N / 2) (hm : markedCell N k = true) :
    ∃ I ∈ intervals N, I.1 ≤ k ∧ k < I.2 := by
  exact scanCells_covers (markedCell N)
    ((List.range (N / 2)).map (markedCell N)) 0 none
    (by intro k hk; simp only [List.length_map, List.length_range] at hk
        simp [List.getD_eq_getElem?_getD, hk]) (by simp) k (by omega) (by simpa) hm

/-- Seven-cell exclusion transfers directly from the Boolean marking test
 to the widths of the actual merged runs. -/
theorem intervals_width {N : ℕ}
    (hseven : ∀ j, j + 7 ≤ N / 2 → ∃ k < 7, markedCell N (j + k) = false)
    {I : ℕ × ℕ} (hI : I ∈ intervals N) : I.2 ≤ I.1 + 6 := by
  by_contra h
  have hb := intervals_bounds hI
  obtain ⟨k, hk, hm⟩ := hseven I.1 (by omega)
  have ht := (intervals_cells hI).1 (I.1 + k) (by omega) (by omega)
  rw [hm] at ht
  contradiction

/-- Cellwise axis exclusion also handles odd `N`: no artificial endpoint
cell is inserted into the scan. -/
theorem intervals_clearance {N : ℕ}
    (haxis : ∀ j, j < N / 2 → markedCell N j = true →
      100 ≤ j ∧ 2 * (j + 101) ≤ N)
    {I : ℕ × ℕ} (hI : I ∈ intervals N) :
    100 ≤ I.1 ∧ 2 * (I.2 + 100) ≤ N := by
  have hb := intervals_bounds hI
  have hl := haxis I.1 (by omega) ((intervals_cells hI).1 I.1 le_rfl hb.1)
  have hr := haxis (I.2 - 1) (by omega)
    ((intervals_cells hI).1 (I.2 - 1) (by omega) (by omega))
  constructor <;> omega

end FlatFrontend
end Power2ModuleSVP
