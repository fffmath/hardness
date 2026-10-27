import Power2ModuleSVPSubsetSum.Problem
import Power2ModuleSVPSubsetSum.Reduction.UnitAction

/-! # Integral shortest-vector gaps

Elementary consequences of the natural-valued coefficient maximum norm. These lemmas
convert short-vector correctness and exact short-vector norms into first-minimum statements.

Paper: `paper/power2svp-subsetsum.pdf`, Proposition 4.2.
-/
namespace Power2ModuleSVPSubsetSum.Reduction
open Power2ModuleSVP (Coeff pairSup moduleVector FirstMinimum)

/-- Every nonzero integral coefficient pair has maximum norm at least one. -/
theorem one_le_pairSup_of_ne_zero {d : ℕ} (v : Coeff d × Coeff d) (hv : v ≠ 0) :
    1 ≤ pairSup v := by
  have h : pairSup v ≠ 0 := fun h => hv ((pairSup_eq_zero_iff v).mp h)
  omega

/-- Nonzero coefficient pairs have positive maximum norm. -/
theorem pairSup_pos_iff {d : ℕ} (v : Coeff d × Coeff d) :
    0 < pairSup v ↔ v ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, pairSup_eq_zero_iff]

/-- A negative decision answer gives an additive unit gap for every nonzero module vector. -/
theorem not_ModuleYes_iff_gap {d : ℕ} (a b : Coeff d × Coeff d) (M : ℕ) :
    ¬ModuleYes a b M ↔
      ∀ u v : Coeff d, moduleVector a b u v ≠ 0 →
        M + 1 ≤ pairSup (moduleVector a b u v) := by
  constructor
  · intro h u v hne
    have hnot : ¬pairSup (moduleVector a b u v) ≤ M := by
      intro hn
      exact h ⟨u, v, hne, hn⟩
    omega
  · intro h ⟨u, v, hne, hn⟩
    have := h u v hne
    omega

/-- A negative decision answer bounds every nonzero module vector below by `M+1`. -/
theorem gap_of_not_ModuleYes {d : ℕ} (a b : Coeff d × Coeff d) (M : ℕ)
    (h : ¬ModuleYes a b M) (u v : Coeff d) (hne : moduleVector a b u v ≠ 0) :
    M + 1 ≤ pairSup (moduleVector a b u v) :=
  (not_ModuleYes_iff_gap a b M).mp h u v hne

/-- An attained radius whose short nonzero vectors all have exactly that norm is the first
minimum. The exact-norm condition is intended to be supplied by the gadget's soundness proof. -/
theorem firstMinimum_of_ModuleYes_of_short_eq {d : ℕ}
    (a b : Coeff d × Coeff d) (M : ℕ) (hyes : ModuleYes a b M)
    (hexact : ∀ u v : Coeff d, moduleVector a b u v ≠ 0 →
      pairSup (moduleVector a b u v) ≤ M → pairSup (moduleVector a b u v) = M) :
    FirstMinimum a b M := by
  obtain ⟨u, v, hne, hn⟩ := hyes
  refine ⟨⟨u, v, hne, hexact u v hne hn⟩, ?_⟩
  intro u v hne
  by_cases hn : pairSup (moduleVector a b u v) ≤ M
  · exact (hexact u v hne hn).ge
  · omega

/-- Radius zero never contains a nonzero integral module vector. -/
theorem not_ModuleYes_zero {d : ℕ} (a b : Coeff d × Coeff d) :
    ¬ModuleYes a b 0 := by
  rintro ⟨u, v, hne, hn⟩
  have := one_le_pairSup_of_ne_zero _ hne
  omega

end Power2ModuleSVPSubsetSum.Reduction
