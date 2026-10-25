import Power2ModuleSVP.Runtime.Coloring.DirectionDataBounds
import Power2ModuleSVP.Runtime.Coloring.ReifyBounds

/-!
# Box

Uniform encoding bounds for list states with bounded weights.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open PartialColoringAlg ColoringNative
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- The parameter encoding stores normalized rows and thresholds, without
any current point or current weights. -/
def walkParameter {r m : ℕ} (a : Fin m → Row r) : WalkParameter :=
  (r, List.ofFn fun i => ((a i).threshold, List.ofFn (a i).a))

/-- Encode a walk state after replacing unfixed coordinates by zero. -/
def frozenWalkInput {r m : ℕ} (a : Fin m → Row r) (s : State r m) : WalkInput :=
  (walkParameter a, (List.ofFn (frozenPoint s.x), List.ofFn s.w))

/-- Uniform encoding bound for states with frozen coordinates and bounded weights. -/
def boxStateBound (p : WalkParameter) : ℕ :=
  26 * p.1 +
    (2 * (2 * (2 * (stepBudget p.1 + 1) + 1 + 2 * (precision p.1 p.2.length + 2)) + 3) + 1) *
      p.2.length + 1

theorem boxStateBound_polyBounded :
    PolyBounded (fun p => (encWalkParameter p).length) boxStateBound := by
  have hr : PolyBounded (fun p : WalkParameter => (encWalkParameter p).length)
      (fun p => p.1) := by
    have h : ComputableTidilyInPolyTime (fun p : WalkParameter => p.1)
        encWalkParameter encUnary := by unfold encWalkParameter; fun_prop
    simpa only [encUnary_apply, List.length_replicate] using h.polyBounded_length
  have hm : PolyBounded (fun p : WalkParameter => (encWalkParameter p).length)
      (fun p => p.2.length) := by
    have h : ComputableTidilyInPolyTime (fun p : WalkParameter => p.2.length)
        encWalkParameter encUnary := by unfold encWalkParameter; fun_prop
    simpa only [encUnary_apply, List.length_replicate] using h.polyBounded_length
  have hf : PolyBounded (fun p : WalkParameter => (encWalkParameter p).length)
      (fun p => stepBudget p.1) := by
    unfold stepBudget
    exact (PolyBounded.const 2048).mul (by simpa [pow_succ] using (hr.mul hr).mul hr)
  have hp : PolyBounded (fun p : WalkParameter => (encWalkParameter p).length)
      (fun p => precision p.1 p.2.length) := by
    have h : ComputableTidilyInPolyTime (fun p : WalkParameter => precision p.1 p.2.length)
        encWalkParameter encUnary := by
      exact precision_polytime.comp (show ComputableTidilyInPolyTime
        (fun p : WalkParameter => (p.1, p.2.length)) encWalkParameter
        (encPair encUnary encUnary) from by unfold encWalkParameter; fun_prop)
    simpa only [encUnary_apply, List.length_replicate] using h.polyBounded_length
  have hbits := (((PolyBounded.const 2).mul (hf.add (.const 1))).add (.const 1)).add
    ((PolyBounded.const 2).mul (hp.add (.const 2)))
  have hentry := ((PolyBounded.const 2).mul hbits).add (.const 3)
  have hweights := (((PolyBounded.const 2).mul hentry).add (.const 1)).mul hm
  exact (((PolyBounded.const 26).mul hr).add hweights).add (.const 1)

theorem frozenWalkInput_encoding {r m : ℕ} (a : Fin m → Row r) (s : State r m)
    (hs : WeightBox (stepBudget r) s) :
    (encWalkInput (frozenWalkInput a s)).length ≤
      2 * (encWalkParameter (walkParameter a)).length + boxStateBound (walkParameter a) + 1 := by
  have hx := frozenPoint_encoding s.x
  have hw := weightBox_encoding hs
  simp only [encWalkInput, frozenWalkInput, encListState, length_encPair]
  simp only [boxStateBound, walkParameter, List.length_ofFn]
  omega

/-- A uniform polynomial bound on all reifier inputs over the entire
weight box. It charges no bits to the actual point's fractions. -/
theorem frozenWalkInput_uniform_encoding :
    ∃ c d : ℕ, ∀ (r m : ℕ) (a : Fin m → Row r) (s : State r m),
      WeightBox (stepBudget r) s →
      (encWalkInput (frozenWalkInput a s)).length ≤
        c * ((encWalkParameter (walkParameter a)).length + 1) ^ d := by
  have h : PolyBounded (fun p => (encWalkParameter p).length)
      (fun p => 2 * (encWalkParameter p).length + boxStateBound p + 1) :=
    (((PolyBounded.const 2).mul PolyBounded.self).add boxStateBound_polyBounded).add (.const 1)
  obtain ⟨c, d, hb⟩ := h.exists_le
  exact ⟨c, d, fun r m a s hs => (frozenWalkInput_encoding a s hs).trans (hb _)⟩

/-- An index order is charged by its list length, without assuming a
machine certificate for computing that order. -/
def boxReifyBound (p : WalkParameter) : ℕ :=
  2 * (2 * (encWalkParameter p).length + boxStateBound p + 1) +
    (2 * p.2.length + 1) * p.2.length + 1

theorem boxReifyBound_polyBounded :
    PolyBounded (fun p => (encWalkParameter p).length) boxReifyBound := by
  have hm : PolyBounded (fun p : WalkParameter => (encWalkParameter p).length)
      (fun p => p.2.length) := by
    have h : ComputableTidilyInPolyTime (fun p : WalkParameter => p.2.length)
        encWalkParameter encUnary := by unfold encWalkParameter; fun_prop
    simpa only [encUnary_apply, List.length_replicate] using h.polyBounded_length
  have hin := (((PolyBounded.const 2).mul PolyBounded.self).add
    boxStateBound_polyBounded).add (.const 1)
  exact (((PolyBounded.const 2).mul hin).add
    ((((PolyBounded.const 2).mul hm).add (.const 1)).mul hm)).add (.const 1)

/-- The exact direction data have a uniform bound throughout the weight
box, independently of any certificate for heavy-row sorting. -/
theorem walkDirectionInput_uniform_encoding :
    ∃ c d : ℕ, ∀ (r m : ℕ) (a : Fin m → Row r) (s : State r m),
      WeightBox (stepBudget r) s →
      (encDirectionInput (walkDirectionInput a s)).length ≤
        c * ((encWalkParameter (walkParameter a)).length + 1) ^ d := by
  have hout := directionGivenHeavy_polytime.polyBounded_length
  obtain ⟨c₁, d₁, hb₁⟩ := hout.exists_le
  have hfinal : PolyBounded (fun p => (encWalkParameter p).length)
      (fun p => c₁ * (boxReifyBound p + 1) ^ d₁) := by
    obtain ⟨bound, hp, hb⟩ := boxReifyBound_polyBounded
    refine ⟨fun n => c₁ * (bound n + 1) ^ d₁, by fun_prop, fun p => ?_⟩
    exact Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left (Nat.add_le_add_right (hb p) 1) d₁)
  obtain ⟨c, d, hb⟩ := hfinal.exists_le
  refine ⟨c, d, fun r m a s hs => ?_⟩
  let p := frozenWalkInput a s
  let indices := heavyIndices (r, List.ofFn s.w)
  have hspec : directionGivenHeavy (p, indices) = walkDirectionInput a s := by
    rw [walkDirectionInput_frozen a s]
    exact (directionGivenHeavy_spec p).trans (directionDataList_spec a ⟨frozenPoint s.x, s.w⟩)
  have hsize : (encReifyInput (p, indices)).length ≤ boxReifyBound (walkParameter a) := by
    have hi := heavyIndices_encoding r (List.ofFn s.w)
    have hp := frozenWalkInput_encoding a s hs
    simp only [walkParameter] at hp
    simp only [List.length_ofFn] at hi
    simp only [encReifyInput, length_encPair]
    simp only [boxReifyBound, walkParameter, List.length_ofFn]
    dsimp only [p, indices] at *
    omega
  rw [← hspec]
  exact (hb₁ _).trans ((Nat.mul_le_mul_left c₁
    (Nat.pow_le_pow_left (Nat.add_le_add_right hsize 1) d₁)).trans (hb _))

end Power2ModuleSVP.ColoringRuntime
