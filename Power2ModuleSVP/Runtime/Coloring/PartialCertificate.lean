import Power2ModuleSVP.Runtime.Coloring.StateBounds
import Power2ModuleSVP.Runtime.Coloring.Loop

/-!
# Partial Certificate

The size invariant of the complete native stopped walk.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
namespace Power2ModuleSVP.ColoringRuntime
open PartialColoringAlg ColoringNative
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def loopStartWire (input : PartialColoringInput) : WalkInput :=
  (loopParameter input, (input.2.1, []))

theorem loopStartWire_polytime :
    ComputableTidilyInPolyTime loopStartWire encPartialColoring encWalkInput := by
  have hx : ComputableTidilyInPolyTime (fun p : PartialColoringInput => p.2.1)
      encPartialColoring (encList encColoringRational) := by unfold encPartialColoring; fun_prop
  exact loopParameter_polytime.prod (hx.prod (.const []))

private theorem ofFn_getD {α : Type} (xs : List α) (d : α) :
    List.ofFn (fun i : Fin xs.length => xs.getD i d) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.getD_eq_getElem?_getD]

/-- Raw valid inputs supply exactly the cube and nonnegative thresholds
needed by the entropy-free prefix estimates. -/
theorem validInput_read_bounds (input : PartialColoringInput)
    (hv : validInput input = true) :
    RationalCube (fun j : Fin input.2.1.length => input.2.1.getD j 0) ∧
      ∀ i : Fin input.1.length, 0 ≤ input.2.2.getD i 0 := by
  have hc := (Bool.and_eq_true_iff.mp hv).2
  have hx := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).2
  have hn := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hv).1).1).2
  change decide (input.2.2.length = input.1.length) = true at hn
  have hlen := of_decide_eq_true hn
  constructor
  · intro j
    have hq := List.all_eq_true.mp hx (input.2.1.getD j 0) (by
      simp [List.getD_eq_getElem?_getD, j.isLt])
    have hb : |input.2.1.getD j 0| ≤ (1 : ℚ) := of_decide_eq_true hq
    exact_mod_cast hb
  · intro i
    have hi : i.val < input.2.2.length := by omega
    exact of_decide_eq_true (List.all_eq_true.mp hc _ (by
      simp [List.getD_eq_getElem?_getD, hi]))

/-- All prefixes of the actual raw-input evaluator have polynomial encoding
length, including the zero-fuel malformed-input branches. -/
theorem stoppedWalkEncoding_of_projector (h : CanonicalProjectorDenominatorHypothesis) :
    StoppedWalkEncodingHypothesis := by
  obtain ⟨c₀, d₀, hb⟩ := walk_initial_state_encoding_uniform h
  have hp : PolyBounded (fun input => (encPartialColoring input).length)
      (fun input => c₀ * ((encWalkInput (loopStartWire input)).length + 1) ^ d₀) := by
    have hout : PolyBounded (fun p : WalkInput => (encWalkInput p).length)
        (fun p => c₀ * ((encWalkInput p).length + 1) ^ d₀) :=
      PolyBounded.of_forall_le c₀ d₀ (fun _ => le_rfl)
    exact hout.comp loopStartWire_polytime.polyBounded_length
  have hinit := loopInitial_polytime.polyBounded_length
  obtain ⟨c, d, hbound⟩ := (hinit.add hp).exists_le
  refine ⟨⟨c, d, fun input k hk => ?_⟩⟩
  apply le_trans (b := (encListState (loopInitial input)).length +
    c₀ * ((encWalkInput (loopStartWire input)).length + 1) ^ d₀) ?_ (hbound input)
  by_cases hk0 : k = 0
  · subst k
    simp
  have hg : (validInput input && (!(loopParameter input).2.isEmpty)) = true := by
    by_contra hg
    have hf : (validInput input && (!(loopParameter input).2.isEmpty)) = false :=
      Bool.eq_false_iff.mpr hg
    simp [loopCount, hf] at hk
    omega
  have hv := (Bool.and_eq_true_iff.mp hg).1
  have hne : (loopParameter input).2.isEmpty = false := by
    simpa using (Bool.and_eq_true_iff.mp hg).2
  have hc : loopCount input = stepBudget input.2.1.length := by simp [loopCount, hg]
  have hr : 0 < input.2.1.length := by
    by_contra hr
    have hz : input.2.1.length = 0 := by omega
    simp [hc, stepBudget, hz] at hk
    omega
  let r := input.2.1.length
  let m := input.1.length
  let V : Fin m → Vec r := fun i j => (input.1.getD i []).getD j 0
  let x : Vec r := fun j => input.2.1.getD j 0
  let c' : Fin m → ℚ := fun i => input.2.2.getD i 0
  let rows := prepareRows V c'
  have hparam : loopParameter input = reifyRows rows.get := loopParameter_read input
  have hx : List.ofFn x = input.2.1 := ofFn_getD _ _
  have hi : loopInitial input = reifyState (initialState rows.get x) :=
    loopInitial_spec_of_active input hv hne
  obtain ⟨hxc, hcc⟩ := validInput_read_bounds input hv
  have hrow (i : Fin rows.length) := prepareRows_row_properties V c' hcc
    (rows.get i) (List.get_mem _ _)
  rw [hi, hparam, stopped_iterate_spec]
  have hstate := hb r rows.length k hr rows.get
    (fun i => (hrow i).2.1) (fun i => (hrow i).2.2) (by simpa [hc] using hk) x hxc
  have he : startWire rows.get x = loopStartWire input := by
    change (walkParameter rows.get, (List.ofFn x, [])) = _
    rw [hx]
    change (reifyRows rows.get, (input.2.1, [])) = _
    rw [← hparam]
    rfl
  rw [he] at hstate
  exact hstate.trans (Nat.le_add_left _ _)

theorem partialColorNative_of_projector_and_sort
    (h : CanonicalProjectorDenominatorHypothesis) (hsort : HeavyIndicesNativeHypothesis) :
    PartialColoringNativeHypothesis :=
  partialColorNative_of_components h hsort (stoppedWalkEncoding_of_projector h)

end Power2ModuleSVP.ColoringRuntime
