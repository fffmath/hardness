module

public import Power2ModuleSVP.ColoringAux
public import Mathlib.Analysis.Normed.Group.Constructions

/-!
The full-coloring program and its semantic correctness, conditional on the
semantic contract of the supplied partial-coloring program. This separates
the recursion from both the partial walk and the machine-time certificate.
-/

@[expose] public section

namespace Power2ModuleSVP

open scoped BigOperators

def PartialColoringCorrect (F : PartialColoringInput → List ℚ) : Prop :=
  ∀ (r m : ℕ) (V : Fin m → Fin r → ℚ) (x : Fin r → ℚ) (c : Fin m → ℚ),
    64 ≤ r → RationalCube x → (∀ i, 0 ≤ c i) →
    coloringEntropy c ≤ (r : ℝ) / 64 →
    ∃ y : Fin r → ℚ, F (partialColoringInput V x c) = List.ofFn y ∧
      PartialColoringSpec V x y c

def readColoringVector (r : ℕ) (l : List ℚ) : Fin r → ℚ := fun j => l.getD j 0

@[simp] theorem readColoringVector_ofFn {r : ℕ} (x : Fin r → ℚ) :
    readColoringVector r (List.ofFn x) = x := by
  funext j
  simp [readColoringVector, List.getD_eq_getElem?_getD]

namespace Coloring

/-- A total recursion on the actual dimension. Malformed partial-program
outputs fall back to nearest signs if they fail to reduce the dimension. -/
def fullColorCore (F : PartialColoringInput → List ℚ) (r m : ℕ)
    (V : Fin m → Fin r → ℚ) (x : Fin r → ℚ) (c : Fin m → ℚ) : Fin r → ℚ :=
  if r ≤ 64 then fun j => nearestRationalSign (x j)
  else
    let y := readColoringVector r (F (partialColoringInput V x c))
    let A := activeSet y
    if h : A.card < r then
      let z := fullColorCore F A.card m (fun i j => V i (embed A j))
        (fun j => y (embed A j)) (fun i => c i + 4)
      extend A y z
    else fun j => nearestRationalSign (x j)
termination_by r

def FullBound {r m : ℕ} (V : Fin m → Fin r → ℚ)
    (x y : Fin r → ℚ) (c : Fin m → ℚ) : Prop :=
  (∀ j, y j = -1 ∨ y j = 1) ∧
  ∀ i (B : ℝ), 0 ≤ B → (∀ j, |(V i j : ℝ)| ≤ B) →
    coloringDiscrepancy (V i) x y ≤ (240 * (c i : ℝ) + 2400) * Real.sqrt r * B

theorem sqrt_half_le {r s : ℕ} (hs : 2 * s ≤ r) :
    Real.sqrt s ≤ Real.sqrt r / Real.sqrt 2 := by
  have hcast : (2 : ℝ) * s ≤ r := by exact_mod_cast hs
  have hs₁ := Real.sqrt_nonneg (s : ℝ)
  have hr₁ := Real.sqrt_nonneg (r : ℝ)
  have ht : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs₂ := Real.sq_sqrt (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  have hr₂ := Real.sq_sqrt (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have ht₂ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  apply (le_div_iff₀ ht).mpr
  nlinarith [sq_nonneg (Real.sqrt s * Real.sqrt 2 - Real.sqrt r)]

theorem fullColorCore_spec (F : PartialColoringInput → List ℚ)
    (hF : PartialColoringCorrect F) (r m : ℕ)
    (V : Fin m → Fin r → ℚ) (x : Fin r → ℚ) (c : Fin m → ℚ)
    (hx : RationalCube x) (hc : ∀ i, 0 ≤ c i)
    (he : coloringEntropy c ≤ (r : ℝ) / 64) :
    FullBound V x (fullColorCore F r m V x c) c := by
  induction r using Nat.strong_induction_on generalizing c with
  | h r ih =>
    by_cases hr : r ≤ 64
    · rw [fullColorCore, ite_eq_left hr]
      refine ⟨fun j => nearestRationalSign_isSign _, ?_⟩
      intro i B hB hv
      have hi : (0 : ℝ) ≤ c i := by exact_mod_cast hc i
      have hcoeff : (8 : ℝ) ≤ 240 * (c i : ℝ) + 2400 := by linarith
      exact (nearestRationalSign_small_discrepancy hr (V i) x hx hB hv).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg _)) hB)
    · obtain ⟨y, hy, hycube, hycount, hydisc⟩ :=
        hF r m V x c (by omega) hx hc he
      have hA := activeSet_card y hycount
      have hlt : (activeSet y).card < r := by rw [hA]; omega
      have he' := coloringEntropy_add_four (by omega : 5 ≤ r) c hc he
      have hz := ih (activeSet y).card hlt
        (fun i j => V i (embed (activeSet y) j))
        (fun j => y (embed (activeSet y) j))
        (fun i => c i + 4)
        (fun j => hycube _) (fun i => by have := hc i; linarith)
        (by simpa only [hA] using he')
      rw [fullColorCore, ite_eq_right hr, hy, readColoringVector_ofFn, dite_eq_left hlt]
      refine ⟨extend_signs y _ hz.1, ?_⟩
      intro i B hB hv
      have hi : (0 : ℝ) ≤ c i := by exact_mod_cast hc i
      have hN := coloringRowNorm_le_sqrt_mul (V i) hB hv
      have hD := hydisc i
      have hD' := hz.2 i B hB (fun j => hv _)
      have hs := sqrt_half_le (show 2 * (activeSet y).card ≤ r by rw [hA]; omega)
      have hcoef : 0 ≤ 240 * ((c i : ℝ) + 4) + 2400 := by linarith
      have htail :
          (240 * ((c i + 4 : ℚ) : ℝ) + 2400) * Real.sqrt (activeSet y).card * B ≤
          ((240 * ((c i : ℝ) + 4) + 2400) / Real.sqrt 2) * Real.sqrt r * B := by
        push_cast
        calc
          _ ≤ (240 * ((c i : ℝ) + 4) + 2400) *
              (Real.sqrt r / Real.sqrt 2) * B :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hcoef) hB
          _ = _ := by ring
      calc
        _ ≤ coloringDiscrepancy (V i) x y +
            coloringDiscrepancy (V i) y (extend (activeSet y) y _) :=
          coloringDiscrepancy_triangle _ _ _ _
        _ ≤ 68 * (c i : ℝ) * (Real.sqrt r * B) +
            ((240 * ((c i : ℝ) + 4) + 2400) / Real.sqrt 2) * Real.sqrt r * B := by
          apply add_le_add
          · exact hD.trans (mul_le_mul_of_nonneg_left hN (by positivity))
          · rw [discrepancy_extend]
            exact hD'.trans htail
        _ = (68 * (c i : ℝ) +
            (240 * ((c i : ℝ) + 4) + 2400) / Real.sqrt 2) * Real.sqrt r * B := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (fullColoring_constant_recurrence hi)
            (Real.sqrt_nonneg _)) hB

end Coloring

/-- List interface to the full-coloring program. Matrix dimensions are
explicit in the list lengths; missing entries on malformed inputs read zero. -/
def fullColor (F : PartialColoringInput → List ℚ) (input : PartialColoringInput) : List ℚ :=
  let r := input.2.1.length
  let m := input.1.length
  let V : Fin m → Fin r → ℚ := fun i j => (input.1.getD i []).getD j 0
  let x := readColoringVector r input.2.1
  let c := readColoringVector m input.2.2
  List.ofFn (Coloring.fullColorCore F r m V x c)

theorem fullColor_length (F : PartialColoringInput → List ℚ) (input : PartialColoringInput) :
    (fullColor F input).length = input.2.1.length := by
  simp only [fullColor, List.length_ofFn]

theorem fullColor_on_input (F : PartialColoringInput → List ℚ) {r m : ℕ}
    (V : Fin m → Fin r → ℚ) (x : Fin r → ℚ) (c : Fin m → ℚ) :
    fullColor F (partialColoringInput V x c) =
      List.ofFn (Coloring.fullColorCore F r m V x c) := by
  unfold fullColor
  simp (config := { zeta := false }) only [partialColoringInput, List.length_ofFn]
  dsimp only
  simp only [readColoringVector_ofFn]
  congr 2
  funext i j
  simp [List.getD_eq_getElem?_getD]

/-- The coefficient maximum norm of a rational row, including the empty row. -/
noncomputable def coloringRowSup {r : ℕ} (v : Fin r → ℚ) : ℝ :=
  ‖fun j => (v j : ℝ)‖

theorem coloringRowSup_nonneg {r : ℕ} (v : Fin r → ℚ) : 0 ≤ coloringRowSup v :=
  norm_nonneg _

theorem abs_le_coloringRowSup {r : ℕ} (v : Fin r → ℚ) (j : Fin r) :
    |(v j : ℝ)| ≤ coloringRowSup v := by
  exact norm_le_pi_norm (fun j => (v j : ℝ)) j

def FullColoringSpec {r m : ℕ} (V : Fin m → Fin r → ℚ)
    (x y : Fin r → ℚ) (c : Fin m → ℚ) : Prop :=
  (∀ j, y j = -1 ∨ y j = 1) ∧ ∀ i,
    coloringDiscrepancy (V i) x y ≤
      (240 * (c i : ℝ) + 2400) * Real.sqrt r * coloringRowSup (V i)

theorem fullColoring_of_partialCorrect (F : PartialColoringInput → List ℚ)
    (hF : PartialColoringCorrect F) (r m : ℕ)
    (V : Fin m → Fin r → ℚ) (x : Fin r → ℚ) (c : Fin m → ℚ)
    (hx : RationalCube x) (hc : ∀ i, 0 ≤ c i)
    (he : coloringEntropy c ≤ (r : ℝ) / 64) :
    FullColoringSpec V x (Coloring.fullColorCore F r m V x c) c := by
  obtain ⟨hs, hd⟩ := Coloring.fullColorCore_spec F hF r m V x c hx hc he
  exact ⟨hs, fun i => hd i _ (coloringRowSup_nonneg _) (abs_le_coloringRowSup _)⟩

/-- Semantic full coloring from the existing partial-coloring interface.
This theorem does not assert a machine certificate for full coloring. -/
theorem fullColoring_exists_of (h : DeterministicPartialColoringHypothesis)
    (r m : ℕ) (V : Fin m → Fin r → ℚ) (x : Fin r → ℚ) (c : Fin m → ℚ)
    (hx : RationalCube x) (hc : ∀ i, 0 ≤ c i)
    (he : coloringEntropy c ≤ (r : ℝ) / 64) :
    ∃ y : Fin r → ℚ, FullColoringSpec V x y c := by
  obtain ⟨F, _, hF⟩ := h.exists_algorithm
  exact ⟨_, fullColoring_of_partialCorrect F hF r m V x c hx hc he⟩

theorem fullColor_spec (F : PartialColoringInput → List ℚ) (hF : PartialColoringCorrect F)
    (r m : ℕ) (V : Fin m → Fin r → ℚ) (x : Fin r → ℚ) (c : Fin m → ℚ)
    (hx : RationalCube x) (hc : ∀ i, 0 ≤ c i)
    (he : coloringEntropy c ≤ (r : ℝ) / 64) :
    ∃ y : Fin r → ℚ, fullColor F (partialColoringInput V x c) = List.ofFn y ∧
      FullColoringSpec V x y c :=
  ⟨_, fullColor_on_input F V x c, fullColoring_of_partialCorrect F hF r m V x c hx hc he⟩

/-- A separate obligation: a polynomial certificate for one partial call
does not by itself bound bit growth across a logarithmic recursion. This
field concerns the actual full-coloring list program. -/
structure FullColoringNativeHypothesis (F : PartialColoringInput → List ℚ) : Prop where
  polytime : Turing.MultiTapeTM.ComputableTidilyInPolyTime (fullColor F) encPartialColoring
    (Turing.MultiTapeTM.encList encColoringRational)

theorem fullColor_algorithm_of_partialCorrect (F : PartialColoringInput → List ℚ)
    (hF : PartialColoringCorrect F) (hN : FullColoringNativeHypothesis F) :
    ∃ G : PartialColoringInput → List ℚ,
      Turing.MultiTapeTM.ComputableTidilyInPolyTime G encPartialColoring
        (Turing.MultiTapeTM.encList encColoringRational) ∧
      ∀ (r m : ℕ) (V : Fin m → Fin r → ℚ) (x : Fin r → ℚ) (c : Fin m → ℚ),
        RationalCube x → (∀ i, 0 ≤ c i) → coloringEntropy c ≤ (r : ℝ) / 64 →
        ∃ y : Fin r → ℚ, G (partialColoringInput V x c) = List.ofFn y ∧
          FullColoringSpec V x y c :=
  ⟨fullColor F, hN.polytime, fullColor_spec F hF⟩

end Power2ModuleSVP
