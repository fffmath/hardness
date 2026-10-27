import Power2IdealSVP.Runtime.Graph
import Power2IdealSVP.Problem
import IdealCVP.Complexity.ListRing

/-!
# Executable principal ideal reduction

List programs for all parameters of the CLIQUE reduction. Counters and labels are polynomial
natural values; coefficients use integers. The guard adds both contributions at the antipodal
coordinate, as required by negacyclic multiplication.

Paper: `paper/power2-ideal-svp.pdf`, Sections 1.1 and 1.5; `AUDIT_B.md`, Section 3.
-/

namespace Power2IdealSVP.Runtime

open Cslib.Complexity

/-- The base separating the first three power sums of vertex indices. -/
def labelBase (x : Graph × ℕ) : ℕ := 3 * vertexCount x.1 ^ 3 + 1

/-- The paper's label for a one-based vertex index. -/
def graphLabel (x : Graph × ℕ) (i : ℕ) : ℕ :=
  i + labelBase x * i ^ 2 + labelBase x ^ 2 * i ^ 3

/-- Labels in the order of the distinct declared vertices. -/
def graphLabels (x : Graph × ℕ) : List ℕ :=
  (List.range (vertexCount x.1)).map fun i => graphLabel x (i + 1)

/-- The largest label `A₀ = aᵥ` (zero when the declared vertex set is empty). -/
def maxLabel (x : Graph × ℕ) : ℕ := graphLabel x (vertexCount x.1)

/-- Unsigned difference of the labels at two zero-based indices. -/
def edgeDifference (x : Graph × ℕ) (e : ℕ × ℕ) : ℕ :=
  (graphLabel x (e.1 + 1) - graphLabel x (e.2 + 1)) +
    (graphLabel x (e.2 + 1) - graphLabel x (e.1 + 1))

/-- Sorted, duplicate-free positive edge differences, computed by a bounded unary scan. -/
def diffSet (x : Graph × ℕ) : List ℕ :=
  (List.range (maxLabel x + 1)).filter fun d =>
    decide (0 < d) && (normalEdges x.1).any (fun e => decide (d = edgeDifference x e))

/-- The window spacing `Q`. -/
def windowSpacing : ℕ := 16

/-- The bound `R₀` on positive allowed distances. -/
def windowBound (x : Graph × ℕ) : ℕ := windowSpacing * maxLabel x + 2

/-- Least power of two strictly greater than `8R₀ + 16`. -/
def degree (x : Graph × ℕ) : ℕ := 2 ^ Nat.clog 2 (8 * windowBound x + 17)

/-- Membership in `E₊`: the two near distances and four-point far windows. -/
def allowedDistance (x : Graph × ℕ) (d : ℕ) : Bool :=
  decide (d = 1) || decide (d = 2) || (diffSet x).any (fun e =>
    decide (d = windowSpacing * e - 1) || decide (d = windowSpacing * e) ||
      decide (d = windowSpacing * e + 1) || decide (d = windowSpacing * e + 2))

/-- Forbidden distances in increasing order, including the antipodal distance. -/
def forbiddenDistances (x : Graph × ℕ) : List ℕ :=
  ((List.range (degree x / 2)).map (· + 1)).filter fun d => !allowedDistance x d

/-- A guard coefficient. At the antipode both indicators equal one. -/
def guardCoeff (x : Graph × ℕ) (i : ℕ) : ℤ :=
  ((forbiddenDistances x).zipIdx.map fun p =>
    (5 : ℤ) ^ p.2 * ((if i = p.1 then 1 else 0) +
      (if i = degree x - p.1 then 1 else 0))).sum

/-- The coefficient list of `A = Σⱼ 5ʲ(Xᵈʲ - X⁻ᵈʲ)`. -/
def guardCoeffs (x : Graph × ℕ) : List ℤ :=
  (List.range (degree x)).map (guardCoeff x)

/-- Coefficient of `Xᵉ + X⁻ᵉ` for `0 < e < n`. -/
def symmetricCoeff (n e i : ℕ) : ℤ :=
  (if i = e then 1 else 0) - (if i = n - e then 1 else 0)

/-- The coefficient of the endpoint interaction polynomial `T`. -/
def interactionCoeff (x : Graph × ℕ) (i : ℕ) : ℤ :=
  ((diffSet x).map fun d =>
    symmetricCoeff (degree x) (windowSpacing * d) i +
      symmetricCoeff (degree x) (windowSpacing * d + 2) i).sum

/-- The coefficient array of the self-adjoint polynomial `T`. -/
def interactionCoeffs (x : Graph × ℕ) : List ℤ :=
  (List.range (degree x)).map (interactionCoeff x)

/-- Exact coefficient one-norm of an integer list, with binary output. -/
def listNorm (a : List ℤ) : ℕ := (a.map Int.natAbs).sum

/-- The exact norm `R_T`, including any coefficient cancellations. -/
def interactionNorm (x : Graph × ℕ) : ℕ := listNorm (interactionCoeffs x)

/-- Nearest-neighbor amplitude `C = R_T + h + 1`. -/
def neighborAmplitude (x : Graph × ℕ) : ℕ := interactionNorm x + x.2 + 1

/-- Sparse-spin threshold `τ = C + h - 1`. -/
def spinThreshold (x : Graph × ℕ) : ℕ := neighborAmplitude x + x.2 - 1

/-- Guard amplitude `L = 2C + R_T + τ + 1`. -/
def guardAmplitude (x : Graph × ℕ) : ℕ :=
  2 * neighborAmplitude x + interactionNorm x + spinThreshold x + 1

/-- The sparse-spin polynomial `G = LA - C(X + X⁻¹) + T`. -/
def spinCoeffs (x : Graph × ℕ) : List ℤ :=
  (List.range (degree x)).map fun i =>
    (guardAmplitude x : ℤ) * guardCoeff x i -
      (neighborAmplitude x : ℤ) * symmetricCoeff (degree x) 1 i + interactionCoeff x i

/-- Domain-wall polynomial `H = G(1-X)`, using certified negacyclic list multiplication. -/
def wallCoeffs (x : Graph × ℕ) : List ℤ :=
  IdealCVP.negacyclicMul (degree x) (spinCoeffs x) [1, -1]

/-- The exact reduced coefficient norm `R_H`. -/
def wallNorm (x : Graph × ℕ) : ℕ := listNorm (wallCoeffs x)

/-- Clock amplitude `B = R_H + 2τ + 1`. -/
def clockAmplitude (x : Graph × ℕ) : ℕ := wallNorm x + 2 * spinThreshold x + 1

/-- The full-sign polynomial `K = BX + H`. -/
def clockCoeffs (x : Graph × ℕ) : List ℤ :=
  (List.range (degree x)).map fun i =>
    (if i = 1 then (clockAmplitude x : ℤ) else 0) + (wallCoeffs x).getD i 0

/-- The exact reduced coefficient norm `R_K`. -/
def clockNorm (x : Graph × ℕ) : ℕ := listNorm (clockCoeffs x)

/-- Dominating scalar `M = 3R_K + 1`. -/
def dominantAmplitude (x : Graph × ℕ) : ℕ := 3 * clockNorm x + 1

/-- The polynomial `S = 1 + X + ⋯ + Xⁿ⁻¹`. -/
def parityCoeffs (x : Graph × ℕ) : List ℤ := List.replicate (degree x) 1

/-- The factor `M-K` in reduced coefficient form. -/
def dominantCoeffs (x : Graph × ℕ) : List ℤ :=
  (List.range (degree x)).map fun i =>
    (if i = 0 then (dominantAmplitude x : ℤ) else 0) - (clockCoeffs x).getD i 0

/-- Generator `f = (M-K)S`, using the existing negacyclic product program. -/
def generatorCoeffs (x : Graph × ℕ) : List ℤ :=
  IdealCVP.negacyclicMul (degree x) (dominantCoeffs x) (parityCoeffs x)

/-- The output threshold `r = M+B-2τ`. -/
def outputRadius (x : Graph × ℕ) : ℕ :=
  dominantAmplitude x + clockAmplitude x - 2 * spinThreshold x

/-- The unrestricted list construction, used only in the main target range by `reduceList`. -/
def construction (x : Graph × ℕ) : IdealInput :=
  (degree x, generatorCoeffs x, outputRadius x)

/-- Fixed well-formed YES instance: the unit ideal in dimension one at radius one. -/
def yesInput : IdealInput := (1, [1], 1)

/-- Fixed well-formed NO instance: radius zero excludes every nonzero integer vector. -/
def noInput : IdealInput := (1, [1], 0)

/-- Total reduction. Small targets and impossible targets are decided before the main gadget. -/
def reduceList (x : Graph × ℕ) : IdealInput :=
  if mainCase x then construction x else if smallAnswer x then yesInput else noInput

/-- On the paper's target range the total map is exactly the main construction. -/
@[simp] theorem reduceList_of_mainCase {x : Graph × ℕ} (h : mainCase x = true) :
    reduceList x = construction x := by simp [reduceList, h]

/-- Outside the paper's target range a positive direct decision selects the unit YES input. -/
theorem reduceList_of_small_yes {x : Graph × ℕ} (h : mainCase x = false)
    (hs : smallAnswer x = true) : reduceList x = yesInput := by simp [reduceList, h, hs]

/-- Outside the paper's target range a negative direct decision selects the radius-zero input. -/
theorem reduceList_of_small_no {x : Graph × ℕ} (h : mainCase x = false)
    (hs : smallAnswer x = false) : reduceList x = noInput := by simp [reduceList, h, hs]

/-- The label program is monotone on natural vertex indices. -/
theorem graphLabel_mono (x : Graph × ℕ) : Monotone (graphLabel x) := by
  intro i j hij
  unfold graphLabel
  exact Nat.add_le_add
    (Nat.add_le_add hij (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hij 2)))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hij 3))

/-- Distinct increasing indices have strictly increasing labels. -/
theorem graphLabel_strictMono (x : Graph × ℕ) : StrictMono (graphLabel x) := by
  intro i j hij
  have h₂ := Nat.mul_le_mul_left (labelBase x)
    (Nat.pow_le_pow_left hij.le 2)
  have h₃ := Nat.mul_le_mul_left (labelBase x ^ 2)
    (Nat.pow_le_pow_left hij.le 3)
  unfold graphLabel
  omega

/-- Every label in the enumerated graph is bounded by `A₀`. -/
theorem graphLabel_le_maxLabel (x : Graph × ℕ) {i : ℕ}
    (hi : i ≤ vertexCount x.1) : graphLabel x i ≤ maxLabel x :=
  graphLabel_mono x hi

/-- Exact membership specification for the deduplicated edge-difference scan. -/
theorem mem_diffSet (x : Graph × ℕ) (d : ℕ) :
    d ∈ diffSet x ↔ d ≤ maxLabel x ∧ 0 < d ∧
      ∃ e ∈ normalEdges x.1, d = edgeDifference x e := by
  simp [diffSet]

/-- Every normalized edge difference is positive and bounded by `A₀`. -/
theorem edgeDifference_bounds (x : Graph × ℕ) {e : ℕ × ℕ}
    (he : e ∈ normalEdges x.1) :
    0 < edgeDifference x e ∧ edgeDifference x e ≤ maxLabel x := by
  obtain ⟨_, hj, hij, _⟩ := mem_normalEdges.mp he
  have hlt := graphLabel_strictMono x (Nat.add_lt_add_right hij 1)
  have hbound := graphLabel_le_maxLabel x (Nat.succ_le_iff.mpr hj)
  simp only [Nat.succ_eq_add_one] at hbound
  unfold edgeDifference
  omega

/-- The scan represents exactly the set of unsigned normalized edge-label differences. -/
theorem mem_diffSet_iff (x : Graph × ℕ) (d : ℕ) :
    d ∈ diffSet x ↔ ∃ e ∈ normalEdges x.1, d = edgeDifference x e := by
  rw [mem_diffSet]
  constructor
  · exact fun h => h.2.2
  · rintro ⟨e, he, rfl⟩
    have hb := edgeDifference_bounds x he
    exact ⟨hb.2, hb.1, e, he, rfl⟩

/-- The difference list contains no repeated distance. -/
theorem diffSet_nodup (x : Graph × ℕ) : (diffSet x).Nodup :=
  List.Nodup.filter _ List.nodup_range

/-- Edge differences are enumerated in strictly increasing order. -/
theorem diffSet_increasing (x : Graph × ℕ) : (diffSet x).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

/-- Forbidden distances are enumerated in strictly increasing order. -/
theorem forbiddenDistances_increasing (x : Graph × ℕ) :
    (forbiddenDistances x).Pairwise (· < ·) := by
  apply List.Pairwise.filter
  apply List.pairwise_map.mpr
  exact List.pairwise_lt_range.imp (fun h => Nat.add_lt_add_right h 1)

/-- The Boolean window test is precisely the paper's union defining `E₊`. -/
theorem allowedDistance_eq_true (x : Graph × ℕ) (d : ℕ) :
    allowedDistance x d = true ↔ d = 1 ∨ d = 2 ∨ ∃ e ∈ diffSet x,
      d = windowSpacing * e - 1 ∨ d = windowSpacing * e ∨
        d = windowSpacing * e + 1 ∨ d = windowSpacing * e + 2 := by
  simp [allowedDistance, or_assoc]

/-- The forbidden-distance array contains precisely the excluded positive half-circle. -/
theorem mem_forbiddenDistances (x : Graph × ℕ) (d : ℕ) :
    d ∈ forbiddenDistances x ↔ 0 < d ∧ d ≤ degree x / 2 ∧
      allowedDistance x d = false := by
  simp only [forbiddenDistances, List.mem_filter, List.mem_map, List.mem_range,
    Bool.not_eq_true_eq_eq_false]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hd⟩
    exact ⟨by omega, by omega, hd⟩
  · rintro ⟨hpos, hle, hd⟩
    exact ⟨⟨d - 1, by omega, by omega⟩, hd⟩

/-- The labels array has exactly one entry per distinct declared vertex. -/
@[simp] theorem graphLabels_length (x : Graph × ℕ) :
    (graphLabels x).length = vertexCount x.1 := by simp [graphLabels]

/-- Lookup of the guard array agrees with its coefficient formula at every valid index. -/
theorem guardCoeffs_getD (x : Graph × ℕ) {i : ℕ} (hi : i < degree x) :
    (guardCoeffs x).getD i 0 = guardCoeff x i := by
  simp [guardCoeffs, List.getD_eq_getElem?_getD, hi]

/-- Lookup of the interaction array agrees with its coefficient formula. -/
theorem interactionCoeffs_getD (x : Graph × ℕ) {i : ℕ} (hi : i < degree x) :
    (interactionCoeffs x).getD i 0 = interactionCoeff x i := by
  simp [interactionCoeffs, List.getD_eq_getElem?_getD, hi]

/-- The list domain-wall program is the Coeff-level product `G(1-X)`. -/
theorem wallCoeffs_eq (x : Graph × ℕ) :
    IdealCVP.ofList (d := degree x) (wallCoeffs x) =
      IdealCVP.Cyclotomic.mul (IdealCVP.ofList (spinCoeffs x))
        (IdealCVP.ofList [1, -1]) :=
  IdealCVP.ofList_negacyclicMul _ _ _

/-- The list generator program is the Coeff-level product `(M-K)S`. -/
theorem generatorCoeffs_eq (x : Graph × ℕ) :
    IdealCVP.ofList (d := degree x) (generatorCoeffs x) =
      IdealCVP.Cyclotomic.mul (IdealCVP.ofList (dominantCoeffs x))
        (IdealCVP.ofList (parityCoeffs x)) :=
  IdealCVP.ofList_negacyclicMul _ _ _

end Power2IdealSVP.Runtime
