import Power2ModuleSVP.Runtime.Source.Normalize

/-!
# Executable Boolean source map

Interface: `SourceInput = ℕ × (ℕ × (List ℤ × List ℤ))`, storing
`(L,(T,(P,c)))`. `encSource` uses unary dimensions and signed binary
coefficients. `sourceMap_eq` identifies this list program with
`BooleanSource.threeSATEncode`, including the exact prime choices.
`sourceMap_correct` gives the affine equation with the original semantic
source. `sourceMap_polytime` (in `Runtime/Source/PolyTime.lean`, namespace
`Power2ModuleSVP`) supplies the native multitape-TM certificate.

Only finite range loops, lookup and the imported bounded prime scan occur in
the program. Polynomial interpretation occurs solely in specifications.

Paper: `paper/power2svp.pdf`, Section 4 (Proposition 2 and Lemmas 5–6).
-/
namespace Power2ModuleSVP
open Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM
open BooleanSource

/-- Stored affine dimension, polynomial degree, polynomial coefficients, and offset. -/
abbrev SourceInput := ℕ × (ℕ × (List ℤ × List ℤ))
/-- Unary dimensions and signed binary coefficient encoding of an affine source input. -/
abbrev encSource : SourceInput ↪ List Bool :=
  encPair encUnary (encPair encUnary
    (encPair (encList encIntBin) (encList encIntBin)))

namespace SourceRuntime
attribute [local irreducible] BooleanSource.positiveEncoding List.getD

/-- The executable Sidon position of a zero-based input variable. -/
def position (ell i : ℕ) := IdealCVP.SidonPositions.erdosTuranAlpha ell (i+1)
/-- The executable upper bound on the input Sidon positions. -/
def bound (ell v : ℕ) := IdealCVP.SidonPositions.erdosTuranAlpha ell v
/-- The spacing between adjacent executable clause clusters. -/
def delta (ell v : ℕ) := 4*bound ell v+1
/-- The executable exponent of a zero-based clause cluster. -/
def cluster (ell v j : ℕ) := (j+1)*delta ell v
/-- The executable degree of the reciprocal source polynomial. -/
def top (ell v r : ℕ) := (4*r+1)*delta ell v
/-- The executable dimension determined by the exponent-prime choice. -/
def dimension (ell v r : ℕ) := (exponentPrime (top ell v r)+top ell v r)/2

/-- Test membership in the unreflected clause support by a bounded scan. -/
def lowerCheck (p : PositiveInput) (ell z : ℕ) : Bool :=
  (List.range (2*p.2.length)).any fun j =>
    let t := p.2.getD (j/2) (0,0,0)
    decide (z = cluster ell p.1 j - position ell t.1 ∨
      z = cluster ell p.1 j - position ell t.2.1 ∨
      z = cluster ell p.1 j - position ell t.2.2)

/-- Test membership in the guarded reciprocal polynomial support. -/
def supportCheck (p : PositiveInput) (ell z : ℕ) : Bool :=
  decide (z = 0 ∨ z = top ell p.1 p.2.length) || lowerCheck p ell z ||
    (List.range (top ell p.1 p.2.length+1)).any (fun a =>
      lowerCheck p ell a && decide (top ell p.1 p.2.length-a = z))

/-- Test whether an exponent is reached by an input position plus a support exponent. -/
def touchedCheck (p : PositiveInput) (ell z : ℕ) : Bool :=
  (List.range p.1).any fun i =>
    (List.range (top ell p.1 p.2.length+1)).any fun a =>
      supportCheck p ell a && decide (position ell i+a = z)

/-- Test membership in the clause rows receiving negative translation. -/
def negativeCheck (p : PositiveInput) (ell z : ℕ) : Bool :=
  (List.range p.2.length).any fun j => decide (cluster ell p.1 (2*j+1) = z)

/-- Compute the ternary affine translation with the negative case taking priority. -/
def offset (p : PositiveInput) (ell z : ℕ) : ℤ :=
  if negativeCheck p ell z then -1 else if touchedCheck p ell z then 0 else 1

/-- A total coefficient-array construction; all loops have explicit unary bounds. -/
def affineData (p : PositiveInput) : SourceInput :=
  let ell := positionPrime p.1
  let t := top ell p.1 p.2.length
  let len := dimension ell p.1 p.2.length
  (len,(t,((List.range (t+1)).map (fun z => if supportCheck p ell z then 1 else 0),
    (List.range len).map (offset p ell))))

theorem any_range_iff (n : ℕ) (b : ℕ → Bool) :
    (List.range n).any b = true ↔ ∃ i : Fin n, b i.val = true := by
  simp only [List.any_eq_true, List.mem_range]
  exact ⟨fun ⟨i,hi,h⟩ => ⟨⟨i,hi⟩,h⟩,fun ⟨i,h⟩ => ⟨i,i.isLt,h⟩⟩

theorem top_eq (ell v r : ℕ) : top ell v r = SparseEncoding.T ell v r := rfl
theorem dimension_eq (ell v r : ℕ) : dimension ell v r = SparseEncoding.L ell v r := by
  unfold dimension
  rw [top_eq, exponentPrime_eq]
  rfl

/-- Relabel the positive gadget variables by their bounded natural-number codes. -/
abbrev numbered {v r : ℕ} (f : ThreeFormula v r) : PositiveInput :=
  (4+2*v+6*r, (positiveEncoding f).map codeTriple)

theorem lowerCheck_spec {v r : ℕ} (f : ThreeFormula v r) (ell z : ℕ) :
    lowerCheck (numbered f) ell z = true ↔
      z ∈ SparseEncoding.lowerSupport (finiteClauses f) ell := by
  simp only [lowerCheck, List.length_map, any_range_iff, decide_eq_true_eq,
    SparseEncoding.lowerSupport, Finset.mem_biUnion, Finset.mem_univ, true_and]
  apply exists_congr
  intro j
  have hj : j.val/2 < (positiveEncoding f).length := by have := j.isLt; omega
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj)]
  simp only [List.getElem_map, codeTriple, finiteClauses, clauseFinset,
    SparseEncoding.originalRow, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
    Sidon.position, position, variableFin]
  constructor
  · rintro (h | h | h)
    · exact ⟨_, Or.inl rfl, h.symm⟩
    · exact ⟨_, Or.inr (Or.inl rfl), h.symm⟩
    · exact ⟨_, Or.inr (Or.inr rfl), h.symm⟩
  · rintro ⟨a, (rfl | rfl | rfl), h⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h.symm)

theorem supportCheck_spec {v r : ℕ} (f : ThreeFormula v r) {ell : ℕ}
    (hell : 0 < ell) (z : ℕ) :
    supportCheck (numbered f) ell z = true ↔
      z ∈ SparseEncoding.support (finiteClauses f) ell := by
  simp only [supportCheck, Bool.or_eq_true, decide_eq_true_eq, lowerCheck_spec,
    any_range_iff, Bool.and_eq_true, numbered, List.length_map, top_eq]
  simp only [SparseEncoding.support, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro (h | ⟨a,ha,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a,ha,he⟩
  · rintro (h | ⟨a,ha,he⟩)
    · exact Or.inl h
    · have hb := (SparseEncoding.lower_bounds (finiteClauses f) hell ha).2
      have ht : a ≤ SparseEncoding.T ell (4+2*v+6*r) (positiveEncoding f).length :=
        SparseEncoding.support_bounds (finiteClauses f) hell
          (Finset.mem_union_left _ (Finset.mem_union_right _ ha))
      exact Or.inr ⟨⟨a,by omega⟩,ha,he⟩

theorem touchedCheck_spec {v r : ℕ} (f : ThreeFormula v r) {ell : ℕ}
    (hell : 0 < ell) (z : ℕ) :
    touchedCheck (numbered f) ell z = true ↔
      z ∈ SparseEncoding.touched (finiteClauses f) ell := by
  simp only [touchedCheck, any_range_iff, Bool.and_eq_true, supportCheck_spec f hell,
    decide_eq_true_eq, numbered, List.length_map, top_eq]
  simp only [SparseEncoding.touched, SparseEncoding.positions, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i,a,ha,he⟩
    exact ⟨Sidon.position ell i,⟨i,rfl⟩,a,ha,he⟩
  · rintro ⟨_,⟨i,rfl⟩,a,ha,he⟩
    have ht := SparseEncoding.support_bounds (finiteClauses f) hell ha
    exact ⟨i,⟨a,by omega⟩,ha,he⟩

theorem negativeCheck_spec {v r : ℕ} (f : ThreeFormula v r) (ell z : ℕ) :
    negativeCheck (numbered f) ell z = true ↔
      z ∈ SparseEncoding.negativeRows ell (4+2*v+6*r) (positiveEncoding f).length := by
  simp only [negativeCheck, List.length_map, any_range_iff,
    decide_eq_true_eq, SparseEncoding.negativeRows, Finset.mem_image,
    Finset.mem_univ, true_and]
  rfl

theorem offset_eq {v r : ℕ} (f : ThreeFormula v r) {ell : ℕ}
    (hell : 0 < ell) (z : ℕ) :
    offset (numbered f) ell z = SparseEncoding.translation (finiteClauses f) ell z := by
  simp only [offset, SparseEncoding.translation, negativeCheck_spec,
    touchedCheck_spec f hell]

theorem affineData_eq {v r : ℕ} (f : ThreeFormula v r) :
    affineData (numbered f) =
      let q := SparseEncoding.encode (finiteClauses f)
      (q.dimension, (q.degreeBound,
        ((List.range (q.degreeBound+1)).map (fun z => if z ∈ q.exponents then 1 else 0),
          q.offset))) := by
  have hell := (SparseEncoding.positionPrime_spec (4+2*v+6*r)).1.pos
  simp only [affineData, numbered, List.length_map, positionPrime_eq, dimension_eq,
    top_eq, SparseEncoding.encode]
  simp only [Prod.mk.injEq, true_and]
  constructor
  · apply List.map_congr_left
    intro z hz
    simp only [supportCheck_spec f hell]
    rfl
  · apply List.map_congr_left
    intro z hz
    exact offset_eq f hell z

end SourceRuntime

/-- Total map from complexitylib's binary-labelled CNF encoding. -/
def sourceMap (f : CNF ℕ) : SourceInput :=
  SourceRuntime.affineData
    (SourceRuntime.positiveData (SourceRuntime.normalizeData (toExactThreeSAT f)))

/-- Exact agreement with the completed semantic source on every CNF. -/
theorem sourceMap_eq (f : CNF ℕ) :
    sourceMap f =
      let q := BooleanSource.threeSATEncode f
      (q.dimension, (q.degreeBound,
        ((List.range (q.degreeBound+1)).map (fun z => if z ∈ q.exponents then 1 else 0),
          q.offset))) := by
  unfold sourceMap
  rw [SourceRuntime.normalizeData_eq, SourceRuntime.positiveData_eq]
  exact SourceRuntime.affineData_eq (fromThreeSAT f).formula

/-- The polynomial represented by an explicit coefficient list. -/
noncomputable def sourcePolynomial (a : List ℤ) : Polynomial ℤ :=
  SparseEncoding.vectorPolynomial a.length (fun z => a.getD z 0)

theorem sourcePolynomial_coeff (a : List ℤ) (z : ℕ) :
    (sourcePolynomial a).coeff z = a.getD z 0 := by
  rw [sourcePolynomial, SparseEncoding.vectorPolynomial_coeff]
  split_ifs with hz
  · rfl
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : a.length ≤ z)]

/-- The output lists interpreted by the same coefficientwise affine equation
as `SparseEncoding.AffineSolution`. -/
def SourceAffineSolution (q : SourceInput) (x y : Polynomial ℤ) : Prop :=
  SparseEncoding.BitPolynomial q.1 x ∧ SparseEncoding.BitPolynomial q.1 y ∧
    ∀ z < q.1, y.coeff z =
      ((sourcePolynomial q.2.2.1*x) %ₘ
        (Polynomial.X^q.1+sourcePolynomial q.2.2.1)).coeff z + q.2.2.2.getD z 0

theorem sourceMap_lengths (f : CNF ℕ) :
    (sourceMap f).2.2.1.length = (sourceMap f).2.1+1 ∧
      (sourceMap f).2.2.2.length = (sourceMap f).1 := by
  rw [sourceMap_eq]
  exact ⟨by simp, SparseEncoding.encode_offset_length _⟩

theorem sourceMap_dimension_bound (f : CNF ℕ) :
    (sourceMap f).1 ≤ 1125*(7*f.length+17)*(12*f.length+28)^2 := by
  rw [sourceMap_eq]
  exact threeSATEncode_size f

theorem sourcePolynomial_indicator {v r : ℕ} (C : SparseEncoding.Clauses v r)
    {ell : ℕ} (hell : 0 < ell) :
    sourcePolynomial ((List.range (SparseEncoding.T ell v r+1)).map
      (fun z => if z ∈ SparseEncoding.support C ell then 1 else 0)) =
        SparseEncoding.P C ell := by
  ext z
  rw [sourcePolynomial_coeff, SparseEncoding.coeff_P]
  by_cases hz : z < SparseEncoding.T ell v r+1
  · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_range] using hz)]
    simp only [List.getElem_map, List.getElem_range]
  · have hn : z ∉ SparseEncoding.support C ell := by
      intro h
      have hb := SparseEncoding.support_bounds C hell h
      omega
    rw [ite_eq_right hn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · simpa only [List.length_map, List.length_range] using Nat.le_of_not_gt hz

theorem sourceMap_polynomial (f : CNF ℕ) :
    sourcePolynomial (sourceMap f).2.2.1 =
      SparseEncoding.P (finiteClauses (fromThreeSAT f).formula)
        (SparseEncoding.positionPrime
          (4 + 2 * (fromThreeSAT f).varCount + 6 * (fromThreeSAT f).rowCount)) := by
  rw [sourceMap_eq]
  exact sourcePolynomial_indicator _
    (SparseEncoding.positionPrime_spec
      (4 + 2 * (fromThreeSAT f).varCount + 6 * (fromThreeSAT f).rowCount)).1.pos

/-- Agreement of the affine predicates, exposing only coefficient arrays to callers. -/
theorem sourceMap_solution_iff (f : CNF ℕ) (x y : Polynomial ℤ) :
    SourceAffineSolution (sourceMap f) x y ↔
      SparseEncoding.AffineSolution (finiteClauses (fromThreeSAT f).formula)
        (SparseEncoding.positionPrime
          (4 + 2 * (fromThreeSAT f).varCount + 6 * (fromThreeSAT f).rowCount)) x y := by
  unfold SourceAffineSolution
  rw [sourceMap_polynomial, sourceMap_eq]
  simp only [threeSATEncode, SparseEncoding.encode, SparseEncoding.AffineSolution]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro z
  apply forall_congr'
  intro hz
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_range] using hz)]
  simp only [List.getElem_map, List.getElem_range]

/-- Correctness for all original inputs, including malformed clauses. -/
theorem sourceMap_correct (f : CNF ℕ) :
    f ∈ ThreeSAT ↔ ∃ x y, SourceAffineSolution (sourceMap f) x y := by
  simpa only [sourceMap_solution_iff] using threeSAT_affine_correct f

end Power2ModuleSVP
