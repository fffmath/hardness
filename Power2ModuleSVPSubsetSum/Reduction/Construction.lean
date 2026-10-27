import Power2ModuleSVPSubsetSum.Problem
import Power2ModuleSVP.Coset.ParityBlock

/-!
# Executable Subset Sum gadget

The coefficient-list program for equations (4.1)–(4.3). All loops range over the
number of weights or the output degree; weights, the target, and scales are used
only in integer arithmetic. The actual l1 norms determine the scales.

Paper: `paper/power2svp-subsetsum.pdf`, Section 4.1.
-/

namespace Power2ModuleSVPSubsetSum.Reduction
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- Least dyadic half-degree at least two and at least the number of weights. -/
def halfDegree (s : ℕ) : ℕ := 2 ^ Nat.clog 2 (max 2 s)

/-- The output ring degree, represented in unary by the problem encoding. -/
def degree (s : ℕ) : ℕ := 2 * halfDegree s

/-- The degree is always dyadic, including for an empty weight list. -/
theorem degree_dyadic (s : ℕ) : Dyadic (degree s) := by
  refine ⟨Nat.clog 2 (max 2 s) + 1, ?_⟩
  simp [degree, halfDegree, pow_succ, Nat.mul_comm]

/-- The filter always has half-degree at least two. -/
theorem two_le_halfDegree (s : ℕ) : 2 ≤ halfDegree s := by
  exact (le_max_left 2 s).trans
    ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl)

/-- Every weight has a distinct position in the first half of the coefficient array. -/
theorem length_le_halfDegree (s : ℕ) : s ≤ halfDegree s := by
  exact (le_max_right 2 s).trans
    ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl)

/-- List l1 norm, computed by a map and a sum of binary natural numbers. -/
def listL1 (a : List ℤ) : ℕ := (a.map Int.natAbs).sum

/-- Scale an exact-length coefficient array, padding shorter arrays with zeros. -/
def scale (n : ℕ) (c : ℤ) (a : List ℤ) : List ℤ :=
  (List.range n).map fun i => c * a.getD i 0

/-- A constant polynomial, stored in an array of the specified degree. -/
def constant (n : ℕ) (c : ℤ) : List ℤ :=
  (List.range n).map fun i => if i = 0 then c else 0

/-- The coefficient array of `1 + X^m` in degree `2m`. -/
def filterD (m : ℕ) : List ℤ :=
  (List.range (2 * m)).map fun i => if i = 0 ∨ i = m then 1 else 0

/-- The coefficient array of `1 - X^m` in degree `2m`. -/
def filterDStar (m : ℕ) : List ℤ :=
  (List.range (2 * m)).map fun i => if i = 0 then 1 else if i = m then -1 else 0

/-- Balanced-base-five filter. The zero and middle coefficients are zero. -/
def filterK (m : ℕ) : List ℤ :=
  (List.range (2 * m)).map fun i =>
    if 0 < i ∧ i < m then (5 : ℤ) ^ (i - 1)
    else if m < i then (5 : ℤ) ^ (2 * m - i - 1) else 0

/-- Boolean mask polynomial `u`, with one in each weight position. -/
def mask (n s : ℕ) : List ℤ :=
  (List.range n).map fun i => if i < s then 1 else 0

/-- Laurent weight polynomial `h = Σ_j w_j X^(-j)`, with negacyclic signs. -/
def weights (n : ℕ) (w : List ℕ) : List ℤ :=
  (List.range n).map fun i =>
    if i = 0 then (w.getD 0 0 : ℤ) else -(w.getD (n - i) 0 : ℤ)

/-- All intermediate arrays and scales, retained as data for the correctness bridge.
There are no logical assumptions or proof fields in this executable record. -/
structure Gadget where
  m : ℕ
  H : List ℤ
  V : List ℤ
  DK : List ℤ
  u : List ℤ
  F : ℕ
  nu : ℕ
  rho : ℕ
  L : ℕ
  M : ℕ
  Q : List ℤ

/-- Compute the paper's gadget using binary arithmetic and explicit coefficient lists.
`rho` is the exact norm of `DK`, rather than the upper bound in Lemma 3.1. -/
def gadget (w : List ℕ) (B : ℕ) : Gadget :=
  let m := halfDegree w.length
  let n := 2 * m
  let D := filterD m
  let DStar := filterDStar m
  let DK := IdealCVP.negacyclicMul n D (filterK m)
  let H := IdealCVP.negacyclicMul n DStar (weights n w)
  let E : ℤ := 2 * (B : ℤ) - (w.sum : ℤ)
  let V := scale n E DStar
  let F := listL1 H
  let nu := listL1 V
  let rho := listL1 DK
  let L := F + nu + 1
  let M := 2 * (L * rho + nu) + F + 1
  let Q := IdealCVP.listAdd n (scale n (M : ℤ) D) (scale n (L : ℤ) DK)
  ⟨m, H, V, DK, mask n w.length, F, nu, rho, L, M, Q⟩

/-- Store the two columns of (4.3) and the radius `M`.
The outer total reduction will preprocess zeros and dispatch an empty list. -/
def positiveReduce (w : List ℕ) (B : ℕ) : SVPInput :=
  let p := gadget w B
  let n := 2 * p.m
  let Hu := IdealCVP.negacyclicMul n p.H p.u
  let topRight := IdealCVP.listSub n
    (IdealCVP.listSub n (scale n (-1) Hu) p.Q) p.V
  ((n, (scale n 2 p.H, constant n (2 * (p.M : ℤ))),
    (topRight, scale n (-(p.M : ℤ)) p.u)), p.M)

@[simp] theorem length_scale (n : ℕ) (c : ℤ) (a : List ℤ) :
    (scale n c a).length = n := by simp [scale]

@[simp] theorem length_constant (n : ℕ) (c : ℤ) :
    (constant n c).length = n := by simp [constant]

/-- List scalar multiplication agrees with scalar multiplication of coefficient vectors. -/
@[simp] theorem ofList_scale (n : ℕ) (c : ℤ) (a : List ℤ) :
    IdealCVP.ofList (d := n) (scale n c a) = c • IdealCVP.ofList a := by
  ext i
  simp [IdealCVP.ofList, scale, List.getD_eq_getElem?_getD, i.isLt]

/-- Stored constants are scalar multiples of the coefficient identity. -/
theorem ofList_constant (n : ℕ) (hn : 0 < n) (c : ℤ) :
    IdealCVP.ofList (d := n) (constant n c) = c • coeffOne hn := by
  ext i
  simp [IdealCVP.ofList, constant, coeffOne, monomial, Fin.ext_iff,
    List.getD_eq_getElem?_getD, i.isLt]

/-- Every stored generator has exactly the output degree coefficients. -/
theorem positiveReduce_lengths (w : List ℕ) (B : ℕ) :
    let x := positiveReduce w B
    x.1.2.1.1.length = x.1.1 ∧ x.1.2.1.2.length = x.1.1 ∧
      x.1.2.2.1.length = x.1.1 ∧ x.1.2.2.2.length = x.1.1 := by
  simp [positiveReduce, IdealCVP.listSub]

/-- The output degree is the prescribed power of two. -/
theorem positiveReduce_dyadic (w : List ℕ) (B : ℕ) :
    Dyadic (positiveReduce w B).1.1 := degree_dyadic w.length

/-- The radius is strictly positive. -/
theorem gadget_M_pos (w : List ℕ) (B : ℕ) : 0 < (gadget w B).M := by
  simp only [gadget]
  omega

/-- The exact coefficient-model columns of the list program. -/
theorem positiveReduce_columns (w : List ℕ) (B : ℕ) :
    let p := gadget w B
    let n := 2 * p.m
    let H := IdealCVP.ofList (d := n) p.H
    let u := IdealCVP.ofList (d := n) p.u
    let Q := IdealCVP.ofList (d := n) p.Q
    let V := IdealCVP.ofList (d := n) p.V
    let x := positiveReduce w B
    (IdealCVP.ofList (d := n) x.1.2.1.1,
      IdealCVP.ofList (d := n) x.1.2.1.2) =
      ((2 : ℤ) • H, (2 * (p.M : ℤ)) • coeffOne
        (by have := two_le_halfDegree w.length; dsimp [n, p, gadget]; omega)) ∧
    (IdealCVP.ofList (d := n) x.1.2.2.1,
      IdealCVP.ofList (d := n) x.1.2.2.2) =
      (-mul H u - Q - V, (-(p.M : ℤ)) • u) := by
  dsimp only
  constructor
  · apply Prod.ext
    · exact ofList_scale _ _ _
    · exact ofList_constant _ _ _
  · apply Prod.ext
    · simp only [positiveReduce, IdealCVP.ofList_listSub, ofList_scale,
        IdealCVP.ofList_negacyclicMul, neg_one_zsmul]
    · exact ofList_scale _ _ _

end Power2ModuleSVPSubsetSum.Reduction
