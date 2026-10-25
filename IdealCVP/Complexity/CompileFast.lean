import IdealCVP.Complexity.CompileList

/-! # A compiler using polynomially bounded list loops

Cubic Sidon positions avoid prime search. All counters, including square-root
search bounds and the dimension, are computed with unary polynomial arithmetic.
Sparse coefficients are counts, so overlapping supports would retain multiplicity.
-/

namespace IdealCVP

namespace MaskedSys

/-- Mathematical reduction data using padded equations and cubic Sidon positions. -/
def reductionDataCubic (S : MaskedSys) : ReductionData (S.rows.length + 1) (S.cols + 1) where
  system := S.paddedSystem
  positions := SidonPositions.cubic (S.cols + 1)
  M_pos := Nat.succ_pos _
  n_pos := Nat.succ_pos _

end MaskedSys

namespace Fast

/-- The padded number of equations. -/
abbrev M (S : MaskedSys) : ℕ := S.rows.length + 1

/-- The padded number of Boolean variables. -/
abbrev n (S : MaskedSys) : ℕ := S.cols + 1

/-- Total lookup in the padded incidence matrix. -/
def A (S : MaskedSys) (i j : ℕ) : Bool :=
  if i = 0 then decide (j = 0) else
    if j = 0 then false else (S.rows.getD (i - 1) []).getD (j - 1) false

/-- Total lookup in the padded right-hand side. -/
def b (S : MaskedSys) (i : ℕ) : Bool :=
  if i = 0 then true else S.rhs.getD (i - 1) false

/-- Total lookup in the padded selection mask. -/
def mask (S : MaskedSys) (j : ℕ) : Bool :=
  if j = 0 then true else S.mask.getD (j - 1) false

/-- The cubic Sidon position of a column. -/
def alpha (S : MaskedSys) (j : ℕ) : ℕ := (2 * (n S) ^ 2 + 1) * j + j ^ 2

/-- The largest column position. -/
def c (S : MaskedSys) : ℕ := alpha S (n S - 1)

/-- The spacing between consecutive equation blocks. -/
def L (S : MaskedSys) : ℕ := 2 * c S + 1

/-- The distinguished position of an equation block. -/
def rho (S : MaskedSys) (i : ℕ) : ℕ := c S + i * L S

/-- The generator exponent associated to a matrix entry. -/
def hExp (S : MaskedSys) (i j : ℕ) : ℕ := rho S i - alpha S j

/-- The exponent of a cross term between two columns in an equation block. -/
def crossExp (S : MaskedSys) (i j k : ℕ) : ℕ := hExp S i j + alpha S k

/-- The least power of two large enough for all equation blocks. -/
def N (S : MaskedSys) : ℕ := 2 ^ Nat.clog 2 (M S * L S)

/-- Enumerate every padded row-column pair. -/
def entries (S : MaskedSys) : List (ℕ × ℕ) :=
  (List.range (M S)).product (List.range (n S))

/-- Enumerate every padded row-column pair with a second column. -/
def crosses (S : MaskedSys) : List ((ℕ × ℕ) × ℕ) :=
  (entries S).product (List.range (n S))

/-- The number of true entries in the padded incidence matrix. -/
def W (S : MaskedSys) : ℕ := (entries S).countP fun e => A S e.1 e.2

/-- The total cross-term contribution to the squared-distance threshold. -/
def nu (S : MaskedSys) : ℕ := (n S - 1) * W S

/-- Compute a coefficient of the sparse generator by counting its support entries. -/
def h (S : MaskedSys) (r : ℕ) : ℕ :=
  (entries S).countP fun e => A S e.1 e.2 && decide (r = hExp S e.1 e.2)

/-- Compute a coefficient of the even target block, retaining support multiplicities. -/
def t (S : MaskedSys) (r : ℕ) : ℕ :=
  2 * ((List.range (M S)).countP fun i => b S i && decide (r = rho S i)) +
    (crosses S).countP fun e =>
      A S e.1.1 e.1.2 && decide (e.2 ≠ e.1.2) &&
        decide (r = crossExp S e.1.1 e.1.2 e.2)

/-- Compute a coefficient of the mask vector. -/
def u (S : MaskedSys) (r : ℕ) : ℕ :=
  (List.range (n S)).countP fun j => mask S j && decide (r = alpha S j)

/-- Count precisely the integers strictly below the nonnegative square root. -/
def sqrtCeil (r : ℕ) : ℕ := (List.range r).countP fun k => decide (k ^ 2 < r)

/-- The integral penalty scale separating noncanonical coefficient choices. -/
def P (S : MaskedSys) : ℕ :=
  let s := sqrtCeil (n S + 4)
  1 + s * (s * W S +
    sqrtCeil (4 * ((List.range (M S)).countP (b S)) + nu S) + sqrtCeil (nu S + 4))

/-- The number of allowed columns in the padded mask. -/
def weight (S : MaskedSys) : ℕ := (List.range (n S)).countP (mask S)

/-- Compute a coefficient of the principal ideal generator. -/
def gCoeff (S : MaskedSys) (r : ℕ) : ℤ :=
  if r % 2 = 0 then 2 * (h S (r / 2) : ℤ)
  else if r / 2 = 0 then 2 * (P S : ℤ) else 0

/-- Compute a coefficient of the target vector. -/
def TCoeff (S : MaskedSys) (r : ℕ) : ℤ :=
  if r % 2 = 0 then (t S (r / 2) : ℤ) else (P S : ℤ) * (u S (r / 2) : ℤ)

/-- Check the declared row, right-hand-side, and mask lengths. -/
def wellFormed (S : MaskedSys) : Bool :=
  S.rows.all (fun r => decide (r.length = S.cols)) &&
    decide (S.rhs.length = S.rows.length) && decide (S.mask.length = S.cols)

/-- Compile the padded data into the generator, target, and squared threshold. -/
def compile (S : MaskedSys) : CVPInput :=
  (2 * N S, (List.range (2 * N S)).map (gCoeff S),
    (List.range (2 * N S)).map (TCoeff S), (P S : ℤ) ^ 2 * (weight S : ℤ) + (nu S : ℤ))

end Fast

/-- Total list compiler; malformed inputs map to the fixed NO instance. -/
def compileFast (S : MaskedSys) : CVPInput :=
  if Fast.wellFormed S then Fast.compile S else cvpNoInput

end IdealCVP
