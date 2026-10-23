import Hardness.Complexity.CompileList

/-! # A compiler using polynomially bounded list loops

Cubic Sidon positions avoid prime search. All counters, including square-root
search bounds and the dimension, are computed with unary polynomial arithmetic.
Sparse coefficients are counts, so overlapping supports would retain multiplicity.
-/
namespace Hardness

namespace MaskedSys

def reductionDataCubic (S : MaskedSys) : ReductionData (S.rows.length + 1) (S.cols + 1) where
  system := S.paddedSystem
  positions := SidonPositions.cubic (S.cols + 1)
  M_pos := Nat.succ_pos _
  n_pos := Nat.succ_pos _

end MaskedSys

namespace Fast

abbrev M (S : MaskedSys) : ℕ := S.rows.length + 1
abbrev n (S : MaskedSys) : ℕ := S.cols + 1

def A (S : MaskedSys) (i j : ℕ) : Bool :=
  if i = 0 then decide (j = 0) else
    if j = 0 then false else (S.rows.getD (i-1) []).getD (j-1) false

def b (S : MaskedSys) (i : ℕ) : Bool :=
  if i = 0 then true else S.rhs.getD (i-1) false

def mask (S : MaskedSys) (j : ℕ) : Bool :=
  if j = 0 then true else S.mask.getD (j-1) false

def alpha (S : MaskedSys) (j : ℕ) : ℕ := (2 * (n S)^2 + 1) * j + j^2
def c (S : MaskedSys) : ℕ := alpha S (n S - 1)
def L (S : MaskedSys) : ℕ := 2 * c S + 1
def rho (S : MaskedSys) (i : ℕ) : ℕ := c S + i * L S
def hExp (S : MaskedSys) (i j : ℕ) : ℕ := rho S i - alpha S j
def crossExp (S : MaskedSys) (i j k : ℕ) : ℕ := hExp S i j + alpha S k

def N (S : MaskedSys) : ℕ := 2 ^ Nat.clog 2 (M S * L S)

def entries (S : MaskedSys) : List (ℕ × ℕ) :=
  (List.range (M S)).product (List.range (n S))

def crosses (S : MaskedSys) : List ((ℕ × ℕ) × ℕ) :=
  (entries S).product (List.range (n S))

def W (S : MaskedSys) : ℕ := (entries S).countP fun e => A S e.1 e.2
def nu (S : MaskedSys) : ℕ := (n S - 1) * W S

def h (S : MaskedSys) (r : ℕ) : ℕ :=
  (entries S).countP fun e => A S e.1 e.2 && decide (r = hExp S e.1 e.2)

def t (S : MaskedSys) (r : ℕ) : ℕ :=
  2 * ((List.range (M S)).countP fun i => b S i && decide (r = rho S i)) +
    (crosses S).countP fun e =>
      A S e.1.1 e.1.2 && decide (e.2 ≠ e.1.2) &&
        decide (r = crossExp S e.1.1 e.1.2 e.2)

def u (S : MaskedSys) (r : ℕ) : ℕ :=
  (List.range (n S)).countP fun j => mask S j && decide (r = alpha S j)

/-- Count precisely the integers strictly below the nonnegative square root. -/
def sqrtCeil (r : ℕ) : ℕ := (List.range r).countP fun k => decide (k^2 < r)

def P (S : MaskedSys) : ℕ :=
  let s := sqrtCeil (n S + 4)
  1 + s * (s * W S +
    sqrtCeil (4 * ((List.range (M S)).countP (b S)) + nu S) + sqrtCeil (nu S + 4))

def weight (S : MaskedSys) : ℕ := (List.range (n S)).countP (mask S)

def gCoeff (S : MaskedSys) (r : ℕ) : ℤ :=
  if r % 2 = 0 then 2 * (h S (r / 2) : ℤ)
  else if r / 2 = 0 then 2 * (P S : ℤ) else 0

def TCoeff (S : MaskedSys) (r : ℕ) : ℤ :=
  if r % 2 = 0 then (t S (r / 2) : ℤ) else (P S : ℤ) * (u S (r / 2) : ℤ)

def wellFormed (S : MaskedSys) : Bool :=
  S.rows.all (fun r => decide (r.length = S.cols)) &&
    decide (S.rhs.length = S.rows.length) && decide (S.mask.length = S.cols)

def compile (S : MaskedSys) : CVPInput :=
  (2 * N S, (List.range (2 * N S)).map (gCoeff S),
    (List.range (2 * N S)).map (TCoeff S), (P S : ℤ)^2 * (weight S : ℤ) + (nu S : ℤ))

end Fast

/-- Total list compiler; malformed inputs map to the fixed NO instance. -/
def compileFast (S : MaskedSys) : CVPInput :=
  if Fast.wellFormed S then Fast.compile S else cvpNoInput

end Hardness
