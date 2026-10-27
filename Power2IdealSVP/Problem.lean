import Power2ModuleSVP.Problem

/-!
# Problem

Exact decision SVP in the coefficient infinity norm for principal ideals `f R_n` of
`R_n = ℤ[X]/(X^n + 1)`, `n` a power of two.

An input stores the degree in unary, the generator `f` as a signed-binary coefficient array, and
the radius `r` in binary. Malformed inputs (non-dyadic degree, wrong length, `f = 0`) are
rejected. The language asks for a nonzero ideal element of coefficient max norm at most `r`,
i.e. `λ₁,∞(f R_n) ≤ r`.

Paper: `paper/power2-ideal-svp.pdf`, Theorem 1.
-/
namespace Power2IdealSVP
open Turing.MultiTapeTM
open Power2ModuleSVP (Coeff Dyadic coeffSup)

/-- Stored degree, generator coefficient array, and binary radius. -/
abbrev IdealInput := ℕ × (List ℤ × ℕ)

/-- Unary degree, signed-binary generator coefficients, and binary radius. -/
def encIdeal : IdealInput ↪ List Bool :=
  encPair encUnary (encPair (encList encIntBin) encNat)

/-- The principal ideal `f R_n` contains a nonzero element of coefficient max norm at most
`r`. -/
def IdealYes {d : ℕ} (f : Coeff d) (r : ℕ) : Prop :=
  ∃ u : Coeff d, IdealCVP.Cyclotomic.mul f u ≠ 0 ∧ coeffSup (IdealCVP.Cyclotomic.mul f u) ≤ r

/-- A dyadic degree, an exact-length generator array, and a nonzero generator. -/
def IdealInput.WellFormed (x : IdealInput) : Prop :=
  Dyadic x.1 ∧ x.2.1.length = x.1 ∧ IdealCVP.ofList (d := x.1) x.2.1 ≠ 0

/-- The encoded principal-ideal coefficient infinity-norm SVP decision language. -/
def IdealSVPLang : Set IdealInput := {x | IdealInput.WellFormed x ∧
  IdealYes (IdealCVP.ofList (d := x.1) x.2.1) x.2.2}

end Power2IdealSVP
