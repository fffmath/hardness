
YOUR JOB: JOBNAME = r3-reduction. Files: Rank2ModuleSVP/Reduction.lean (optionally
Rank2ModuleSVP/ReductionAux.lean, Rank2ModuleSVP/Clearing.lean). Imports allowed: every committed
round-1/2 module (Checker, CheckerAux, Completions, Wan, Descent, Descent2, RobustCenter,
BennettPeikert, GaussSum, Sparse, SparsePolynomial, Problem, PrimeCyclotomic) and IdealCVP.
Do NOT import Asymptotics*/Membership* (other jobs are writing them right now).

GOAL: reduction.tex, sections up to and including subsec:denominator-clearing (lines 1-~465):
1. The rational module M = O_K(Uπ^k,0) + O_K(Uc − V, −Γ) (eq:module-vector-exact), threshold S,
   using Checker's U, V (checkerV), the robust centre from RobustCenter and ramifiedIdeal from
   PrimeCyclotomic/Descent2. Where the paper uses a real Γ, follow eq:Gamma-target-exact /
   eq:F-S-nu-exact exactly (Γ² rational is fine if that is what the paper does).
2. Thm exact-X3C-encoding: completeness (X3C YES ⇒ a nonzero module vector of norm ≤ S) and soundness
   (norm ≤ S ⇒ X3C YES, the four cases on w). Every purely numerical inequality that the paper
   derives from "q sufficiently large" (lem:gap-and-stability and the parameter choices) must be taken
   as fields of ONE explicit hypothesis structure you define, e.g. `structure GapConditions (q k h T : ℕ)
   (Γsq S : ℚ) : Prop` (another job, r3-asymptotics, is proving these eventually; keep each field a
   plain inequality between explicit numbers so it can be discharged later). Clean / enhanced-clean
   representatives: take their existence as an explicit premise phrased with the round-2 definitions
   (Completions' clean notion / Checker.Clean), NOT a new axiom.
3. Denominator clearing (subsec:denominator-clearing, eq:cleared-UV-exact, eq:integral-module-exact,
   eq:scaled-exact-encoding, Hadamard bounds eq:hadamard-norm-r / eq:hadamard-quotient-r): the integral
   module over IntegerRing q and scaled threshold, with the exact equivalence of SVPYes for the
   integral module (Problem.lean's `SVPYes`, via `powerPair` of explicit power-basis lists) and the
   rational statement; size bounds of the produced coefficients (polynomial in q).
Target headline: `theorem exact_X3C_encoding` and `theorem integral_encoding_correct` relating an X3C
instance (IdealCVP X3C types, IdealCVP.Complexity.X3CList) to `ModuleSVPLang` membership of the produced
`SVPInput`, under GapConditions + representative premises. Record every premise in the notes.
