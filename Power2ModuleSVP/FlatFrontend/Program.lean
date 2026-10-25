import Power2ModuleSVP.FlatFrontend.Words
import Power2ModuleSVP.FlatFrontend.Taylor

/-!
# Program

The total rational frontend. This module defines programs, not a claim of
the preparation contract. Every loop has an explicit natural bound. The
same preprocessing is recomputed in both calls, so there is no hidden state.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend

def precision (N : ℕ) : ℕ := 128 + 64 * Nat.log2 (N + 1)

def taylorOrder (N : ℕ) : ℕ := 128 * (N + 1) ^ 2 + precision N

def sqrtApprox (p N : ℕ) : ℚ :=
  (Nat.sqrt (N * (2 ^ p) ^ 2) : ℚ) / (2 ^ p : ℕ)

def clamp (a b q : ℚ) : ℚ := max a (min b q)

def gridSample (N r : ℕ) : ℚ :=
  let M := gridSize N
  if r = 0 then 1
  else if M ≤ r then -1
  else if 2 * r = M then 0
  else
    let s := if 2 * r < M then r else M - r
    let y := clamp 0 1 (cosTaylor (taylorOrder N)
      ((s : ℚ) * piTaylor (precision N) / M))
    if 2 * r < M then y else -y

/-- The first-kind recurrence is evaluated in one forward pass. -/
def chebyshevPair : ℕ → ℚ → ℚ × ℚ
  | 0, q => (1, q)
  | n + 1, q =>
    let p := chebyshevPair n q
    (p.2, 2 * q * p.2 - p.1)

def cosinePolynomialValue (N : ℕ) (q : ℚ) : ℚ :=
  ((List.range N).map fun j =>
    (cosineCoefficient N (j + 1) : ℚ) * (chebyshevPair (2 * (j + 1)) q).1).sum

/-- The endpoints of a closed cell are both included. -/
def markedCell (N j : ℕ) : Bool :=
  (List.range (gridRatio N + 1)).any fun r =>
    decide (|cosinePolynomialValue N (gridSample N (j * gridRatio N + r))| ≤
      3 * height N / 4)

/-- A single pass merges a Boolean word into half-open index runs. The
corresponding angular intervals include both endpoint angles. -/
def scanCells : ℕ → Option ℕ → List Bool → List (ℕ × ℕ)
  | _, none, [] => []
  | p, some a, [] => [(a, p)]
  | p, none, b :: bs =>
    scanCells (p + 1) (if b then some p else none) bs
  | p, some a, b :: bs =>
    if b then scanCells (p + 1) (some a) bs
    else (a, p) :: scanCells (p + 1) none bs

def intervals (N : ℕ) : List (ℕ × ℕ) :=
  scanCells 0 none ((List.range (N / 2)).map (markedCell N))

def firstThreshold (N J : ℕ) : ℚ :=
  (Nat.sqrt (56 * (Nat.log2 (64 * N / J) + 1) / 5) + 1 : ℕ)

def kernelEntry (N : ℕ) (I : ℕ × ℕ) (j : ℕ) : ℚ :=
  let m := 2 * j + 1
  let p := piTaylor (precision N)
  let a := cosTaylor (taylorOrder N) ((m * I.1 : ℕ) * p / N)
  let b := cosTaylor (taylorOrder N) ((m * I.2 : ℕ) * p / N)
  36000 * sqrtApprox (precision N) N * (a - b) / m

def intervalInput (d : ℕ) : PartialColoringInput :=
  let N := seedN d
  let Is := intervals N
  let J := Is.length
  if J = 0 then ([], ([], []))
  else
    ((List.range N).map (fun j => Is.map (fun I => kernelEntry N I j)),
      (List.replicate J 0, List.replicate N (firstThreshold N J)))

def fractionalCoefficient (N : ℕ) (Is : List (ℕ × ℕ)) (α : List ℚ) (j : ℕ) : ℚ :=
  ((List.range Is.length).map fun i =>
    α.getD i 1 * kernelEntry N (Is.getD i (0, 0)) j).sum

def derivativeEntry (N k ell j : ℕ) : ℚ :=
  let m := 2 * j + 1
  let q := (m * (2 * k + 1) : ℕ) * piTaylor (precision N) / (64 * (N : ℚ))
  let p := expTaylor (taylorOrder N) q
  ((m : ℚ) / (2 * N : ℕ)) ^ ell *
    ((phase ell).1 * p.2 + (phase ell).2 * p.1)

def coefficientInput (a : ℕ × List ℚ) : PartialColoringInput :=
  let N := seedN a.1
  let Is := intervals N
  let rows := List.range (16 * N * (N + 1))
  (rows.map (fun i => (List.range N).map
      (derivativeEntry N (i % (16 * N)) (i / (16 * N)))),
    ((List.range N).map (fun j => clamp (-(4 / 5)) (4 / 5)
      (fractionalCoefficient N Is a.2 j)),
      rows.map fun i => 12 + (i / (16 * N) : ℕ)))

end FlatFrontend

/-- Explicit integer/rational programs for all three frontend calls.
Correctness and native runtime are separate obligations. -/
def flatFrontend : FlatSeedFrontend where
  background := FlatFrontend.background
  intervalInput := FlatFrontend.intervalInput
  coefficientInput := FlatFrontend.coefficientInput

end Power2ModuleSVP
