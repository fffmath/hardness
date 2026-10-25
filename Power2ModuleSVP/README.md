# Power2ModuleSVP — rank-two SVP in power-of-two cyclotomic rings

Lean formalisation of [Rank-Two Module SVP in Power-of-Two Cyclotomic Rings](paper/power2svp.pdf).
The [degree-refinement companion](paper/degree-refinement.pdf) sharpens an auxiliary degree bound.

For dyadic `d`, let `R_d = ℤ[X]/(X^d + 1)`. Given a nonsingular rank-two basis over `R_d`,
deciding whether its module contains a nonzero vector of coefficient maximum norm at most one
is NP-complete under deterministic polynomial-time many-one reductions. The principal-coset
problem with nonzero even `g`, deciding whether `h + gR_d` meets the coefficient unit cube,
is also NP-complete.
Malformed coefficient arrays are rejected by the encoded languages in [Problem.lean](Problem.lean).

## Main Lean results

All names below are in namespace `Power2ModuleSVP`. Import `Power2ModuleSVP` for the whole
library, or `Power2ModuleSVP.Main` for both unconditional completeness results.

| Result | Lean name | File |
| --- | --- | --- |
| NP membership | `coset_mem_NP`, `moduleSVP_mem_NP` | [Membership/NP.lean](Membership/NP.lean) |
| Coset NP-completeness | `coset_npComplete : NPComplete encCoset CosetLang` | [Main.lean](Main.lean) |
| Module completeness from a rigid anchor family | `moduleSVP_npComplete_of (hJ : RigidAnchorFamilyHypothesis)` | [Reduction/Completeness.lean](Reduction/Completeness.lean) |
| Spectral seed to rigid anchor | `rigidAnchorFamily_of_seed` | [Anchor/FromSeed.lean](Anchor/FromSeed.lean) |
| Module completeness from a spectral seed family | `moduleSVP_npComplete_of_seed` | [Anchor/FromSeed.lean](Anchor/FromSeed.lean) |
| Certified spectral seed family | `spectralSeedFamily_holds` | [Seed/Family.lean](Seed/Family.lean) |
| **Module SVP NP-completeness** | `moduleSVP_npComplete : NPComplete encSVP ModuleSVPLang` | [Main.lean](Main.lean) |
| Integral YES/NO gap on reduction images | `moduleReduction_gap` | [Reduction/Completeness.lean](Reduction/Completeness.lean) |

Both main completeness theorems are unconditional. The useful anchor and seed interfaces remain
available for reading the proof in stages. Their hypothesis structures describe intermediate
contracts; the final assembly supplies proofs of the contracts for the concrete programs.

## Proof route

1. Translate 3SAT to positive exactly-one triples and place variables at explicit Sidon positions.
   Sparse reciprocal products, positivity padding, and a prime exponent give an affine bit source.
2. Pack the affine equation into a principal coset using parity blocks. Mahler estimates,
   reciprocal resultants, and divided derivatives recover an integer equality from the congruence.
3. Homogenize the coset with a rigid Littlewood anchor. The stored module reduction has first
   minimum one on YES inputs and every nonzero vector has norm at least two on NO inputs.
4. Construct the anchor by deterministic repair of a flat spectral seed. Rudin–Shapiro words,
   Bernstein estimates, an explicit rational sampling grid, and two rational coloring calls
   produce the seed; exact conditional expectations choose the repair flips.
5. Certify the executable reductions, frontend, repair, and coloring programs on native multitape
   Turing machines, including intermediate encoding sizes. Combine these reductions with the
   certificate verifiers for NP membership.

## Layout

| Directory | Contents |
| --- | --- |
| `Source/` | Boolean constraints, Sidon encoding, executable affine source map |
| `Coset/` | Coefficient predicates, parity blocks, packing, algebraic norm separation |
| `Anchor/` | Rigid family interface, screening, local expectations, repair, homogenization |
| `Seed/` | Spectral contract, Rudin–Shapiro words, Bernstein/Chebyshev estimates, geometry, kernel, assembly |
| `FlatFrontend/` | Rational programs, enclosure proofs, computed marked-run geometry |
| `Coloring/` | Rational specifications, projector, walk, trajectory estimates, full recursion |
| `Runtime/` | Native machine certificates for source, reduction packing, seed, frontend, repair, coloring |
| `Membership/` | Boolean verifiers, certificate bounds, runtime, NP membership |
| `Reduction/` | Total reductions, polynomial-time composition, conditional completeness, gap |
| `Problem.lean`, `Main.lean` | Encoded languages and the final unconditional theorems |

[NOTES.md](NOTES.md) maps paper results to Lean declarations.
[specs/RENAMES.md](specs/RENAMES.md) records every old-to-new module path and the dead-code audit.
[specs/STATUS.md](specs/STATUS.md) gives the current verification state. The plan and four audit
reports are historical; their opening notes explain how to resolve old file references.
Shared lattice, encoding, SAT, and prime-search infrastructure comes from `IdealCVP`,
`Rank2ModuleSVP`, Mathlib, and complexitylib.

## Verification

From the repository root, run `lake build Power2ModuleSVP`. A scratch file importing
`Power2ModuleSVP.Main` and running `#print axioms` on both completeness theorems
(via `lake env lean`) reports only
`propext`, `Classical.choice`, and `Quot.sound`. See the final verification record in STATUS.
