# hardness

Lean 4 / Mathlib formalisation of

> Jiaqi Liu, Yansong Feng, Yanbin Pan. **Exact CVP Is NP-Complete for Principal Cyclotomic Ideals.**
> arXiv:2608.23828 (ePrint 2026/1793). PDF: `paper/2608.23828.pdf`, LaTeX source: `paper/src/`.

Build with `timeout 1500 lake build` (toolchain `leanprover/lean4:v4.36.0-rc1`, Mathlib `v4.36.0-rc1`).
The library is sorry-free and adds no axioms. If the toolchain artifact cache is read-only, use
`LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 1500 lake build`.

## Final summary

Everything below is sorry-free and axiom-clean: `#print axioms` gives only `propext`,
`Classical.choice` and `Quot.sound`. Complexity classes, reductions and polynomial time are
complexitylib's native multitape-TM notions (`NP`, `NPHard`, `NPComplete`, `PolyTimeReducible`,
`PPoly`, `PH`, `SigmaP`).

### Headline theorems

| Theorem | Statement | File |
|---|---|---|
| `Hardness.principalCVP_npComplete` | `NPComplete encCVP PrincipalCVP`: exact principal cyclotomic CVP over ℤ[X]/(X^d+1) is NP-complete | `Hardness/Complexity/NPComplete.lean` |
| `Hardness.x3c_npComplete` | `NPComplete encX3C X3CLang`: X3C is NP-complete, via ExactThreeSAT → X3C (direct gadget) | `Hardness/Complexity/SatToX3C.lean` |
| `Hardness.principalCVP_npHard_via_X3C` | The paper's route to principal CVP hardness: X3C → principal CVP | `Hardness/Complexity/SatToX3C.lean` |
| `Hardness.principalCyclicCVP_npComplete` | `NPComplete encCVP SeparatedPrincipalCyclicCVP`: cyclic ℤ[X]/(X^{2d}−1), separated generators | `Hardness/Complexity/SeparatedCyclic.lean` |
| `Hardness.principalCyclicCVP_npHard` | NP-hardness for arbitrary principal cyclic CVP | `Hardness/Complexity/CyclicProblem.lean` |
| `Hardness.moduleSIVP_npComplete` | `NPComplete encModuleSIVP ModuleSIVPLang`: rank-2 module-SIVP, triangular-basis subclass | `Hardness/Complexity/ModuleProblem.lean` |
| `Cslib.Circuits.Boolean.PPoly.of_polyTimeReducible` | P/poly is closed under polynomial-time reductions | `Hardness/Complexity/PPolyReduction.lean` |
| `Hardness.np_subset_ppoly_of_fixedCVPP` | P/poly circuits for the fixed CVPP family ⇒ NP ⊆ P/poly | `Hardness/Complexity/CVPPClass.lean` |
| `Hardness.PH_eq_SigmaP_two_of_fixedCVPP` | The same hypothesis ⇒ PH = Σ₂ (Karp–Lipton) | `Hardness/Complexity/CVPPClass.lean` |
| `Hardness.PH_eq_SigmaP_two_of_polyCVPP` | Poly-size advice plus a poly-time decider for fixed-family CVPP ⇒ PH = Σ₂ | `Hardness/Complexity/CVPPClass.lean` |

Below the complexity layer sit the paper's mathematical results:

- the X3C → CVP reduction with its exact gaps: `x3c_correct`, `x3c_yes_gap`, `x3c_no_gap`;
- the cyclic and canonical-embedding variants;
- module completion: `module_completion`;
- the fixed family: `Fixed.fixed_family_correct`;
- explicit certificate bounds;
- search-to-decision.

### Remaining gaps

1. **Module-SIVP for arbitrary bases.** NP membership is proved only for the triangular subclass
   `(Q,T),(0,g)` with `Q = 1+‖T‖²+‖g‖²`. That subclass is the image of the paper's completion,
   so hardness holds as stated. NP membership for general independent rank-2 bases is not
   formalised.
2. **Cyclic CVP with singular generators.** NP membership is proved only for the
   polynomial-time-recognisable separated generators `(g+B e₀, −g+B e₀)`, which contain the
   reduction's image. It is not formalised for arbitrary, possibly singular, generators of
   ℤ[X]/(X^{2d}−1); that would need integer-solution size bounds for rank-deficient systems.
3. **CVPP is stated in a non-uniform form.** The corollary assumes P/poly circuits, or
   poly-size advice plus a poly-time decider, for the fixed family. Preprocessing time is
   unbounded, which matches the paper's corollary.
4. **Not formalised:** approximate (gap) versions beyond the exact +4 / +32 squared-distance gaps.

## Detailed entry points

- `Hardness.polyTimeReducible_X3C_FixedCVPP`, `Hardness.fixedCVPP_npHard` –
  the certified reduction to one principal ideal per unary universe size, using
  all ordered triples and a presence mask. `Hardness.FixedFast.generator_independent`
  proves that only the target and threshold depend on the input collection.
- `Hardness.PH_eq_SigmaP_two_of_fixedCVPP` – polynomial circuits for that fixed
  CVPP family imply `NP ⊆ P/poly` and `PH = Σ₂`. The universe-indexed
  polynomial-advice preprocessing version is
  `Hardness.PH_eq_SigmaP_two_of_polyCVPP`; see `Hardness/Complexity/CVPPClass.lean`.
- `Cslib.Circuits.Boolean.PPoly.of_polyTimeReducible` – closure under native
  polynomial-time reductions, including variable output lengths and arbitrary
  source encodings, in `Hardness/Complexity/PPolyReduction.lean`.
- `Hardness.moduleSIVP_npComplete` – unconditional NP-completeness for the
  polynomial-time recognizable subclass of module-SIVP with explicit triangular
  bases `(Q,T),(0,g)`, nonzero `g`, and `Q = 1 + ‖T‖² + ‖g‖²`.
  `Hardness/Complexity/ModuleProblem.lean` bridges the list language to the actual
  second successive minimum and `ModuleSIVPInstance.Yes`, reusing proved CVP
  certificate bounds. General rank-two basis membership is not asserted.
- `Hardness.principalCVP_npComplete` – **unconditional** complexitylib NP-completeness
  for exact principal cyclotomic CVP with signed binary integer data
- `Hardness.principalCVP_mem_NP` – unconditional NP membership for exact principal
  cyclotomic CVP, with binary integer data and an explicit polynomial certificate-bit bound
- `Hardness.x3c_npComplete` – unconditional complexitylib NP-completeness of list X3C;
  `encX3C` uses unary q and binary labels, with malformed triples rejected
- `Hardness.satToX3C_correct`, `Hardness.poly_satToX3C` – a direct, certified
  ExactThreeSAT → exact-one equations → three-element exact-cover gadget
- `Hardness.compileX3CList_correct`, `Hardness.polyTimeReducible_X3C_CVP` – the
  paper's incidence-matrix route, using the certified cubic compiler
- `Hardness.principalCVP_npHard_via_X3C` – unconditional principal CVP hardness
  through `x3c_npComplete`, discharging the list version of the paper's route
- `Hardness.principalCyclicCVP_npComplete` – unconditional NP-completeness of
  `SeparatedPrincipalCyclicCVP` in the actual quotient ℤ[X]/(X^{2d}−1).
  Its polynomial-time recognizable generators are exactly
  `(g+B e₀,−g+B e₀)`, with integral nonzero `B`, nonzero `g`, and power-of-two
  half-dimension `d`; targets are arbitrary lists of length `2d`.
  `Hardness/Complexity/SeparatedCyclic.lean` proves the recognizer's exact scope,
  native verifier runtime, nonsingularity, and polynomial certificate bound.
  The existing `compileCyclicFast` reduction has its image in this subclass.
- `Hardness.principalCyclicCVP_npHard` – unconditional hardness for the actual
  cyclic quotient, via `compileCyclicFast`; NP membership for arbitrary cyclic
  generators is not claimed
- `Hardness.maskedSys_npHard` – unconditional ExactThreeSAT → masked Boolean systems
  hardness, including repeated literals and degenerate/malformed inputs
- `Hardness.compileFast_correct` – total list compiler using cubic Sidon positions,
  with a coefficient-by-coefficient bridge to the mathematical reduction
- `Hardness.poly_compileFast` – native multitape TM polynomial-time certificate;
  `Hardness.polyTimeReducible_Masked_CVP` and `Hardness.principalCVP_npHard`
  complete the unconditional hardness chain
- `Hardness.compileList_correct` – the original prime-search reference compiler;
  its former conditional headline is retained as
  `Hardness.principalCVP_npComplete_of_compilePoly`. See NOTES.md, Rounds 7–8.

- `Hardness.x3cToCVP` – the X3C → principal cyclotomic CVP reduction (ℤ[y]/(y^d+1), d a power of two)
- `Hardness.x3c_correct`, `x3c_yes_gap` (min dist² = Δ), `x3c_no_gap` (dist² ≥ Δ+4),
  `exactCoverEquivClosest` (exact covers ≃ lattice points at dist² exactly Δ)
- `Hardness.x3c_correct_quotient` – the same statement in the genuine ring ℤ[X]/(X^d+1)
- `Hardness.x3c_cyclic_correct`, `x3c_cyclic_yes_gap` (8Δ), `x3c_cyclic_no_gap` (≥ 8Δ+32) –
  the cyclic extension to ℤ[X]/(X^{2d}−1)
- `Hardness.Cyclotomic.principal_full_rank`, `principalMultiplicationBasis` – full rank
  for every nonzero power-of-two cyclotomic generator, including dimension one
- `Hardness.Cyclic.principal_full_rank` – general full rank of the separated cyclic lift
- `Hardness.ModuleSIVP.module_completion` – exact second field-linear minimum Q²+dist²
- `Hardness.x3cToModuleSIVP`, `x3c_module_sivp_correct`, `x3c_module_sivp_yes`,
  `x3c_module_sivp_no` – rank-two module-SIVP reduction with squared gap Γ versus Γ+4
- `Hardness.Fixed.fixed_family_correct`, `fixed_family_yes`, `fixed_family_no` –
  masked collections of all three-subsets, with generator, ideal and basis depending only on m
- `Hardness.fixed_family_correct_indexed`, `fixed_family_yes_indexed`, `fixed_family_no_indexed` –
  the fixed family for indexed X3C, including repeated triples
- `Hardness.RationalCVPYes`, `rationalCVP_clear_denominators`, `x3c_correct_rational` –
  rational targets and thresholds, proved scaling and floor conversion
- `Hardness.ModuleSIVP.rationalBasisSIVP_clear_denominators` – arbitrary rational module
  generators reduced to an integral module, preserving field independence
- `Hardness.Canonical.norm_identity`, `field_norm_identity`, `principalCVP_iff_rational` –
  actual canonical embeddings and the squared-norm factor d (`lem:canonical`)
- `Hardness.x3c_correct_canonical`, `x3c_yes_gap_canonical`, `x3c_no_gap_canonical`,
  `x3c_module_sivp_yes_canonical`, `x3c_module_sivp_no_canonical` – canonical reductions and gaps
- `Hardness.verify_eq_true`, `matrix_cvp_iff`, `x3c_bounded_certificate` – computable matrix
  verifier and zero/one certificates for the produced instances
- `Hardness.compileX3C`, `compileX3C_correct`, `compileX3C_size` – executable finite integer
  output with explicit dimension, coefficient and threshold bounds in q,n
- `Hardness.compileX3C_coeff_bits`, `compileX3C_threshold_bits`,
  `compileX3C_outputLength_le`, `compileX3C_unaryLength_le` – explicit logarithmic
  bit bounds and polynomial binary/unary output lengths
- `Hardness.CVPPScheme`, `cvpp_advice_decides`, `cvpp_advice_decides_indexed` –
  abstract exact preprocessing gives fixed-family advice depending only on the universe size
- `Hardness.certificate_coeff_le`, `cvp_iff_bounded_certificate`,
  `cvp_iff_finite_certificate`, `decideBoundedCVP_eq_true` – explicit certificates
  and finite exhaustive decision for every nonsingular square integer basis
- `Hardness.principal_cvp_iff_bounded_certificate`, `x3c_general_bounded_certificate` –
  general principal-ideal certificates and their X3C specialization

- `Hardness.X3CInstance.decode`, `X3CInstance.decode_closest_isExactCover`,
  `Hardness.x3c_iff_decode_oracle`, `x3c_iff_checkDecoded_oracle` – computable
  cover extraction and X3C decision from any closest-vector oracle on the produced family

Polynomial running time, NP membership, and NP-completeness are formalised using the pinned
complexitylib native multitape TM API. Certificate correctness and explicit bounds for all
nonsingular square integer bases are also proved.
See [NOTES.md](NOTES.md) for the full theorem ↔ paper mapping.
The Lean code was written by Codex (prompts in `specs/`).
