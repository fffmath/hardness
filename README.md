# hardness

Lean 4 / Mathlib formalisation of

> Jiaqi Liu, Yansong Feng, Yanbin Pan. **Exact CVP Is NP-Complete for Principal Cyclotomic Ideals.**
> arXiv:2608.23828 (ePrint 2026/1793). PDF: `paper/2608.23828.pdf`, LaTeX source: `paper/src/`.

Build with `timeout 1500 lake build` (toolchain `leanprover/lean4:v4.36.0-rc1`, Mathlib `v4.36.0-rc1`).
The library is sorry-free and adds no axioms.

Main entry points:

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

Polynomial running time and complexity-class NP membership are not formalised. Certificate
correctness and explicit bounds for all nonsingular square integer bases are proved.
See [NOTES.md](NOTES.md) for the full theorem ↔ paper mapping.
The Lean code was written by Codex (prompts in `specs/`).
