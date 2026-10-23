# hardness

Lean 4 / Mathlib formalisation of

> Jiaqi Liu, Yansong Feng, Yanbin Pan. **Exact CVP Is NP-Complete for Principal Cyclotomic Ideals.**
> arXiv:2608.23828 (ePrint 2026/1793). PDF: `paper/2608.23828.pdf`, LaTeX source: `paper/src/`.

Build with `lake build` (toolchain `leanprover/lean4:v4.36.0-rc1`, Mathlib `v4.36.0-rc1`).
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

Polynomial running time / NP membership are not formalised; explicit dimension bounds are proved
instead (`x3c_dimension_le`). See [NOTES.md](NOTES.md) for the full theorem ↔ paper mapping.
The Lean code was written by Codex (prompts in `specs/`).
