# r7-polytime — paper v2 §5.3

Owned source: `Rank2ModuleSVP/ReductionMapPoly.lean`, namespace
`Rank2ModuleSVP.ReductionMap`. The existing `ReductionMap.lean` and
`ReductionMapAux.lean` were left unchanged. No other Lean source was edited.

## Result and assembly interface

Both requested theorems are proved:

```lean
reductionMap_polytime (K0 C0 : ℕ) :
  ComputableTidilyInPolyTime (reductionMap K0 C0) IdealCVP.encX3C encSVP

reductionMap_polyTimeReducible_of_correct (K0 C0 : ℕ)
    (h : ∀ x, x ∈ IdealCVP.X3CLang ↔
      reductionMap K0 C0 x ∈ ModuleSVPLang) :
  PolyTimeReducible IdealCVP.encX3C encSVP
    IdealCVP.X3CLang ModuleSVPLang
```

Import `Rank2ModuleSVP.ReductionMapPoly` to use them. Polynomial time holds for
**all** natural `K0 C0`, including `C0 = 0`. No Wan estimate, primality premise,
asymptotic cutoff, or correctness premise is needed for the first theorem.
The second theorem takes exactly the explicitly requested semantic equivalence;
it packages that equivalence with the proved certificate. Semantic correctness
and final NP-completeness assembly remain with their respective jobs.

## Paper-to-Lean correspondence

| Paper v2 label / construction | Lean declarations | Status / hypotheses |
| --- | --- | --- |
| §5.3 power-basis arithmetic, variable dimension and exponent | `powList`, `powList_eq_ringPow`, `powList_eq_iterate`, `poly_powList` | Done. Total implementation also handles dimension zero; equality with the existing `ringPow` assumes `[NeZero q]`. |
| §5.3 intermediate coefficient encoding length | `powList_length_bound` | Done using `ringPow_abs_bound`. For input encoding length `N`, every intermediate power has encoding length at most `N*(2*(3+(2*N+2)*N)+1)`. Dimension and exponent are unary; coefficients are binary. |
| §4.1 signed offsets in the checker | `residueSub`, `residueSub_cast`, `plainOffset`, `poly_residueSub`, `poly_plainOffset`, `poly_cubicAlpha` | Done. Natural residues implement subtraction without a binary-to-unary expansion; the residue identity assumes `[NeZero q]`. |
| §4.2 integral checker sums | `plainG`, `plainV`, `poly_plainG`, `poly_plainV` | Done with ordinary `List.range`, `List.getD`, and the existing list arithmetic certificates. All loop bounds and offset arithmetic are unary. |
| Equality with existing checker definitions | `plainG_eq_gList`, `plainV_eq_vList`, `singleList_eq_atom_cast`, `range_map_eq_ofFn` | Done. Checker equalities assume `[NeZero q]`, well-formed input, positive universe size and positive triple-list length. |
| §5.3 four generator coordinate lists | `plainPi`, `plainU`, `plainCenter`, `plainCore`, `poly_plainPi`, `poly_plainU`, `poly_plainCenter`, `poly_plainCore` | Done, including variable powers and integral second coordinate `-QΓ`. |
| Equality with the existing core constructor | `plainPi_eq_piList`, `plainCore_eq_coreInput` | Done, under the same nondegenerate-input premises. |
| §5.3 preprocessing, parameters, prime scan and threshold composition | `plainReduction`, `plainReduction_eq_reductionMap`, `poly_plainReduction` | Done. Reuses `poly_mapK`, `poly_mapQ`, `poly_hasZeroRow`, `poly_threshold`, and X3C well-formedness checking. The wrapper equality is unconditional. |
| §5.3 deterministic polynomial running time | `reductionMap_polytime` | Done for every natural `K0 C0`; no additional hypotheses. |
| §5.4 reduction packaging | `reductionMap_polyTimeReducible_of_correct` | Done, given the displayed semantic correctness argument. |

All three remaining certificate tasks listed in `r6-map.md` are closed. There
are no unfinished proofs or additional assumptions in this module. Since the
universe size is already unary in `encX3C`, the computational certificate does
not need the semantic preprocessing inequality `M ≤ n`.

## Validation

- `LAKE_CACHE_DIR=/tmp/hardness-lake-cache lake env lean Rank2ModuleSVP/ReductionMapPoly.lean`
  passed.
- `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build Rank2ModuleSVP.ReductionMapPoly`
  passed (7085 jobs; style warnings only).
- A scratch Lean file ran `#print axioms` on **all 34 new theorems**, including
  both requested main theorems. Every axiom set is contained in
  `{propext, Classical.choice, Quot.sound}`. No `sorryAx` occurs.
- No `sorry`, `axiom`, or `native_decide` declaration occurs in the new source.
- Scratch files were removed after validation.
