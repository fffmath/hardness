# hp2n-bglue — complete

Own scope: `Glue/Ideal.lean`, `Glue/Source.lean`, and this status file.
Read the shared infrastructure survey and existing Runtime, Source, Ideal interfaces.
No existing definition, library root, project configuration, dependency, or Spin file changed.
No commits (git is read-only); dispatcher should add the three new files.

## Ideal bridge

Namespace `Power2IdealSVP.Glue`; import `Power2IdealSVP.Glue.Ideal`.

- `degree_pos x : 0 < Runtime.degree x` (indeed `degree_one_lt`).
- `runtimeG x := IdealCVP.ofList (d := Runtime.degree x) (Runtime.spinCoeffs x)`.
- `runtimeTau x : ℤ := Runtime.spinThreshold x`; `runtimeTau_nonneg`.
- Intermediate identities are proved for **every input**, without a main-case assumption:
  `difference_eq` (literal `[1,-1]` = `1-X`), `wallCoeffs_eq_perturbation` (H),
  `wallNorm_eq` (R_H), `clockAmplitude_eq` (B), `clockCoeffs_eq_constructedK` (K),
  `clockNorm_eq` (R_K), `dominantAmplitude_eq` (M), `parityCoeffs_eq_sumPoly` (S),
  `dominantCoeffs_eq` (M-K), `generatorCoeffs_eq_constructedF` (f),
  `generatorCoeffs_eq_toList`, `outputRadius_eq` (r).
- `listNorm_toList` and `listNorm_eq_coeffL1` give reusable norm conversion lemmas.
- `construction_eq_outputInput` identifies the unrestricted executable construction.
- `construction_wellFormed` and `reduceList_wellFormed` prove dyadic degree, exact length,
  and a nonzero generator, including both constant branches.

Main exact statements (with `open Cslib.Complexity` in the Glue namespace):

```lean
theorem construction_eq_outputInput (x : Graph × ℕ) :
    Runtime.construction x = Ideal.outputInput (degree_pos x) (runtimeG x) (runtimeTau x)

theorem reduceList_eq_constructed {x : Graph × ℕ} (hx : Runtime.mainCase x = true) :
    Runtime.reduceList x =
      (Runtime.degree x,
        IdealCVP.toList (Ideal.constructedF (degree_pos x) (runtimeG x) (runtimeTau x)),
        (Ideal.radius (degree_pos x) (runtimeG x) (runtimeTau x)).toNat)

theorem reduceList_wellFormed (x : Graph × ℕ) : (Runtime.reduceList x).WellFormed

theorem reduceList_mem_iff {x : Graph × ℕ} (hx : Runtime.mainCase x = true) :
    Runtime.reduceList x ∈ IdealSVPLang ↔
      runtimeTau x ≤ Ideal.thetaOf (degree_pos x) (runtimeG x)
```

## Source bridge

Import `Power2IdealSVP.Glue.Source`; namespace `Power2IdealSVP.Glue`.

`differenceSet x := ((Runtime.diffSet x).map (fun d => (d : ℤ))).toFinset`.
`graphLabel_eq_label`, `maxLabel_eq_labelBound`, and `edgeDifference_eq_abs` identify
all runtime label formulas, including the empty graph bound. `mem_differenceSet` exposes
membership in the cast runtime list. No main-case assumption is used for these identities.

Exact main statements (Runtime/Source names qualified below):

```lean
theorem graphLabel_eq_label (x : Graph × ℕ) (i : Fin (Runtime.vertexCount x.1)) :
    (Runtime.graphLabel x (i.val + 1) : ℤ) = Source.label i

theorem differenceSet_eq_edgeDifferences (x : Graph × ℕ) :
    differenceSet x = Source.edgeDifferences (Runtime.normalGraph x.1)

theorem normalised_clique_iff_positions (x : Graph × ℕ) (hh : 2 ≤ x.2) :
    (∃ C : Finset (Fin (Runtime.vertexCount x.1)),
      (Runtime.normalGraph x.1).IsNClique x.2 C) ↔
    ∃ P : Finset ℤ, x.2 ≤ P.card ∧
      Source.PositiveDifferences P (differenceSet x) ∧ 0 ∈ P

theorem clique_iff_positions (x : Graph × ℕ) (hh : 2 ≤ x.2) :
    x ∈ Clique ↔ ∃ P : Finset ℤ, x.2 ≤ P.card ∧
      Source.PositiveDifferences P (differenceSet x) ∧ 0 ∈ P

theorem clique_iff_positions_exact (x : Graph × ℕ) (hh : 2 ≤ x.2) :
    x ∈ Clique ↔ ∃ P : Finset ℤ, P.card = x.2 ∧
      Source.PositiveDifferences P (differenceSet x) ∧ 0 ∈ P ∧
      ∀ p ∈ P, 0 ≤ p ∧ p ≤ (Runtime.maxLabel x : ℤ)
```

The lower bound two is stronger than the requested h ≥ 3. The forward direction of the
exact version uses `Source.clique_positions_nonneg`; extraction uses the proved Lemma 1.
The independent Source bridge was delegated under the shared AGENTS.md instructions.

## Explicit intermediate composition / integration boundary

`Glue/Ideal.lean` imports the source bridge and includes the following **conditional helper**.
`hEq1` is exactly the pending Spin equation (1) transported to `runtimeG` and `runtimeTau`.
It is an explicit argument, never an axiom, structure field, or claimed proved paper step.

```lean
theorem reduceList_correct_of_eq1
    (hEq1 : ∀ x : Graph × ℕ, Runtime.mainCase x = true →
      (runtimeTau x ≤ Ideal.thetaOf (degree_pos x) (runtimeG x) ↔
        ∃ P : Finset ℤ, x.2 ≤ P.card ∧
          Source.PositiveDifferences P (differenceSet x) ∧ 0 ∈ P))
    (x : Graph × ℕ) : x ∈ Clique ↔ Runtime.reduceList x ∈ IdealSVPLang
```

All non-main cases use `Runtime.reduceList_correct_of_not_mainCase`. In the main case,
the helper composes `clique_iff_positions`, `hEq1`, and `reduceList_mem_iff` in two lines.
The dispatcher must prove/discharge `hEq1` after Spin lands; this work does not claim an
unconditional reduction or the coefficient-level equivalence to Spin's own G.
No other proof obligations remain in this job.

## Validation

Every Lean invocation used the mandatory wrapper and machine-wide lock.
Final aggregate targeted build **PASSED**:

```sh
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked build \
  Power2IdealSVP.Glue.Ideal Power2IdealSVP.Glue.Source
```

Result: `Build completed successfully (7121 jobs)`; `/tmp/bglue-final-build.log`.
No warnings in either new module; existing dependency module-system warnings replayed.

Axiom audit **PASSED** for ten central declarations: only `propext`, `Classical.choice`,
`Quot.sound` (the label identity uses only `propext`). Script `/tmp/BGlueAudit.lean`,
log `/tmp/bglue-final-audit.log`; run with `lake-locked env lean`.
Static scan: no sorry/admit/axiom/native_decide in Glue; all Lean lines ≤ 100 characters.
