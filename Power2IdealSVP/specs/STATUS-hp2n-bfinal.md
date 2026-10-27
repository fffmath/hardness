# hp2n-bfinal — complete

Paper B is closed: equation (1) is discharged, the total executable CLIQUE
reduction is unconditionally correct, and principal ideal coefficient
infinity-norm SVP in dyadic degree is NP-complete.

Read INFRA.md, the bsrc/bspin/bglue status reports, both fixed problem
interfaces, Paper B, and AUDIT_B.md. Independent bridges were delegated under
`/workspace/shared/AGENTS.md`. Every Lean invocation used
`/workspace/shared/bin/lake-locked` and `LAKE_CACHE_DIR=/tmp/hardness-lake-cache`.

## Files

Added:

- `Glue/Distances.lean`: natural distance-set validity and equivalence of the
  Spin and Source positive-difference predicates.
- `Glue/Theta.lean`: equivalence of prefix and rank alternation, followed by
  exact equality of the finite sparse-spin objectives.
- `Glue/Spin.lean`: runtime parameter, degree, ordering, guard, interaction,
  amplitude, and coefficient-list identities.
- `Glue/Correctness.lean`: degree-independent objective transport through
  canonical lists, executable equation (1), and unconditional correctness.
- `Main.lean`: polynomial reduction, NP-hardness, and NP-completeness.

Updated:

- `Glue/Ideal.lean`: documentation now points to the discharged equation (1).
- `Power2IdealSVP.lean`: imports Main and every project module; module docstring
  follows the import header, matching the other complete library roots.
- This status report.

No mathematical definitions were changed. The runtime and Spin constants
already agree with the paper. In particular, both guard constructions add
both monomial contributions at the antipodal coordinate. No hypotheses were
added to the final correctness or hardness results. No edits were made to
`Power2ModuleSVPSubsetSum/`, its root, the root README, fixed problem
interfaces, package sources, or project configuration. No commits attempted.

## Exact bridge declarations

In namespace `Power2IdealSVP.Glue`, with `Graph = Cslib.Complexity.Graph`
and `Coeff = Power2ModuleSVP.Coeff`:

```lean
def spinDistances (x : Graph × ℕ) : Finset ℕ :=
  (Runtime.diffSet x).toFinset

theorem spinDistances_valid (x : Graph × ℕ) :
    Spin.DValid (spinDistances x) (Runtime.maxLabel x)

theorem positiveDifferences_iff (x : Graph × ℕ) (P : Finset ℤ) :
    Spin.PositiveDifferences (spinDistances x) P ↔
      Source.PositiveDifferences P (differenceSet x)

theorem oddAlternating_iff {n : ℕ} (σ : Coeff n) :
    Ideal.OddAlternating σ ↔ Spin.OddAlternating σ

theorem thetaOf_eq_Theta {n : ℕ} (hn : 0 < n) (G : Coeff n) :
    Ideal.thetaOf hn G = Spin.Theta G

theorem degree_eq_spin (x : Graph × ℕ) :
    Runtime.degree x = Spin.n (Runtime.maxLabel x)

theorem runtimeTau_eq (x : Graph × ℕ) :
    runtimeTau x = Spin.tau (spinDistances x) (Runtime.maxLabel x) x.2

theorem runtimeG_eq_toList (x : Graph × ℕ) :
    IdealCVP.toList (runtimeG x) =
      IdealCVP.toList (Spin.G (spinDistances x) (Runtime.maxLabel x) x.2)

theorem Theta_eq_of_toList_eq {n m : ℕ} {G : Coeff n} {H : Coeff m}
    (h : IdealCVP.toList G = IdealCVP.toList H) :
    Spin.Theta G = Spin.Theta H

theorem runtime_eq1 (x : Graph × ℕ) (hx : Runtime.mainCase x = true) :
    runtimeTau x ≤ Ideal.thetaOf (degree_pos x) (runtimeG x) ↔
      ∃ P : Finset ℤ, x.2 ≤ P.card ∧
        Source.PositiveDifferences P (differenceSet x) ∧ 0 ∈ P
```

`runtime_eq1` discharges precisely the argument `hEq1` of
`Glue.reduceList_correct_of_eq1`. Its positive-target requirement follows
from `Runtime.mainCase_eq_true`. All parameter identities hold for every
input, including inputs outside the main case. Canonical-list equality
avoids dependent-type casts; list lengths recover equality of degrees.

Other proved identities in `Glue/Spin.lean`: `windowBound_eq`,
`allowedDistance_iff`, `forbiddenDistances_eq`, `guardCoeff_eq`,
`interactionCoeff_eq`, `interactionCoeffs_eq_toList`, `interactionNorm_eq`,
`neighborAmplitude_eq`, `guardAmplitude_eq`, and `spinCoeffs_eq_toList`.

## Exact final declarations

In namespace `Power2IdealSVP`:

```lean
theorem reduceList_correct (x : Cslib.Complexity.Graph × ℕ) :
    x ∈ Cslib.Complexity.Clique ↔ Runtime.reduceList x ∈ IdealSVPLang

theorem clique_polyTimeReducible_idealSVP :
    PolyTimeReducible (encPair encGraph encNat) encIdeal
      Cslib.Complexity.Clique IdealSVPLang

theorem idealSVP_npHard : NPHard encIdeal IdealSVPLang

theorem idealSVP_npComplete : NPComplete encIdeal IdealSVPLang
```

Correctness includes all non-main cases through the existing
`Runtime.reduceList_correct_of_not_mainCase`. The native runtime certificate
is `Runtime.reduceList_polytime`; NP-hardness is exactly
`Cslib.Complexity.Clique_npHard.trans clique_polyTimeReducible_idealSVP`.
NP-completeness combines this with `idealSVP_mem_NP`.

## Validation

Full required locked build PASSED:

```sh
LAKE_CACHE_DIR=/tmp/hardness-lake-cache /workspace/shared/bin/lake-locked build Power2IdealSVP
```

Result: `Build completed successfully (7180 jobs)`.
Log: `/tmp/hp2n-bfinal-build.log`. No warnings in the new/updated modules or
library root; inherited module-system import warnings replay from dependencies.
The root module docstring warning is resolved.

Axiom audit script: `/tmp/hp2n-bfinal-audit.lean`.
Log: `/tmp/hp2n-bfinal-audit.log`. It checks every principal bridge and final
interface and prints axioms of `Glue.runtime_eq1`, `reduceList_correct`, and
`idealSVP_npComplete`. Audit PASSED: each depends on exactly
`[propext, Classical.choice, Quot.sound]`.

Static checks: `git diff --check` passes; all new/modified Lean lines are at
most 100 characters; no `sorry`, `admit`, new `axiom`, or `native_decide`.
Every project Lean module is explicitly imported by the root.

No mathematical gaps or remaining proof obligations.
