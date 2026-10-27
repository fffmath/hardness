# Final status — paper A

Decision NP-completeness is unconditional. `moduleSVP_npComplete` (namespace
`Power2ModuleSVPSubsetSum`, module `Main`) pairs binary-radius NP membership with the
native polynomial-time reduction from complexitylib's binary Subset Sum language.
The exact statement is `moduleSVP_npComplete : NPComplete encSVP ModuleSVPLang`.

- Mathematics: negacyclic adjoint/unit/norm API, opposite-pair identities, base-five
  support and multiplier rigidity, Boolean encoding, exact norm, nonzero determinant,
  total correctness, attained YES minimum and additive NO gap are proved.
- Runtime: actual list programs have native tidy multitape-TM certificates. Degrees
  and loop counters are unary; weights, coefficients, scales, and radius are binary.
  Powers of five use the library's intermediate bit-growth certificate. Exact list
  l1 norms are computed, including `rho`; no estimated-scale replacement is made.
- Membership: exact-length signed-binary multiplier lists, radius scans, squared bound
  `2*d*T²`, Cramer coefficient bounds and polynomial framed witness length yield NP.
  `Membership/Radius` remains shared with `Power2IdealSVP`.
- Source boundaries: repeated weights preserve multiplicities; zeros are removed;
  empty/all-zero lists use fixed degree-one identity outputs at radii one/zero.
- Corollary 4.3: `Search.witnessEquiv`, `card_shortVectors`, and executable recovery
  correctness are proved. The bijection counts actual nonzero short vectors as
  `2 * degree * number of satisfying Boolean assignments`, including the zero count.
- Corollary 4.4: `Search/Shortest` proves shortest-vector existence, correctness of
  threshold comparison for every shortest answer, and coefficient bounds. The gadget
  bound is `2M`; the total reduction needs `max 1 (2M)` for its radius-zero NO output.
  Full oracle encoding/parsing and runtime scope is governed by the `Search/` docstrings
  and the separate `Search/Turing.lean` job.
<!-- TODO-for-dispatcher: reconcile Corollary 4.4 after integrating Search/Turing.lean. -->

## Documentation and tidy

README.md states the encoded theorem, exact headline signatures, imports and locked build.
NOTES.md maps the paper to Lean and incorporates API-hp2n-amath.md's detailed signatures.
This record supersedes STATUS-hp2n-amath.md, STATUS-hp2n-arun.md,
STATUS-hp2n-asearch.md, STATUS-hp2n-mem.md, and the adocs progress note.
Those job-local files are removed. AUDIT.md is retained unchanged as historical evidence;
its original paths and prospective obligations predate the completed formalisation.

All Lean modules have a module docstring with a `Paper:` line. Added docstrings to the
remaining public simp API lemmas and wrapped the problem's encoding description.
Corrected `Search/Shortest`'s obsolete claim that reduction runtime was unavailable;
its theorem statements and proofs are unchanged. `Main` and `Search/Turing` are untouched.

Repository-wide reference searches (including `Power2IdealSVP`) found no callers of
`Reduction.pairSup_pos_iff`, `Reduction.not_ModuleYes_zero`, or `Rigidity.M_dominates`;
these elementary unused convenience lemmas were removed. Public paper endpoints and
shared algebra/membership APIs remain available, including uncalled paper-facing results.

## Verification

All final commands exited 0, using `LAKE_CACHE_DIR=/tmp/hardness-lake-cache` and
`/workspace/shared/bin/lake-locked` exclusively:

- `build Power2ModuleSVPSubsetSum`: successful, 7044 jobs. The root imports only Problem.
- Explicit `build` of `Power2ModuleSVPSubsetSum.Main`, `.Search.Witness`,
  `.Search.Shortest`, and `.Rigidity.Bounds`: successful, 7119 jobs, covering the
  changed implementation files. After wrapping a flagged docstring line, the final
  targeted `.Search.Shortest` rebuild passed (7093 jobs) without project warnings.
- `env lean /tmp/hp2n-adocs-check.lean`: successful. Exact headline signatures and
  paper-map declaration names elaborate. All 19 axiom reports (decision/runtime,
  correctness/gaps, rigidity/exact norm, witness/recovery, shortest-vector endpoints)
  contain only `propext`, `Classical.choice`, and `Quot.sound`.
- All 36 project Lean files pass the 100-character, module-doc/Paper-reference, and
  forbidden-proof-token scans. README/NOTES links resolve; `git diff --check` passes.

Existing dependency module-system warnings remain; changed project files have no warnings.
Logs: `/tmp/hp2n-adocs-build.log`, `/tmp/hp2n-adocs-endpoints-build.log`,
`/tmp/hp2n-adocs-shortest-build.log`, `/tmp/hp2n-adocs-check.log`.
No decision or witness-bijection obligations remain. Corollary 4.4's full Turing-reduction
integration is the dispatcher TODO above. No library roots, fixed definitions, dependency
sources, other subprojects, `Main.lean`, or `Search/Turing.lean` were changed.
