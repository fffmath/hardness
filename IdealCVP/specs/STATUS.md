# IdealCVP final status

The formalisation is complete for the exact problems described in
[README.md](../README.md). The paper ↔ Lean map and mathematical notes
are in [NOTES.md](../NOTES.md); development history is retained in git.

- Principal power-of-two cyclotomic CVP is NP-complete:
  `IdealCVP.principalCVP_npComplete`.
- List X3C is NP-complete, with a certified ExactThreeSAT reduction and the
  paper's X3C → principal CVP route.
- Principal cyclic CVP is NP-complete for both separated generators and
  arbitrary generators, including singular and zero generators.
- Rank-two module-SIVP is NP-complete for the triangular completion subclass
  and for arbitrary independent integral cyclotomic bases.
- The fixed-family CVPP corollaries prove NP ⊆ P/poly and PH = Σ₂ under the
  stated circuit or polynomial-advice query hypotheses.
- Rational data, canonical embeddings, exact squared-distance gaps,
  certificate bounds, and closest-vector cover extraction are formalised.
- The source is sorry-free and adds no axioms. Headline theorem axiom audits
  allow only `propext`, `Classical.choice`, and `Quot.sound`.

The CVPP statements permit unbounded preprocessing; its output advice and
query runtime satisfy the stated polynomial bounds. Approximate variants
beyond the exact +4 / +32 squared-distance gaps are not formalised.

Build the library from the repository root with `lake build IdealCVP`.
The shared tidy jobs use their serialising `build.sh IdealCVP` wrapper.

Historical research notes remain in `research_*.md`; the paper and sources
remain in `../paper/`. Old prompts or audit records using `Hardness/` refer to
the current `IdealCVP/` paths. Scratch smoke tests are not library entry points.
