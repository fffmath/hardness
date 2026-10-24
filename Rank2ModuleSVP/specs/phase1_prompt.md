You are working in /workspace/hardness (Lean 4 v4.36.0-rc1 + Mathlib + complexitylib @ ba134c18
under .lake/packages). Do NOT run `lake update`/`lake exe cache get`, do not edit lake-manifest /
toolchain, do not use git. The lakefile already has two libs: `IdealCVP` (finished, do not break it)
and `Rank2ModuleSVP` (new, root file `/workspace/hardness/Rank2ModuleSVP.lean`, modules go in
`/workspace/hardness/Rank2ModuleSVP/*.lean` with module names `Rank2ModuleSVP.*`, namespace
`Rank2ModuleSVP`). Builds: `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 2400 lake build Rank2ModuleSVP`
and single files `LAKE_CACHE_DIR=/tmp/hardness-lake-cache timeout 900 lake env lean <file>`.
No `sorry` in finished code, no `axiom`, no `native_decide`. Deep results that the paper itself only
cites may be packaged as named hypotheses (`def Foo : Prop := ...`) passed as explicit arguments —
never as axioms — and only the three listed in specs/PLAN.md.

READ FIRST: Rank2ModuleSVP/specs/PLAN.md, and the paper source
Rank2ModuleSVP/paper/src/chapter/{pre,descent,representative,reduction}.tex (main.tex for macros).
Reuse IdealCVP infrastructure by importing it (do not copy): IdealCVP/Lattice.lean (sqNorm etc.),
IdealCVP/X3C.lean, IdealCVP/Sidon.lean (Erdős–Turán Sidon positions), IdealCVP/Complexity/X3CList.lean
(`X3CLang`, `encX3C`), IdealCVP/Complexity/SatToX3C.lean (`x3c_npComplete`), and the NP-certificate
machinery IdealCVP/{CertificateBound,Certificates,IntegerPreimage}.lean and
IdealCVP/Complexity/{Verifier,Witness,CertificateBits,GeneralModule}.lean. Skim IdealCVP/NOTES.md.

ROUND 1 GOALS (paper §2 and §3.1; do in order, build + log in Rank2ModuleSVP/NOTES.md after each):

1. `Rank2ModuleSVP/PrimeCyclotomic.lean`: model of O_K = ℤ[ζ_q] for prime q via q-coordinate
   vectors `ZMod q → ℤ` (and ℚ where needed) with cyclic convolution (ℤ[X]/(X^q−1)); element
   equality in O_K = difference is a constant vector (kernel of evaluation is (Φ_q)). Define the
   canonical form ⟨x,y⟩ = q·Σ x_a y_a − (Σx)(Σy) and norm; prove it is invariant under adding
   constants, nonneg, = Σ_{a<b}(z_a−z_b)², zero iff constant; conjugation a ↦ −a; multiplication
   by ±ζ^j is an isometry. Choose a clean API (structure or quotient) — it must later support
   module vectors (pairs), ideals π^k O_K, and elements of K with denominators (U, V).
2. Lemma `sparse-tools` (i): ‖v‖² < q²/4 ⇒ integral representative with ≤ 2‖v‖²/q nonzero coords;
   Lemma `second-shell`: nonzero w is ±ζ^j (norm q−1) or ‖w‖² ≥ 2q−4. (Roots of unity in the model
   = ±(monomial) up to constants.)
3. Lemma `sparse-tools` (ii): nonzero s-term polynomial over ZMod q with distinct exponents < q has
   order of vanishing at 1 at most s−1 (Hasse derivatives / Vandermonde-binomial determinant; Mathlib
   has `Polynomial.hasseDeriv`, `rootMultiplicity`).
4. Gauss sum (q ≡ 3 mod 4): ϑ = Σ χ(a) ζ^a with χ = quadratic character; conj ϑ = −ϑ, ϑ·conj ϑ = q,
   ϑ² = −q in the model (Mathlib: `quadraticChar`, `gaussSum_sq`, ... may help, or prove directly).
5. Problem statement `Rank2ModuleSVP/Problem.lean`: input type (q, m₁=(m₁₁,m₁₂), m₂, S) with
   power-basis integer coefficient lists, an injective `List Bool` encoding usable with complexitylib
   (`NP`, `NPComplete`, `PolyTimeReducible`; copy the style of IdealCVP/Complexity/GeneralModule.lean),
   WellFormed (q prime, q % 4 = 3, lengths q−1, det m₁₁m₂₂−m₁₂m₂₁ ≠ 0 in O_K, S ≥ 0), and the
   language: ∃ z w ∈ O_K, z m₁ + w m₂ ≠ 0 with norm ≤ S. (State only; membership is a later round
   unless it falls out cheaply from IdealCVP certificate bounds — attempt it if time remains.)
6. Stretch (paper §3.1): lifted Reed–Solomon lattice L_{q,k}, Thm `cyclotomic-descent`
   ({[z] : z ∈ L_{q,k}} = π^k O_K, iso on 1^⊥), Lemma `coset-syndrome`, Lemma `binary-shell`.
   Try to PROVE Bennett–Peikert λ₁(L_{q,k})² ≥ 2k (1 ≤ k ≤ q/2); if it resists, isolate it as
   `BennettPeikertMinimum` and record precisely why.

Keep every finished file building and imported from Rank2ModuleSVP.lean. Write Rank2ModuleSVP/NOTES.md
mapping paper labels → Lean names ("Round 1" section) and list any named hypotheses. At the end run
`#print axioms` (scratch file in /tmp) on every new main theorem: only propext, Classical.choice,
Quot.sound allowed. Finish with a full `lake build` (both libs) passing.
