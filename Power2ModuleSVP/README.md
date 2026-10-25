# Power2ModuleSVP — rank-2 module SVP in power-of-two cyclotomic rings

Lean 4 formalisation of

> **Rank-Two Module SVP in Power-of-Two Cyclotomic Rings** (`paper/power2svp.pdf`;
> companion with a sharper auxiliary degree bound: `paper/degree-refinement.pdf`).

Main theorem: for power-of-two d and R_d = ℤ[X]/(X^d+1), deciding whether a rank-2 module
G·R_d² (G nonsingular, coefficient embedding, ℓ∞ norm) contains a nonzero vector of norm at most 1
is NP-complete under deterministic polynomial-time many-one reductions; the principal-coset
version (does h + gR_D meet the unit cube?) is NP-complete as well.

## Main Lean results (namespace `Power2ModuleSVP`, root `Power2ModuleSVP.lean`)

| Result | Lean name | File |
| --- | --- | --- |
| NP membership | `coset_mem_NP`, `moduleSVP_mem_NP` | `Membership.lean` |
| Coset problem NP-complete | `coset_npComplete : NPComplete encCoset CosetLang` | `Main.lean` |
| Module SVP from a rigid anchor family | `moduleSVP_npComplete_of` | `Main.lean` |
| Spectral seed ⇒ rigid anchor (repair) | `rigidAnchorFamily_of_seed`, `moduleSVP_npComplete_of_seed` | `AnchorRepairPoly2.lean` |
| **Main theorem** | `moduleSVP_npComplete : NPComplete encSVP ModuleSVPLang` | `MainFinal.lean` |

Both main theorems are **unconditional**: no `sorry`, no extra axioms, no `native_decide`;
`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

Proof route: 3SAT → positive exactly-one triples at Sidon positions → sparse affine bit equations →
principal coset (parity blocks, reciprocal resultant, divided derivative) → rank-2 homogenisation
with a rigid Littlewood anchor built deterministically (flat seed via Rudin–Shapiro / Chebyshev /
Bernstein, rational-grid coloring, exact conditional expectations, repair), including native
multi-tape TM polynomial-time certificates for every construction step.

`specs/` holds the plan, status log and four audit reports (paper edge cases noted in AUDIT3/4).
Shared infrastructure (lattice norms, Sidon sets, 3SAT reductions, encodings) is imported from
`IdealCVP` and `Rank2ModuleSVP`.
