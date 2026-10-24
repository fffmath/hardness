# Rank2ModuleSVP — SVP on rank-2 cyclotomic modules

Lean 4 formalisation (in progress) of

> Jiaqi Liu, Yansong Feng, Yanbin Pan. **SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules.**
> arXiv:2609.01469 (IACR ePrint 2026/1856). PDF: `paper/2609.01469.pdf`, LaTeX source: `paper/src/`.

Main theorem: for primes q ≡ 3 (mod 4), decision-SVP (ℓ₂, canonical embedding) on full-rank free
rank-2 submodules of ℤ[ζ_q]² is NP-complete under deterministic polynomial-time many-one
reductions from X3C. See `specs/PLAN.md` for the proof outline and the phased plan,
`NOTES.md` for the paper ↔ Lean map and `specs/STATUS.md` for progress.

Modules: `Rank2ModuleSVP.*` (root `Rank2ModuleSVP.lean` at the repo root); it imports the
shared `IdealCVP` infrastructure.
