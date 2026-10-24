# Director status log (hardness formalisation)

Times Asia/Shanghai (UTC+8).

## Done (pushed to master)
- 5e1ab6c / 976898f / f60dcd8 / 35f2352: paper, rounds 1–2, README.
- 461a745 round 3: general full rank, module-SIVP, fixed family.
- d4d28fa round 4: FixedIndexed, Rational, Canonical, Certificates, SizeBounds.
- 50b47f2 round 5: StrongBounds (T3), CVPP (T1), CertificateBound (T2), SearchToDecision (T8), Smoke.lean (#eval), research reports.
- af77627: complexitylib dependency pinned at ba134c18 (+ cslib 6ff325e8), Hardness/Complexity/Smoke.lean.

- (round 6 commit, see below): complexity layer M1–M3 + conditional headline.

## Done (cont.)
- e9d0a61 round 6: Hardness/Complexity/* — PrincipalCVP ∈ NP (unconditional), ExactThreeSAT → MaskedSys NP-hard
  (unconditional), compileList correctness; principalCVP_npComplete conditional on
  hcompilePoly : ComputableTidilyInPolyTime compileList encMasked encCVP.

- (round 7 commit): compileFast (cubic Sidon, pure list code) + bridge + native polytime
  certificate poly_compileFast ⇒ principalCVP_npComplete : NPComplete encCVP PrincipalCVP
  UNCONDITIONAL (axioms: propext, Classical.choice, Quot.sound only). Conditional variant kept as
  principalCVP_npComplete_of_compilePoly.

## In flight
- Nothing. Headline landed; director loop stopped.

## Possible next steps (not started)
- X3C NP-completeness in complexitylib terms (3SAT → 3DM → X3C, polytime) to match the paper's source problem.
- Module-SIVP NP-hardness via the same list-compiler pattern; fixed-family CVPP ⇒ P/poly ⇒ PH = Σ₂
  (complexitylib has PPoly / Karp–Lipton).

## Round 8 (DONE)  — X3C NP-completeness + paper route + cyclic (if cheap)
- prompt: specs/phase8_prompt.md; log: /workspace/hardness_codex_r8.log
- session id: 01a16b2e-d23e-7772-80ec-39486b4e134d (resume with `codex exec resume <id> -c sandbox_mode='"workspace-write"' -`)
- Planned after: round 9 = Module-SIVP NPComplete (class level); round 10 = CVPP ⇒ NP ⊆ P/poly ⇒ PH = Σ₂.
- Result: x3c_npComplete (ExactThreeSAT→X3C, native polytime), principalCVP_npHard_via_X3C, principalCyclicCVP_npHard. Cyclic NP membership open. Axioms clean.
