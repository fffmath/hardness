# Director status log (hardness formalisation)

Times Asia/Shanghai (UTC+8).

## Done (pushed to master)
- 5e1ab6c / 976898f / f60dcd8 / 35f2352: paper, rounds 1–2, README.
- 461a745 round 3: general full rank, module-SIVP, fixed family.
- d4d28fa round 4: FixedIndexed, Rational, Canonical, Certificates, SizeBounds.
- 50b47f2 round 5: StrongBounds (T3), CVPP (T1), CertificateBound (T2), SearchToDecision (T8), Smoke.lean (#eval), research reports.
- af77627: complexitylib dependency pinned at ba134c18 (+ cslib 6ff325e8), Hardness/Complexity/Smoke.lean.

- (round 6 commit, see below): complexity layer M1–M3 + conditional headline.

## In flight
- Round 6 Codex (specs/phase6_prompt.md), started ~06:23, log /workspace/hardness_codex_r6.log,
  PID 867741, session 01a16adc-35fe-7be0-bd96-0b9a55f74ec0. Milestones M1 Problem/encodings, M2 ExactThreeSAT→MaskedSys (+polytime),
  M3 NP membership, M4 list compiler + bridge, M5 compiler polytime, M6 headline
  `principalCVP_npComplete`. Files so far: Hardness/Complexity/{ListRing,Problem,SatToMasked}.lean.

## Next step
- When round 6 ends: build (timeout 1500 lake build), sorry/axiom grep, #print axioms, commit+push,
  then write phase7 prompt continuing from NOTES.md's round-6 "missing" list.
- Stall rule: no log growth for ~30 min → kill and `codex exec resume <id>` with a nudge.
