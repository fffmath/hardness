# Principal cyclotomic CVP reduction

Lean 4 / Mathlib formalization of the masked Boolean-system and X3C reduction
in `paper/src/chapter/principal-ideal.tex`.

Build from this directory with `lake build`. Import `Hardness`.

Main entry points: `Hardness.x3cToCVP`, `Hardness.x3c_correct`,
`Hardness.x3c_yes_gap`, `Hardness.x3c_no_gap`, and
`Hardness.exactCoverEquivClosest`.

See [NOTES.md](NOTES.md) for the theorem-to-paper mapping, the explicit cubic
Sidon variant, size bounds, and scope of the formalization.
