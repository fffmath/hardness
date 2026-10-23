import Complexity.Computability.Complexity.Problems.ExactThreeSAT

/-! Smoke test: the pinned complexitylib (cslib-community/complexitylib @ ba134c18)
imports cleanly from this non-module project. -/
open Cslib.Complexity

example : NPComplete encCNF ExactThreeSAT := ExactThreeSAT_npComplete
