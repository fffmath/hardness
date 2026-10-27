# hp2n-afinal complete

Integrated Corollary 4.4 documentation and exact signatures in README, NOTES, and STATUS.
Merged STATUS-hp2n-asearch2.md into STATUS.md and deleted the superseded note.
The root imports all 37 project modules with its module docstring after the imports.
Main/Search.Turing edits are comments and whitespace only; theorem statements are unchanged.
The root README lists all five subprojects. No files under Power2IdealSVP/ were changed.

Verification: locked build Power2ModuleSVPSubsetSum passed (7912 jobs); no project warnings.
Locked env lean /tmp/hp2n-afinal-check.lean passed: all three documented search signatures
elaborate; moduleSVP_npComplete and moduleSVP_search_turing_npHard use only propext,
Classical.choice, and Quot.sound. Root import coverage, changed Lean line limits, local
Markdown links, unchanged theorem/proof bodies, and git diff --check pass.
Logs: /tmp/hp2n-afinal-build.log and /tmp/hp2n-afinal-check.log.
No remaining work. Full integrated record: STATUS.md.
