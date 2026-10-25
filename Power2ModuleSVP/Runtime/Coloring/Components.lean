import Power2ModuleSVP.Runtime.Coloring.Initialization
import Power2ModuleSVP.Runtime.Coloring.ProjectorStage
import Power2ModuleSVP.Runtime.Coloring.OutputBounds

/-!
# Native coloring components

Collect square-root and rational initialization certificates, projector-stage evaluation, common
denominators, and full-coloring output bounds. The complete native certificate is assembled in
Runtime/Coloring/Certificate.lean.

Paper: `paper/power2svp.pdf`, Appendix B (Lemma 11 and Theorem 6, rational deterministic
coloring).
-/
