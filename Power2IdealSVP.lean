import Power2IdealSVP.Algebra.IdealBasic
import Power2IdealSVP.Algebra.SpinBasic
import Power2IdealSVP.Glue.Correctness
import Power2IdealSVP.Glue.Distances
import Power2IdealSVP.Glue.Ideal
import Power2IdealSVP.Glue.Source
import Power2IdealSVP.Glue.Spin
import Power2IdealSVP.Glue.Theta
import Power2IdealSVP.Ideal.Construction
import Power2IdealSVP.Ideal.FullSigns
import Power2IdealSVP.Ideal.Minimum
import Power2IdealSVP.Ideal.Parity
import Power2IdealSVP.Ideal.Theta
import Power2IdealSVP.Ideal.Walls
import Power2IdealSVP.Main
import Power2IdealSVP.Membership.Certificates
import Power2IdealSVP.Membership.NP
import Power2IdealSVP.Membership.PolyTime
import Power2IdealSVP.Membership.Verifier
import Power2IdealSVP.Problem
import Power2IdealSVP.Runtime.Construction
import Power2IdealSVP.Runtime.Graph
import Power2IdealSVP.Runtime.PolyTime
import Power2IdealSVP.Runtime.Structure
import Power2IdealSVP.Source.Extraction
import Power2IdealSVP.Source.Labels
import Power2IdealSVP.Source.RowColumn
import Power2IdealSVP.Source.ThreeTerm
import Power2IdealSVP.Spin.Classification
import Power2IdealSVP.Spin.Converse
import Power2IdealSVP.Spin.Defs
import Power2IdealSVP.Spin.Equivalence
import Power2IdealSVP.Spin.Geometry
import Power2IdealSVP.Spin.Guard
import Power2IdealSVP.Spin.Interaction
import Power2IdealSVP.Spin.Normalization
import Power2IdealSVP.Spin.Parameters
import Power2IdealSVP.Spin.Runs
import Power2IdealSVP.Spin.Shifts
import Power2IdealSVP.Spin.ShortArc
import Power2IdealSVP.Spin.Support

/-!
# Power-of-two principal ideal SVP

Import every module of the CLIQUE reduction to coefficient infinity-norm SVP on principal
ideals of `ℤ[X]/(X^n + 1)`, including unconditional NP-completeness in `Power2IdealSVP.Main`.

Paper: `Power2IdealSVP/paper/power2-ideal-svp.txt`, Theorem 1 and equations (1)–(3).
-/
