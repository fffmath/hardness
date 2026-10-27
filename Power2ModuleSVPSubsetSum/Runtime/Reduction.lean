import Power2ModuleSVPSubsetSum.Runtime.Primitives
import Power2ModuleSVPSubsetSum.Reduction.Map

/-!
# Native polynomial-time certificate for the Subset Sum reduction

Certify the actual coefficient-list gadget and its total source normalization.
The degree and all loop indices are unary; weights, scales, and coefficients are binary.

Paper: `paper/power2svp-subsetsum.pdf`, Section 4.1, equations (4.1)–(4.3).
-/

namespace Power2ModuleSVPSubsetSum
open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace Reduction

/-- The binary Subset Sum encoding used by complexitylib. -/
abbrev encSource := encPair (encList encNat) encNat

private theorem gadget_m_eq (x : List ℕ × ℕ) :
    (gadget x.1 x.2).m =
    halfDegree x.1.length := rfl

private theorem gadget_DK_eq (x : List ℕ × ℕ) :
    (gadget x.1 x.2).DK =
    IdealCVP.negacyclicMul (2 * (gadget x.1 x.2).m)
      (filterD (gadget x.1 x.2).m) (filterK (gadget x.1 x.2).m) := rfl

private theorem gadget_H_eq (x : List ℕ × ℕ) :
    (gadget x.1 x.2).H =
    IdealCVP.negacyclicMul (2 * (gadget x.1 x.2).m)
      (filterDStar (gadget x.1 x.2).m) (weights (2 * (gadget x.1 x.2).m) x.1) := rfl

private theorem gadget_V_eq (x : List ℕ × ℕ) :
    (gadget x.1 x.2).V =
    scale (2 * (gadget x.1 x.2).m) (2 * (x.2 : ℤ) - (x.1.sum : ℤ))
      (filterDStar (gadget x.1 x.2).m) := rfl

private theorem gadget_u_eq (x : List ℕ × ℕ) :
    (gadget x.1 x.2).u =
    mask (2 * (gadget x.1 x.2).m) x.1.length := rfl

private theorem gadget_F_eq (x : List ℕ × ℕ) :
    (gadget x.1 x.2).F =
    listL1 (gadget x.1 x.2).H := rfl

private theorem gadget_nu_eq (x : List ℕ × ℕ) :
    (gadget x.1 x.2).nu =
    listL1 (gadget x.1 x.2).V := rfl

private theorem gadget_rho_eq (x : List ℕ × ℕ) :
    (gadget x.1 x.2).rho =
    listL1 (gadget x.1 x.2).DK := rfl

private theorem gadget_L_eq (x : List ℕ × ℕ) :
    (gadget x.1 x.2).L =
    (gadget x.1 x.2).F + (gadget x.1 x.2).nu + 1 := rfl

private theorem gadget_M_eq (x : List ℕ × ℕ) :
    (gadget x.1 x.2).M =
    2 * ((gadget x.1 x.2).L * (gadget x.1 x.2).rho + (gadget x.1 x.2).nu) +
      (gadget x.1 x.2).F + 1 := rfl

private theorem gadget_Q_eq (x : List ℕ × ℕ) :
    (gadget x.1 x.2).Q =
    IdealCVP.listAdd (2 * (gadget x.1 x.2).m)
      (scale (2 * (gadget x.1 x.2).m) ((gadget x.1 x.2).M : ℤ)
        (filterD (gadget x.1 x.2).m))
      (scale (2 * (gadget x.1 x.2).m) ((gadget x.1 x.2).L : ℤ)
        (gadget x.1 x.2).DK) := rfl

-- Keep certificate composition from unfolding the entire executable record.
attribute [local irreducible] gadget

/-- The half-degree depends only on the unary length of the weight list. -/
@[fun_prop] theorem gadget_m_polytime : ComputableTidilyInPolyTime
    (fun x : List ℕ × ℕ => (gadget x.1 x.2).m) encSource encUnary := by
  simp_rw [gadget_m_eq]
  unfold encSource
  fun_prop

/-- Computing the negacyclic rigidity filter uses polynomial time. -/
@[fun_prop] theorem gadget_DK_polytime : ComputableTidilyInPolyTime
    (fun x : List ℕ × ℕ => (gadget x.1 x.2).DK) encSource (encList encIntBin) := by
  simp_rw [gadget_DK_eq]
  exact IdealCVP.poly_negacyclicMul.comp
    ((unary_mul.comp ((const 2).prod gadget_m_polytime)).prod
      ((filterD_polytime.comp gadget_m_polytime).prod
        (filterK_polytime.comp gadget_m_polytime)))

/-- Computing the Laurent weight column uses binary coefficient arithmetic. -/
@[fun_prop] theorem gadget_H_polytime : ComputableTidilyInPolyTime
    (fun x : List ℕ × ℕ => (gadget x.1 x.2).H) encSource (encList encIntBin) := by
  simp_rw [gadget_H_eq]
  exact IdealCVP.poly_negacyclicMul.comp
    ((unary_mul.comp ((const 2).prod gadget_m_polytime)).prod
      ((filterDStar_polytime.comp gadget_m_polytime).prod
        (weights_polytime.comp
          ((unary_mul.comp ((const 2).prod gadget_m_polytime)).prod
            (fst (encList encNat) encNat)))))

/-- Computing the target-dependent column uses a binary sum and scalar product. -/
@[fun_prop] theorem gadget_V_polytime : ComputableTidilyInPolyTime
    (fun x : List ℕ × ℕ => (gadget x.1 x.2).V) encSource (encList encIntBin) := by
  simp_rw [gadget_V_eq]
  have hE : ComputableTidilyInPolyTime
      (fun x : List ℕ × ℕ => 2 * (x.2 : ℤ) - (x.1.sum : ℤ)) encSource encIntBin := by
    unfold encSource
    fun_prop
  exact scale_polytime.comp
    ((unary_mul.comp ((const 2).prod gadget_m_polytime)).prod
      (hE.prod (filterDStar_polytime.comp gadget_m_polytime)))

/-- The Boolean mask traverses the unary output degree. -/
@[fun_prop] theorem gadget_u_polytime : ComputableTidilyInPolyTime
    (fun x : List ℕ × ℕ => (gadget x.1 x.2).u) encSource (encList encIntBin) := by
  simp_rw [gadget_u_eq]
  exact mask_polytime.comp
    ((unary_mul.comp ((const 2).prod gadget_m_polytime)).prod
      (by unfold encSource; fun_prop))

/-- The exact l1 norm of the weight column is polynomial-time computable in binary. -/
@[fun_prop] theorem gadget_F_polytime : ComputableTidilyInPolyTime
    (fun x : List ℕ × ℕ => (gadget x.1 x.2).F) encSource encNat := by
  simp_rw [gadget_F_eq]
  exact listL1_polytime.comp gadget_H_polytime

/-- The exact l1 norm of the target column is polynomial-time computable in binary. -/
@[fun_prop] theorem gadget_nu_polytime : ComputableTidilyInPolyTime
    (fun x : List ℕ × ℕ => (gadget x.1 x.2).nu) encSource encNat := by
  simp_rw [gadget_nu_eq]
  exact listL1_polytime.comp gadget_V_polytime

/-- The rigidity scale uses the exact l1 norm, including on empty source lists. -/
@[fun_prop] theorem gadget_rho_polytime : ComputableTidilyInPolyTime
    (fun x : List ℕ × ℕ => (gadget x.1 x.2).rho) encSource encNat := by
  simp_rw [gadget_rho_eq]
  exact listL1_polytime.comp gadget_DK_polytime

/-- The first scale is assembled by binary arithmetic on certified norms. -/
@[fun_prop] theorem gadget_L_polytime : ComputableTidilyInPolyTime
    (fun x : List ℕ × ℕ => (gadget x.1 x.2).L) encSource encNat := by
  simp_rw [gadget_L_eq]
  exact binary_add.comp
    ((binary_add.comp (gadget_F_polytime.prod gadget_nu_polytime)).prod (const 1))

/-- The radius is assembled by binary arithmetic on certified norms. -/
@[fun_prop] theorem gadget_M_polytime : ComputableTidilyInPolyTime
    (fun x : List ℕ × ℕ => (gadget x.1 x.2).M) encSource encNat := by
  simp_rw [gadget_M_eq]
  exact binary_add.comp
    ((binary_add.comp
      ((binary_mul.comp ((const 2).prod
        (binary_add.comp
          ((binary_mul.comp (gadget_L_polytime.prod gadget_rho_polytime)).prod
            gadget_nu_polytime)))).prod gadget_F_polytime)).prod (const 1))

/-- The final rigidity polynomial is computed by list scaling and addition. -/
@[fun_prop] theorem gadget_Q_polytime : ComputableTidilyInPolyTime
    (fun x : List ℕ × ℕ => (gadget x.1 x.2).Q) encSource (encList encIntBin) := by
  simp_rw [gadget_Q_eq]
  have hn := unary_mul.comp ((const 2).prod gadget_m_polytime)
  exact IdealCVP.poly_listAdd.comp
    (hn.prod
      ((scale_polytime.comp
        (hn.prod ((intBin_natCast.comp gadget_M_polytime).prod
          (filterD_polytime.comp gadget_m_polytime)))).prod
        (scale_polytime.comp
          (hn.prod ((intBin_natCast.comp gadget_L_polytime).prod gadget_DK_polytime)))))

/-- Both generator columns and the binary radius have a native TM certificate. -/
@[fun_prop] theorem positiveReduce_polytime : ComputableTidilyInPolyTime
    (fun x : List ℕ × ℕ => positiveReduce x.1 x.2) encSource encSVP := by
  unfold positiveReduce
  dsimp only
  unfold encSVP IdealCVP.encPairRingArgs
  fun_prop

end Reduction

/-- Removing zeros is a polynomial-time filter on the binary input list. -/
@[fun_prop] theorem positiveWeights_polytime : ComputableTidilyInPolyTime
    positiveWeights (encList encNat) (encList encNat) := by
  unfold positiveWeights
  apply filter
  exact bool_not.comp (beq (id' (encIn := encNat)) (const 0))

/-- The total paper-A reduction has a native polynomial-time multitape TM certificate. -/
@[fun_prop] theorem reduce_polytime : ComputableTidilyInPolyTime reduce
    (encPair (encList encNat) encNat) encSVP := by
  unfold reduce
  have h := Reduction.positiveReduce_polytime
  unfold Reduction.encSource at h
  fun_prop

end Power2ModuleSVPSubsetSum
