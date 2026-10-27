import Power2IdealSVP.Glue.Ideal
import Power2IdealSVP.Glue.Distances

/-!
# Executable parameters and the sparse-spin construction

The coefficient arrays computed by the list program are exactly the signed monomials and
integer amplitudes in the sparse-spin proof, including the doubled antipodal guard term.

Paper: `paper/power2-ideal-svp.txt`, Sections 1.2–1.4, equation (1).
-/

namespace Power2IdealSVP.Glue

open Cslib.Complexity Power2ModuleSVP IdealCVP.Cyclotomic

attribute [local irreducible] Runtime.guardCoeff Runtime.interactionCoeff
  Runtime.interactionCoeffs Runtime.interactionNorm Runtime.neighborAmplitude
  Runtime.spinThreshold Runtime.guardAmplitude Runtime.spinCoeffs

/-- The runtime and mathematical geometric bounds coincide. -/
theorem windowBound_eq (x : Graph × ℕ) :
    Runtime.windowBound x = Spin.R0 (Runtime.maxLabel x) := rfl

/-- Both degree formulas select the least power of two above the same separation bound. -/
theorem degree_eq_spin (x : Graph × ℕ) :
    Runtime.degree x = Spin.n (Runtime.maxLabel x) := by
  apply Nat.le_antisymm
  · exact Runtime.degree_le_pow (by
      simpa only [windowBound_eq, Spin.n] using Spin.separation_lt_n (Runtime.maxLabel x))
  · obtain ⟨k, hk⟩ := Runtime.degree_dyadic x
    rw [hk]
    exact Spin.n_le_of_lt_pow _ k (by
      simpa only [windowBound_eq, hk] using Runtime.degree_gt x)

/-- Boolean membership in the allowed-distance list agrees with the finite-set windows. -/
theorem allowedDistance_iff (x : Graph × ℕ) (d : ℕ) :
    Runtime.allowedDistance x d = true ↔ d ∈ Spin.Eplus (spinDistances x) := by
  rw [Runtime.allowedDistance_eq_true, Spin.mem_Eplus_iff]
  simp only [Spin.window, Finset.mem_insert, Finset.mem_singleton, spinDistances,
    List.mem_toFinset, Runtime.windowSpacing, Spin.Q]

/-- The sorted forbidden-distance enumerations agree, including their order. -/
theorem forbiddenDistances_eq (x : Graph × ℕ) :
    Runtime.forbiddenDistances x = Spin.forbiddenList (spinDistances x) (Runtime.maxLabel x) := by
  apply List.Pairwise.eq_of_mem_iff (Runtime.forbiddenDistances_increasing x)
    (Finset.sortedLT_sort _).pairwise
  · intro d
    rw [Runtime.mem_forbiddenDistances]
    simp only [Finset.mem_sort]
    rw [Spin.mem_forbidden_iff, degree_eq_spin]
    simp only [← allowedDistance_iff]
    cases Runtime.allowedDistance x d <;> simp
    omega

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Runtime.maxLabel Runtime.degree Spin.n Spin.R0
  Spin.T Spin.A Spin.C Spin.G Spin.L Spin.RT spinDistances

private theorem xpow_neg_of_lt {n e : ℕ} (he : 0 < e) (hen : e < n) :
    Spin.xpow n (-(e : ℤ)) = -monomial ⟨n - e, by omega⟩ 1 := by
  have hn : 0 < n := by omega
  have hx := Spin.xpow_add_degree hn (-(e : ℤ))
  have heq : -(e : ℤ) + (n : ℤ) = ((n - e : ℕ) : ℤ) := by omega
  rw [heq, Spin.xpow_of_lt (show n - e < n by omega)] at hx
  rw [← neg_inj] at hx
  simpa using hx.symm

private theorem symmetricCoeff_eq {n e : ℕ} (he : 0 < e) (hen : e < n)
    (i : Fin n) :
    Runtime.symmetricCoeff n e i.val =
      (Spin.xpow n e + Spin.xpow n (-(e : ℤ))) i := by
  rw [Spin.xpow_of_lt hen, xpow_neg_of_lt he hen]
  simp [Runtime.symmetricCoeff, monomial, Fin.ext_iff, eq_comm, sub_eq_add_neg]

private theorem skewCoeff_eq {n e : ℕ} (he : 0 < e) (hen : e < n)
    (i : Fin n) :
    ((if i.val = e then 1 else 0) + (if i.val = n - e then 1 else 0) : ℤ) =
      (Spin.xpow n e - Spin.xpow n (-(e : ℤ))) i := by
  rw [Spin.xpow_of_lt hen, xpow_neg_of_lt he hen]
  simp [monomial, Fin.ext_iff, eq_comm]

private theorem sum_zipIdx {α : Type*} (l : List α) (f : α × ℕ → ℤ) :
    (l.zipIdx.map f).sum = ∑ j : Fin l.length, f (l[j.val], j.val) := by
  have heq : l.zipIdx.map f = List.ofFn (fun j : Fin l.length => f (l[j.val], j.val)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp
  rw [heq, List.sum_ofFn]

/-- Every guard digit, including the antipodal double contribution, has the same coefficient. -/
theorem guardCoeff_eq (x : Graph × ℕ) (i : Fin (Spin.n (Runtime.maxLabel x))) :
    Runtime.guardCoeff x i.val = Spin.A (spinDistances x) (Runtime.maxLabel x) i := by
  rw [Runtime.guardCoeff, sum_zipIdx, forbiddenDistances_eq]
  unfold Spin.A
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hd := Spin.forbiddenAt_mem (spinDistances x) (Runtime.maxLabel x) j
  have hb := Spin.mem_forbidden_iff.mp hd
  have hn := Spin.n_pos (Runtime.maxLabel x)
  have he : Spin.forbiddenAt (spinDistances x) (Runtime.maxLabel x) j <
      Spin.n (Runtime.maxLabel x) := by omega
  rw [degree_eq_spin]
  change (5 : ℤ) ^ j.val * _ = (5 : ℤ) ^ j.val * _
  congr 1
  exact skewCoeff_eq (by omega) he i

/-- Every small-interaction coefficient agrees with the signed-monomial definition. -/
theorem interactionCoeff_eq (x : Graph × ℕ) (i : Fin (Spin.n (Runtime.maxLabel x))) :
    Runtime.interactionCoeff x i.val =
      Spin.T (spinDistances x) (Runtime.maxLabel x) i := by
  rw [Runtime.interactionCoeff, ← List.sum_toFinset _ (Runtime.diffSet_nodup x)]
  unfold Spin.T spinDistances
  simp only [Finset.sum_apply, Pi.add_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hb := spinDistances_valid x d (by simpa only [spinDistances] using hd)
  have hn := Spin.separation_lt_n (Runtime.maxLabel x)
  have he : 0 < Spin.Q * d := by simp only [Spin.Q]; omega
  have hen : Spin.Q * d + 2 < Spin.n (Runtime.maxLabel x) := by
    simp only [Spin.R0, Spin.Q] at hn ⊢
    omega
  rw [degree_eq_spin]
  change Runtime.symmetricCoeff _ (Spin.Q * d) i.val +
    Runtime.symmetricCoeff _ (Spin.Q * d + 2) i.val = _
  rw [symmetricCoeff_eq he (by omega), symmetricCoeff_eq (by omega) hen]
  simp only [Pi.add_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, neg_add]
  abel

/-- The entire endpoint-interaction list is the exact mathematical coefficient list. -/
theorem interactionCoeffs_eq_toList (x : Graph × ℕ) :
    Runtime.interactionCoeffs x =
      IdealCVP.toList (Spin.T (spinDistances x) (Runtime.maxLabel x)) := by
  apply List.ext_getElem
  · simp [Runtime.interactionCoeffs, IdealCVP.toList, degree_eq_spin]
  · intro i hi hi'
    have hn : i < Spin.n (Runtime.maxLabel x) := by simpa [IdealCVP.toList] using hi'
    simpa [Runtime.interactionCoeffs, IdealCVP.toList] using interactionCoeff_eq x ⟨i, hn⟩

/-- The exact runtime one-norm equals the spin interaction norm, with cancellations retained. -/
theorem interactionNorm_eq (x : Graph × ℕ) :
    (Runtime.interactionNorm x : ℤ) = Spin.RT (spinDistances x) (Runtime.maxLabel x) := by
  rw [Runtime.interactionNorm, interactionCoeffs_eq_toList, listNorm_toList]
  unfold Spin.RT Spin.coeffL1 Algebra.coeffL1
  rfl

/-- Nearest-neighbor amplitudes agree as integers. -/
theorem neighborAmplitude_eq (x : Graph × ℕ) :
    (Runtime.neighborAmplitude x : ℤ) = Spin.C (spinDistances x) (Runtime.maxLabel x) x.2 := by
  simp only [Runtime.neighborAmplitude, Nat.cast_add, Nat.cast_one,
    interactionNorm_eq, Spin.C]

/-- The runtime threshold is exactly the threshold of the sparse-spin equivalence. -/
theorem runtimeTau_eq (x : Graph × ℕ) :
    runtimeTau x = Spin.tau (spinDistances x) (Runtime.maxLabel x) x.2 := by
  have hb : 1 ≤ Runtime.neighborAmplitude x + x.2 := by
    unfold Runtime.neighborAmplitude
    omega
  simp only [runtimeTau, Runtime.spinThreshold, Nat.cast_sub hb, Nat.cast_add,
    Nat.cast_one, neighborAmplitude_eq, Spin.tau]

/-- Guard amplitudes agree as integers. -/
theorem guardAmplitude_eq (x : Graph × ℕ) :
    (Runtime.guardAmplitude x : ℤ) = Spin.L (spinDistances x) (Runtime.maxLabel x) x.2 := by
  have ht : (Runtime.spinThreshold x : ℤ) =
      Spin.tau (spinDistances x) (Runtime.maxLabel x) x.2 := runtimeTau_eq x
  simp only [Runtime.guardAmplitude, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, neighborAmplitude_eq, interactionNorm_eq, ht, Spin.L]

/-- The executable sparse-spin array is the exact list of the mathematical multiplier. -/
theorem spinCoeffs_eq_toList (x : Graph × ℕ) :
    Runtime.spinCoeffs x =
      IdealCVP.toList (Spin.G (spinDistances x) (Runtime.maxLabel x) x.2) := by
  apply List.ext_getElem
  · simp [Runtime.spinCoeffs, IdealCVP.toList, degree_eq_spin]
  · intro i hi hi'
    have hn : i < Spin.n (Runtime.maxLabel x) := by simpa [IdealCVP.toList] using hi'
    have h1 : 1 < Spin.n (Runtime.maxLabel x) := by
      have := Spin.separation_lt_n (Runtime.maxLabel x)
      omega
    simp only [Runtime.spinCoeffs, List.getElem_map, List.getElem_range, IdealCVP.toList,
      List.getElem_ofFn]
    rw [guardCoeff_eq x ⟨i, hn⟩, interactionCoeff_eq x ⟨i, hn⟩, degree_eq_spin,
      symmetricCoeff_eq (by decide : 0 < 1) h1 ⟨i, hn⟩,
      guardAmplitude_eq, neighborAmplitude_eq]
    simp only [Spin.G, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Nat.cast_one]

/-- Exact coefficient lists identify runtime and Spin multipliers across the degree equality. -/
theorem runtimeG_eq_toList (x : Graph × ℕ) :
    IdealCVP.toList (runtimeG x) =
      IdealCVP.toList (Spin.G (spinDistances x) (Runtime.maxLabel x) x.2) := by
  have roundtrip {n : ℕ} (a : List ℤ) (ha : a.length = n) :
      IdealCVP.toList (IdealCVP.ofList (d := n) a) = a := by
    subst n
    exact IdealCVP.toList_ofList a
  exact (roundtrip _ (by simp only [Runtime.spinCoeffs, List.length_map,
    List.length_range])).trans (spinCoeffs_eq_toList x)

end Power2IdealSVP.Glue
