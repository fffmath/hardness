import Rank2ModuleSVP.Reduction
import Rank2ModuleSVP.ReductionMap
import Rank2ModuleSVP.ReductionMapPoly
import Rank2ModuleSVP.MembershipCert

/-! Paper v2 Theorem 1.1: semantic correctness of the total reduction and
NP-completeness of rank-2 module SVP, given only `WanPowerSumEstimates`. -/

namespace Rank2ModuleSVP
noncomputable section
open IdealCVP Turing.MultiTapeTM Cslib.Complexity
open ReductionMap

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Absolute cutoffs; the extra eighth power also dominates the cubic offsets. -/
def mainK0 : ℕ := max redK0 1
def mainC0 : ℕ := max redC0 8

theorem mainK0_ge_redK0 : redK0 ≤ mainK0 := le_max_left _ _
theorem mainC0_ge_redC0 : redC0 ≤ mainC0 := le_max_left _ _
theorem mainK0_pos : 1 ≤ mainK0 := le_max_right _ _
theorem mainC0_pos : 1 ≤ mainC0 := by
  have : 8 ≤ mainC0 := le_max_right _ _
  omega

/-- Cubic Sidon positions satisfy (16) once the order exceeds `(2*k)^8`.
The premise `I.q ≤ I.n` follows from the absence of zero rows. -/
theorem main_cubic_offsets (I : X3CInstance) {k q : ℕ}
    (hk : 1 ≤ k) (hn : I.n ≤ k) (hM : I.q ≤ I.n)
    (hq : (2*k)^8 ≤ q) :
    4*Checker.tau I (SidonPositions.cubic I.n)*(3*I.q) < q := by
  have ha : Checker.alphaStar I (SidonPositions.cubic I.n) ≤ 3*I.n^3+I.n :=
    ((SidonPositions.cubic I.n).bound _).trans (SidonPositions.cubic_size I.n)
  have hn3 : I.n^3 ≤ k^3 := Nat.pow_le_pow_left hn 3
  have hk3 : k ≤ k^3 := Nat.le_self_pow (by norm_num) k
  have hk3pos : 1 ≤ k^3 := by
    have : 0 < k^3 := pow_pos (by omega) _
    omega
  have ht : Checker.tau I (SidonPositions.cubic I.n) ≤ 9*k^3 := by
    unfold Checker.tau
    omega
  have hMk : I.q ≤ k := hM.trans hn
  have hb : 4*Checker.tau I (SidonPositions.cubic I.n)*(3*I.q) ≤ 108*k^4 := by
    calc
      _ ≤ 4*(9*k^3)*(3*k) := by gcongr
      _ = _ := by ring
  have hk48 : k^4 ≤ k^8 := Nat.pow_le_pow_right hk (by norm_num)
  calc
    _ ≤ 108*k^4 := hb
    _ < 256*k^4 := Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ ≤ 256*k^8 := Nat.mul_le_mul_left _ hk48
    _ = (2*k)^8 := by ring
    _ ≤ q := hq

private theorem main_coreInput_m₁ (q : ℕ) [NeZero q] (I : X3CInstance)
    (s : SidonPositions I.n) (k : ℕ) :
    powerPair (q := q) (coreInput q I s k).m₁ = redM1 I s k := by
  simpa only [redM1, cntH_eq_sepWeight] using coreInput_m₁ q I s k

private theorem main_coreInput_m₂ (q : ℕ) [NeZero q] (I : X3CInstance)
    (s : SidonPositions I.n) (k : ℕ) :
    powerPair (q := q) (coreInput q I s k).m₂ = redM2 I s k := by
  simpa only [redM2, cntH_eq_sepWeight, Nat.cast_mul, redGamma, mapGamma]
    using coreInput_m₂ q I s k

private theorem main_coreInput_S (q : ℕ) [NeZero q] (I : X3CInstance)
    (s : SidonPositions I.n) (k : ℕ) :
    (coreInput q I s k).threshold = redS (q := q) I k := by
  simpa only [redS, redF, cntH_eq_sepWeight, redGamma, mapGamma]
    using coreInput_S q I s k

/-- The integral output satisfies all input promises, including the determinant
and the nonnegative threshold. Nonzero-row coverage supplies the latter premise. -/
theorem main_coreInput_wellFormed (q : ℕ) [NeZero q] [Fact q.Prime]
    (I : X3CInstance) (s : SidonPositions I.n) {k : ℕ}
    (hodd : q ≠ 2) (hk : redK0 ≤ k) (hpow : (2*k)^redC0 ≤ q)
    (hrows : 3*I.q ≤ Checker.W I) : (coreInput q I s k).WellFormed := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := coreInput_lengths q I s k
  refine ⟨(show q.Prime from Fact.out), hodd, h₁, h₂, h₃, h₄, ?_, ?_⟩
  · change determinant (powerPair (q := q) (coreInput q I s k).m₁)
      (powerPair (q := q) (coreInput q I s k).m₂) ≠ 0
    rw [main_coreInput_m₁, main_coreInput_m₂]
    exact redDet_ne_zero I s hk hpow
  · rw [main_coreInput_S]
    exact redS_nonneg I hk hpow hrows

/-- Theorem 5.2 interpreted in the actual power-basis list language. -/
theorem main_coreInput_correct (hWan : WanPowerSumEstimates)
    (q : ℕ) [NeZero q] [Fact q.Prime] (I : X3CInstance)
    (s : SidonPositions I.n) {k : ℕ} (hodd : q ≠ 2)
    (hk : redK0 ≤ k) (hpow : (2*k)^redC0 ≤ q)
    (hn : I.n+2 ≤ Nat.sqrt k) (hoff : 4*Checker.tau I s*(3*I.q) < q)
    (hrows : 3*I.q ≤ Checker.W I) :
    I.HasExactCover ↔ coreInput q I s k ∈ ModuleSVPLang := by
  have hw := main_coreInput_wellFormed q I s hodd hk hpow hrows
  have he : I.HasExactCover ↔
      SVPYes (powerPair (q := q) (coreInput q I s k).m₁)
        (powerPair (q := q) (coreInput q I s k).m₂) (coreInput q I s k).threshold := by
    rw [main_coreInput_m₁, main_coreInput_m₂, main_coreInput_S]
    exact exact_X3C_encoding I s hWan hk hpow hn hoff
  constructor
  · intro hi
    exact ⟨hw, he.mp hi⟩
  · rintro ⟨_, hi⟩
    exact he.mpr hi

/-- Every output meets the problem's promises, including outputs of all three
preprocessing branches. The cutoffs may be enlarged independently. -/
theorem reductionMap_wellFormed_of_constants (K0 C0 : ℕ)
    (hK : redK0 ≤ K0) (hC : redC0 ≤ C0) (hC1 : 1 ≤ C0) (x : X3CList) :
    (reductionMap K0 C0 x).WellFormed := by
  by_cases hw : x.WellFormed
  · by_cases hM : x.1 = 0
    · rw [reductionMap_empty K0 C0 x hw hM]
      exact fixed_outputs_wellFormed.1
    · by_cases hz : hasZeroRow x = true
      · rw [reductionMap_zeroRow K0 C0 x hw hM hz]
        exact fixed_outputs_wellFormed.2
      · have hMpos : 0 < x.1 := by omega
        have hs := mapQ_spec K0 C0 x hC1
        have : Fact (mapQ K0 C0 x).Prime := ⟨hs.1⟩
        have hr := red_regime_mono hK hC (mapK_bounds K0 x).1 hs.2.2.1
        have hf := main_coreInput_wellFormed (mapQ K0 C0 x)
          (mapInstance x hw hMpos hz) (SidonPositions.cubic x.2.length)
          hs.2.1 hr.1 hr.2 (Checker.rows_le_incidence_count _
            (mapInstance_cover x hw hMpos hz))
        simpa only [reductionMap, dite_eq_left hw, dite_eq_right hM,
          dite_eq_right hz, mapInstance, X3CList.toInstance] using hf
  · rw [reductionMap_malformed K0 C0 x hw]
    exact fixed_outputs_wellFormed.2

/-- Paper v2 §5.4: every output is a valid odd-prime rank-two SVP input. -/
theorem reductionMap_wellFormed (x : X3CList) :
    (ReductionMap.reductionMap mainK0 mainC0 x).WellFormed :=
  reductionMap_wellFormed_of_constants mainK0 mainC0
    mainK0_ge_redK0 mainC0_ge_redC0 mainC0_pos x

/-- Total correctness is monotone in both absolute cutoffs. -/
theorem reductionMap_correct_of_constants (hWan : WanPowerSumEstimates)
    (K0 C0 : ℕ) (hK : redK0 ≤ K0) (hC : redC0 ≤ C0) (hC8 : 8 ≤ C0)
    (x : X3CList) :
    x ∈ X3CLang ↔ reductionMap K0 C0 x ∈ ModuleSVPLang := by
  by_cases hw : x.WellFormed
  · by_cases hM : x.1 = 0
    · exact reductionMap_empty_correct K0 C0 x hw hM
    · by_cases hz : hasZeroRow x = true
      · exact reductionMap_zeroRow_correct K0 C0 x hw hM hz
      · have hMpos : 0 < x.1 := by omega
        let I := mapInstance x hw hMpos hz
        let k := mapK K0 x
        let q := mapQ K0 C0 x
        have hspec := mapQ_spec K0 C0 x (by omega)
        have : Fact q.Prime := ⟨hspec.1⟩
        have hk := mapK_bounds K0 x
        have hr := red_regime_mono hK hC hk.1 hspec.2.2.1
        have hn : I.n+2 ≤ Nat.sqrt k := Nat.le_sqrt'.mpr hk.2.1
        have hnk : I.n ≤ k := by
          have hsq : (I.n+2)^2 ≤ k := hk.2.1
          nlinarith
        have hq8 : (2*k)^8 ≤ q :=
          (Nat.pow_le_pow_right (by have := hk.2.2; omega) hC8).trans hspec.2.2.1
        have hoff := main_cubic_offsets I (by have := hk.2.2; omega) hnk
          (mapM_le_n x hw hMpos hz) hq8
        have hrows := Checker.rows_le_incidence_count I
          (mapInstance_cover x hw hMpos hz)
        have he := (x3cList_mem_iff x hw hMpos (nonempty_of_no_zeroRow x hMpos hz)).trans
          (main_coreInput_correct hWan q I (SidonPositions.cubic I.n)
            hspec.2.1 hr.1 hr.2 hn hoff hrows)
        simpa only [reductionMap, dite_eq_left hw, dite_eq_right hM,
          dite_eq_right hz] using he
  · exact reductionMap_malformed_correct K0 C0 x hw

/-- Paper v2 §5.4: the executable total map preserves YES and NO instances. -/
theorem reductionMap_correct (hWan : WanPowerSumEstimates) (x : X3CList) :
    x ∈ X3CLang ↔ ReductionMap.reductionMap mainK0 mainC0 x ∈ ModuleSVPLang :=
  reductionMap_correct_of_constants hWan mainK0 mainC0
    mainK0_ge_redK0 mainC0_ge_redC0 (le_max_right _ _) x

/-- Paper v2 Theorem 1.1, with the time certificate supplied by the map module. -/
theorem moduleSVP_npComplete_of_polytime (hWan : WanPowerSumEstimates)
    (hpoly : ComputableTidilyInPolyTime (ReductionMap.reductionMap mainK0 mainC0)
      IdealCVP.encX3C encSVP) : NPComplete encSVP ModuleSVPLang := by
  refine ⟨moduleSVP_mem_NP, IdealCVP.x3c_npHard.trans ?_⟩
  exact ⟨ReductionMap.reductionMap mainK0 mainC0, hpoly, reductionMap_correct hWan⟩

/-- **Paper v2 Theorem 1.1.** Decision-SVP on rank-2 modules over `ℤ[ζ_q]` (q odd prime) is
NP-complete, assuming only the named point-count estimate `WanPowerSumEstimates`. -/
theorem moduleSVP_npComplete_of (hWan : WanPowerSumEstimates) :
    NPComplete encSVP ModuleSVPLang :=
  moduleSVP_npComplete_of_polytime hWan (reductionMap_polytime mainK0 mainC0)

/-- X3C many-one reduces to rank-2 module SVP in polynomial time (given `WanPowerSumEstimates`). -/
theorem x3c_polyTimeReducible_moduleSVP (hWan : WanPowerSumEstimates) :
    PolyTimeReducible IdealCVP.encX3C encSVP IdealCVP.X3CLang ModuleSVPLang :=
  reductionMap_polyTimeReducible_of_correct mainK0 mainC0 (reductionMap_correct hWan)

end
end Rank2ModuleSVP
