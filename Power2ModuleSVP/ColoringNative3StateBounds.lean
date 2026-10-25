import Power2ModuleSVP.ColoringNative3Bounds

/-! Encoding bounds for every stopped-walk prefix, measured using the
fixed rows and the original starting point. -/
namespace Power2ModuleSVP.ColoringRuntime
open PartialColoringAlg ColoringNative
open Turing.MultiTapeTM
set_option maxHeartbeats 600000

def startWire {r m : ℕ} (a : Fin m → Row r) (x : Vec r) : WalkInput :=
  (walkParameter a, (List.ofFn x, []))

theorem startWire_dimensions {r m : ℕ} (a : Fin m → Row r) (x : Vec r) :
    r ≤ (encWalkInput (startWire a x)).length ∧
      m ≤ (encWalkInput (startWire a x)).length ∧
      (encWalkParameter (walkParameter a)).length ≤ (encWalkInput (startWire a x)).length ∧
      (encList encColoringRational (List.ofFn x)).length ≤ (encWalkInput (startWire a x)).length := by
  have hm := length_le_length_encList
    (encPair encColoringRational (encList encColoringRational))
    (List.ofFn fun i => ((a i).threshold, List.ofFn (a i).a))
  simp only [List.length_ofFn] at hm
  simp only [startWire, encWalkInput, encWalkParameter, walkParameter, encListState,
    encQuadraticRows, length_encPair, encUnary_apply, List.length_replicate, encList_nil]
  change m ≤ (encQuadraticRows (List.ofFn fun i => ((a i).threshold, List.ofFn (a i).a))).length at hm
  unfold encQuadraticRows at hm
  omega

theorem stepSize_den_size_le (r : ℕ) : (stepSize r).den.size ≤ 16 * r + 1 := by
  have he : stepSize r = ((16 * r : ℕ) : ℚ)⁻¹ := by simp [stepSize, one_div]
  rw [he, Rat.inv_natCast_den]
  split_ifs
  · simp
  · exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)

def coordinatePrefixBound (c d N : ℕ) : ℕ :=
  1 + N * N + 2048 * N ^ 3 * (16 * N + 1 + c * (N + 1) ^ d)

def weightPrefixBound (N : ℕ) : ℕ :=
  2 * (2048 * N ^ 3 + 1) + 1 + 2 * (1024 * N * (2048 * N ^ 3 + 1) + 2)

def statePrefixBound (c d N : ℕ) : ℕ :=
  2 * ((8 * coordinatePrefixBound c d N + 7) * N) +
    (4 * weightPrefixBound N + 7) * N + 1

/-- This bound covers every weight, coordinate, and list delimiter at
 every prefix; it does not rely on an entropy or progress promise. -/
theorem walk_initial_state_encoding_uniform
    (h : CanonicalProjectorDenominatorHypothesis) :
    ∃ c d : ℕ, ∀ (r m fuel : ℕ) (_hr : 0 < r) (a : Fin m → Row r),
      (∀ i, (a i).threshold ^ 2 ≤ 4 * (r : ℚ)) →
      (∀ i, dot (a i).a (a i).a ≤ 1) → fuel ≤ stepBudget r →
      ∀ x : Vec r, RationalCube x →
      (encListState (List.ofFn (walk a fuel (initialState a x)).x,
        List.ofFn (walk a fuel (initialState a x)).w)).length ≤
          c * ((encWalkInput (startWire a x)).length + 1) ^ d := by
  obtain ⟨c₀, d₀, hb⟩ := walk_initial_coordinate_bits_uniform h
  have hpoly : PolyBounded id (statePrefixBound c₀ d₀) := by
    refine ⟨statePrefixBound c₀ d₀, ?_, fun _ => le_rfl⟩
    unfold statePrefixBound coordinatePrefixBound weightPrefixBound
    fun_prop
  obtain ⟨c, d, hcd⟩ := hpoly.exists_le
  refine ⟨c, d, fun r m fuel hr a hl hn hf x hx => ?_⟩
  let N := (encWalkInput (startWire a x)).length
  obtain ⟨hrN, hmN, hpN, hxN⟩ := startWire_dimensions a x
  have hdenbits (j : Fin r) : (x j).den.size ≤ N := by
    have hq : (x j).den.size ≤ (encColoringRational (x j)).length := by
      simp only [encColoringRational, Function.Embedding.coeFn_mk, length_encPair,
        length_encIntBin, encNat_apply, Nat.size_eq_bits_len]
      omega
    exact hq.trans ((length_le_encList_of_mem encColoringRational
      (List.mem_ofFn.mpr ⟨j, rfl⟩)).trans hxN)
  have hD := vectorDen_size x hdenbits
  have hbudget : fuel ≤ 2048 * N ^ 3 := hf.trans (by unfold stepBudget; gcongr)
  have hcoord : ∀ j : Fin r, rationalBits ((walk a fuel (initialState a x)).x j) ≤
      2 * coordinatePrefixBound c₀ d₀ N := by
    intro j
    have hh := hb r m (vectorDen x) fuel hr a hl hn hf (vectorDen_pos x) x hx
      (vectorDen_commonDen x) j
    apply hh.trans
    apply Nat.mul_le_mul_left
    unfold coordinatePrefixBound
    calc
      _ ≤ (1 + r * N) + fuel * (16 * r + 1 + c₀ *
          ((encWalkParameter (walkParameter a)).length + 1) ^ d₀) := by
        gcongr
        exact stepSize_den_size_le r
      _ ≤ _ := by gcongr
  have hprec : precision r m ≤ 1024 * N * (2048 * N ^ 3 + 1) := by
    apply (Nat.size_le.mpr Nat.lt_two_pow_self).trans
    unfold stepBudget
    gcongr
  have hweight : ∀ i : Fin m, rationalBits ((walk a fuel (initialState a x)).w i) ≤
      weightPrefixBound N := by
    intro i
    have hw := walk_initial_weight_bits_le_raw hr a hl hn x hx fuel i
    exact hw.trans (by unfold weightPrefixBound; gcongr)
  have hxe := length_encList_le encColoringRational
    (List.ofFn (walk a fuel (initialState a x)).x)
    (b := 4 * coordinatePrefixBound c₀ d₀ N + 3) (by
      intro q hq
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
      exact (rational_encoding_le_bits _).trans (by have hh := hcoord j; omega))
  have hwe := length_encList_le encColoringRational
    (List.ofFn (walk a fuel (initialState a x)).w)
    (b := 2 * weightPrefixBound N + 3) (by
      intro q hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact (rational_encoding_le_bits _).trans (by have hh := hweight i; omega))
  simp only [List.length_ofFn] at hxe hwe
  apply le_trans (b := statePrefixBound c₀ d₀ N)
  · simp only [encListState, length_encPair]
    unfold statePrefixBound
    calc
      _ ≤ 2 * (r * (2 * (4 * coordinatePrefixBound c₀ d₀ N + 3) + 1)) +
          m * (2 * (2 * weightPrefixBound N + 3) + 1) + 1 := by omega
      _ ≤ _ := by nlinarith
  · exact hcd N

end Power2ModuleSVP.ColoringRuntime
