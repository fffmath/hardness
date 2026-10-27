import Power2IdealSVP.Algebra.SpinBasic

/-!
# Sparse-spin parameters and distance windows

The parameters depend on an arbitrary finite set of positive integer distances `D`, a bound
`A0`, and a target `h`. The power of two is the least one strictly above `8 * R0 + 16`.

Paper: `paper/power2-ideal-svp.pdf`, Sections 1.2–1.4; audit Sections 3 and 7.
-/
namespace Power2IdealSVP.Spin

open Power2ModuleSVP (Coeff Dyadic)

/-- The fixed spacing of the far-distance windows. -/
def Q : ℕ := 16

/-- A bound for every allowed positive distance. -/
def R0 (A0 : ℕ) : ℕ := Q * A0 + 2

/-- The least power of two strictly greater than `8 * R0 A0 + 16`. -/
def n (A0 : ℕ) : ℕ := 2 ^ (Nat.log 2 (8 * R0 A0 + 16) + 1)

/-- The four positive distances around a positive edge-difference center. -/
def window (d : ℕ) : Finset ℕ := {Q * d - 1, Q * d, Q * d + 1, Q * d + 2}

/-- Allowed positive cyclic distances. Reflection introduces no extra positive offsets. -/
def Eplus (D : Finset ℕ) : Finset ℕ := {1, 2} ∪ D.biUnion window

/-- The hypotheses on an abstract source difference set. -/
def DValid (D : Finset ℕ) (A0 : ℕ) : Prop := ∀ d ∈ D, 0 < d ∧ d ≤ A0

/-- Forbidden unsigned cyclic distances, including the antipodal distance. -/
def forbidden (D : Finset ℕ) (A0 : ℕ) : Finset ℕ :=
  Finset.Icc 1 (n A0 / 2) \ Eplus D

/-- A fixed increasing enumeration gives distinct base-five guard weights. -/
def forbiddenList (D : Finset ℕ) (A0 : ℕ) : List ℕ :=
  (forbidden D A0).sort (· ≤ ·)

/-- The distance assigned to a particular base-five guard digit. -/
def forbiddenAt (D : Finset ℕ) (A0 : ℕ)
    (j : Fin (forbiddenList D A0).length) : ℕ := (forbiddenList D A0)[j.val]

/-- The skew guard, using the increasing forbidden-distance enumeration. -/
def A (D : Finset ℕ) (A0 : ℕ) : Coeff (n A0) :=
  ∑ j : Fin (forbiddenList D A0).length,
    (5 : ℤ) ^ j.val •
      (xpow (n A0) (forbiddenAt D A0 j) - xpow (n A0) (-(forbiddenAt D A0 j : ℤ)))

/-- The self-adjoint small interaction, with its two offsets at each positive center. -/
def T (D : Finset ℕ) (A0 : ℕ) : Coeff (n A0) :=
  ∑ d ∈ D,
    (xpow (n A0) (Q * d) + xpow (n A0) (-(Q * d : ℤ)) +
      xpow (n A0) (Q * d + 2) + xpow (n A0) (-(Q * d + 2 : ℤ)))

/-- The coefficient one-norm of the small interaction. -/
def RT (D : Finset ℕ) (A0 : ℕ) : ℤ := coeffL1 (T D A0)

/-- The nearest-neighbor amplitude. -/
def C (D : Finset ℕ) (A0 h : ℕ) : ℤ := RT D A0 + h + 1

/-- The active-field acceptance threshold. -/
def tau (D : Finset ℕ) (A0 h : ℕ) : ℤ := C D A0 h + h - 1

/-- The guard amplitude, dominating every small-field contribution. -/
def L (D : Finset ℕ) (A0 h : ℕ) : ℤ :=
  2 * C D A0 h + RT D A0 + tau D A0 h + 1

/-- The multiplier used in the sparse-spin decision equivalence. -/
def G (D : Finset ℕ) (A0 h : ℕ) : Coeff (n A0) :=
  L D A0 h • A D A0 - C D A0 h • (xpow (n A0) 1 + xpow (n A0) (-1)) + T D A0

/-- The chosen dimension belongs to the fixed power-of-two ring family. -/
theorem n_dyadic (A0 : ℕ) : Dyadic (n A0) := ⟨_, rfl⟩

/-- The dimension strictly exceeds the paper's separation bound. -/
theorem separation_lt_n (A0 : ℕ) : 8 * R0 A0 + 16 < n A0 :=
  Nat.lt_pow_succ_log_self (by decide) _

/-- Positivity of the chosen dimension. -/
theorem n_pos (A0 : ℕ) : 0 < n A0 := (n_dyadic A0).pos

/-- Dyadic rounding increases the requested size by a factor of at most two. -/
theorem n_le_twice (A0 : ℕ) : n A0 ≤ 2 * (8 * R0 A0 + 16) := by
  have hb : 8 * R0 A0 + 16 ≠ 0 := by omega
  have hp := Nat.pow_log_le_self 2 hb
  simpa [n, pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left 2 hp

/-- No smaller power of two strictly exceeds the requested size. -/
theorem n_le_of_lt_pow (A0 k : ℕ) (hk : 8 * R0 A0 + 16 < 2 ^ k) : n A0 ≤ 2 ^ k := by
  have hb : 0 < 8 * R0 A0 + 16 := by omega
  have hlog : Nat.log 2 (8 * R0 A0 + 16) < k := by
    by_contra h
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.le_of_not_gt h)
    have hq := Nat.pow_log_le_self 2 (Nat.ne_of_gt hb)
    omega
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Elementary interval description of a far window. -/
theorem mem_window_iff {d e : ℕ} : e ∈ window d ↔ Q * d - 1 ≤ e ∧ e ≤ Q * d + 2 := by
  simp only [window, Finset.mem_insert, Finset.mem_singleton, Q]
  omega

/-- Every allowed distance is near, or belongs to one specified positive far window. -/
theorem mem_Eplus_iff {D : Finset ℕ} {e : ℕ} :
    e ∈ Eplus D ↔ e = 1 ∨ e = 2 ∨ ∃ d ∈ D, e ∈ window d := by
  simp [Eplus]

/-- Allowed distances are positive and bounded by `R0`. -/
theorem Eplus_bounds {D : Finset ℕ} {A0 e : ℕ} (hD : DValid D A0)
    (he : e ∈ Eplus D) : 0 < e ∧ e ≤ R0 A0 := by
  rcases mem_Eplus_iff.mp he with rfl | rfl | ⟨d, hd, he⟩
  · simp [R0]
  · simp [R0]
  · have hd' := hD d hd
    have he' := mem_window_iff.mp he
    simp only [Q] at he'
    dsimp [R0, Q]
    omega

/-- The distance three is forbidden: the first far window begins at fifteen. -/
theorem three_not_mem_Eplus {D : Finset ℕ} {A0 : ℕ} (hD : DValid D A0) :
    3 ∉ Eplus D := by
  intro he
  rcases mem_Eplus_iff.mp he with h | h | ⟨d, hd, he⟩
  · omega
  · omega
  · have hd' := (hD d hd).1
    have he' := mem_window_iff.mp he
    simp only [Q] at he'
    omega

/-- Two distinct far windows have at least twelve missing integers between them. -/
theorem windows_separated {d e : ℕ} (hde : d < e) : Q * d + 2 + 12 < Q * e - 1 := by
  simp only [Q]
  omega

/-- Nearby far-window members must have the same center. -/
theorem window_center_eq_of_close {d e x y : ℕ} (hx : x ∈ window d)
    (hy : y ∈ window e) (hxy : x ≤ y + 12) (hyx : y ≤ x + 12) : d = e := by
  have hx' := mem_window_iff.mp hx
  have hy' := mem_window_iff.mp hy
  simp only [Q] at hx' hy'
  omega

/-- Above the two near distances, allowed membership supplies a positive far window. -/
theorem far_mem_Eplus_iff {D : Finset ℕ} {e : ℕ} (he : 2 < e) :
    e ∈ Eplus D ↔ ∃ d ∈ D, e ∈ window d := by
  rw [mem_Eplus_iff]
  constructor
  · rintro (h | h | h)
    · omega
    · omega
    · exact h
  · exact fun h => Or.inr (Or.inr h)

/-- Four consecutive far distances occupy exactly one entire four-point window. -/
theorem four_consecutive_window {D : Finset ℕ} {e : ℕ} (he : 2 < e)
    (hfirst : e ∈ Eplus D) (hlast : e + 3 ∈ Eplus D) :
    ∃ d ∈ D, e = Q * d - 1 := by
  obtain ⟨d, hd, hde⟩ := (far_mem_Eplus_iff he).mp hfirst
  obtain ⟨d', hd', hd'e⟩ := (far_mem_Eplus_iff (show 2 < e + 3 by omega)).mp hlast
  have heq : d = d' := window_center_eq_of_close hde hd'e (by omega) (by omega)
  subst d'
  have h0 := mem_window_iff.mp hde
  have h3 := mem_window_iff.mp hd'e
  refine ⟨d, hd, ?_⟩
  simp only [Q] at h0 h3 ⊢
  omega

/-- Five consecutive allowed far distances cannot occur. -/
theorem no_five_consecutive {D : Finset ℕ} {e : ℕ} (he : 2 < e)
    (hfirst : e ∈ Eplus D) (hlast : e + 4 ∈ Eplus D) : False := by
  obtain ⟨d, hd, hde⟩ := (far_mem_Eplus_iff he).mp hfirst
  obtain ⟨d', hd', hd'e⟩ := (far_mem_Eplus_iff (show 2 < e + 4 by omega)).mp hlast
  have heq : d = d' := window_center_eq_of_close hde hd'e (by omega) (by omega)
  subst d'
  have h0 := mem_window_iff.mp hde
  have h4 := mem_window_iff.mp hd'e
  omega

/-- A positive multiple of `Q` is allowed exactly when its center belongs to `D`. -/
theorem mem_Eplus_center_iff {D : Finset ℕ} {m : ℕ} (hm : 0 < m) :
    Q * m ∈ Eplus D ↔ m ∈ D := by
  constructor
  · intro he
    have hb : 2 < Q * m := by dsimp [Q]; omega
    obtain ⟨d, hd, hdm⟩ := (far_mem_Eplus_iff hb).mp he
    have hw := mem_window_iff.mp hdm
    have hmd : m = d := by simp only [Q] at hw; omega
    simpa only [hmd] using hd
  · intro hmD
    exact mem_Eplus_iff.mpr (Or.inr (Or.inr ⟨m, hmD, by simp [window]⟩))

/-- Membership in the forbidden enumeration is exactly the unsigned range exclusion. -/
theorem mem_forbidden_iff {D : Finset ℕ} {A0 d : ℕ} :
    d ∈ forbidden D A0 ↔ 1 ≤ d ∧ d ≤ n A0 / 2 ∧ d ∉ Eplus D := by
  simp [forbidden, and_assoc]

/-- The antipodal distance is always forbidden. -/
theorem antipodal_mem_forbidden {D : Finset ℕ} {A0 : ℕ} (hD : DValid D A0) :
    n A0 / 2 ∈ forbidden D A0 := by
  have hn := separation_lt_n A0
  have hn' : R0 A0 < n A0 / 2 := by omega
  apply mem_forbidden_iff.mpr
  refine ⟨by omega, le_rfl, ?_⟩
  intro he
  have := (Eplus_bounds hD he).2
  omega

/-- The perturbation norm is nonnegative. -/
theorem RT_nonneg (D : Finset ℕ) (A0 : ℕ) : 0 ≤ RT D A0 := by
  unfold RT coeffL1
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The threshold exceeds the perturbation norm by exactly `2h`. -/
theorem tau_sub_RT (D : Finset ℕ) (A0 h : ℕ) :
    tau D A0 h - RT D A0 = 2 * h := by unfold tau C; ring

/-- The trimer center has two units of strict threshold margin. -/
theorem center_margin (D : Finset ℕ) (A0 h : ℕ) :
    2 * C D A0 h - RT D A0 = tau D A0 h + 2 := by unfold tau C; ring

/-- A negative integral guard field is strictly below threshold. -/
theorem guard_margin (D : Finset ℕ) (A0 h : ℕ) :
    -L D A0 h + 2 * C D A0 h + RT D A0 = -tau D A0 h - 1 := by unfold L; ring

/-- The nearest-neighbor amplitude is positive, including for an empty distance set. -/
theorem C_pos (D : Finset ℕ) (A0 h : ℕ) : 0 < C D A0 h := by
  have := RT_nonneg D A0
  unfold C
  positivity

/-- A positive target gives a positive threshold. -/
theorem tau_pos (D : Finset ℕ) (A0 : ℕ) {h : ℕ} (hh : 0 < h) :
    0 < tau D A0 h := by
  have := RT_nonneg D A0
  have := tau_sub_RT D A0 h
  omega

/-- The guard amplitude is positive. -/
theorem L_pos (D : Finset ℕ) (A0 h : ℕ) : 0 < L D A0 h := by
  have := RT_nonneg D A0
  unfold L tau C
  omega

/-- The sorted forbidden list has exactly the intended members. -/
theorem mem_forbiddenList_iff {D : Finset ℕ} {A0 d : ℕ} :
    d ∈ forbiddenList D A0 ↔ d ∈ forbidden D A0 := by simp [forbiddenList]

/-- Each enumerated guard digit corresponds to a forbidden unsigned cyclic distance. -/
theorem forbiddenAt_mem (D : Finset ℕ) (A0 : ℕ)
    (j : Fin (forbiddenList D A0).length) : forbiddenAt D A0 j ∈ forbidden D A0 := by
  apply mem_forbiddenList_iff.mp
  exact List.getElem_mem j.isLt

/-- Every forbidden distance appears as a guard digit. -/
theorem exists_forbiddenAt {D : Finset ℕ} {A0 d : ℕ} (hd : d ∈ forbidden D A0) :
    ∃ j : Fin (forbiddenList D A0).length, forbiddenAt D A0 j = d := by
  have hl := mem_forbiddenList_iff.mpr hd
  obtain ⟨j, hj, h⟩ := List.mem_iff_getElem.mp hl
  exact ⟨⟨j, hj⟩, h⟩

end Power2IdealSVP.Spin
