import Power2IdealSVP.Spin.Guard
import Power2IdealSVP.Spin.Shifts
import Power2IdealSVP.Spin.ShortArc
import Power2IdealSVP.Spin.Geometry

/-!
# Cutting a guarded support at its long circular gap

Pairwise allowed cyclic distances place the support on a short integer arc. A signed monomial
shift moves that arc into `[0,R0]`; its wrapping signs are retained by coefficient multiplication.

Paper: `paper/power2-ideal-svp.txt`, Section 1.3; audit Section 7.
-/

namespace Power2IdealSVP.Spin

open Power2ModuleSVP (Coeff)
open IdealCVP.Cyclotomic

/-- Pairwise allowed circular distances allow a signed shift into the short coefficient arc. -/
theorem exists_signed_shift_short_support {D : Finset ℕ} {A0 : ℕ}
    (hD : DValid D A0) {σ : Coeff (n A0)} (hs : (support σ).Nonempty)
    (hpair : ∀ i ∈ support σ, ∀ j ∈ support σ, i ≠ j →
      cyclicDistance i j ∈ Eplus D) :
    ∃ e : Fin (n A0), ∀ x ∈ (support (mul (monomial e 1) σ)).image
      (fun i => (i.val : ℤ)), 0 ≤ x ∧ x ≤ R0 A0 := by
  classical
  have hn := n_pos A0
  let : NeZero (n A0) := ⟨by omega⟩
  let W : Finset ℤ := (support σ).image fun i => (i.val : ℤ)
  have hW : W.Nonempty := hs.image _
  have hclose : ∀ x ∈ W, ∀ y ∈ W, ∃ k : ℤ,
      |x - y + k * (n A0 : ℤ)| ≤ R0 A0 := by
    intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    by_cases hij : i = j
    · subst j
      exact ⟨0, by simp⟩
    · apply circular_min_close ⟨by omega, by exact_mod_cast i.isLt⟩
        ⟨by omega, by exact_mod_cast j.isLt⟩
      exact (Eplus_bounds hD (hpair i hi j hj hij)).2
  have hsep := separation_lt_n A0
  obtain ⟨t, ht⟩ := short_arc_integer hW (by omega : (0 : ℤ) ≤ R0 A0)
    (by omega : 3 * (R0 A0 : ℤ) < n A0) hclose
  let e : Fin (n A0) := ⟨((-t) % n A0).toNat, by
    exact (Int.toNat_lt (Int.emod_nonneg _ (by omega))).mpr
      (Int.emod_lt_of_pos _ (by omega))⟩
  have he : (e.val : ℤ) = (-t) % n A0 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  refine ⟨e, ?_⟩
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
  rw [support_monomial_mul] at hr
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨k, hklo, hkhi⟩ := ht j.val (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hnorm : ((j.val : ℤ) - t) % n A0 = j.val + k * n A0 - t := by
    calc
      _ = (((j.val : ℤ) - t) + k * n A0) % n A0 :=
        (Int.add_mul_emod_self_right _ _ _).symm
      _ = _ := by
        rw [show (j.val : ℤ) - t + k * n A0 = j.val + k * n A0 - t by ring]
        exact Int.emod_eq_of_lt (by omega) (by omega)
  have hadd : ((e.val : ℤ) + j.val) % n A0 = ((j.val : ℤ) - t) % n A0 := by
    rw [he]
    simp [Int.sub_eq_add_neg, Int.add_emod, Int.add_comm]
  have hval : ((e + j).val : ℤ) = ((e.val : ℤ) + j.val) % n A0 := by
    simp only [Fin.val_add, Int.natCast_emod, Nat.cast_add]
  rw [hval, hadd, hnorm]
  omega

/-- After cutting a passing support, its ordinary positive differences are allowed distances. -/
theorem short_support_positiveDifferences {D : Finset ℕ} {A0 h : ℕ} (hh : 0 < h)
    {σ : Coeff (n A0)} (hσ : Ternary σ)
    (hf : ∀ i ∈ support σ, tau D A0 h ≤ fieldAt (G D A0 h) σ i)
    (hshort : ∀ x ∈ (support σ).image (fun i => (i.val : ℤ)), x ≤ R0 A0) :
    PositiveDifferences (Eplus D) ((support σ).image fun i => (i.val : ℤ)) := by
  intro x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  have hjbound := hshort j.val (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hsep := separation_lt_n A0
  have hcast : ((((j.val : ℤ) - i.val).toNat : ℕ) : ℤ) = j.val - i.val :=
    Int.toNat_of_nonneg (by omega)
  apply guard_lift_pair_allowed hh hσ hf (by omega) (by omega) (x := i.val)
  · simpa only [lift_coe] using (mem_support σ i).mp hi
  · have heq : (i.val : ℤ) + ((j.val : ℤ) - i.val).toNat = j.val := by omega
    rw [heq, lift_coe]
    exact (mem_support σ j).mp hj

end Power2IdealSVP.Spin
