import Power2ModuleSVPSubsetSum.Algebra.Norms
import Power2ModuleSVPSubsetSum.Rigidity.Filter

/-!
# Exact multiplier-filter parameters

The exact l1-based parameters and elementary scale-separation inequalities used in
Proposition 3.3. In particular `rho` is the actual norm of `DK`.

Paper: `paper/power2svp-subsetsum.pdf`, Proposition 3.3.
-/

namespace Power2ModuleSVPSubsetSum.Rigidity
open Power2ModuleSVP IdealCVP.Cyclotomic

/-- Exact coefficient l1 norm of `H`. -/
def F {n : ℕ} (H : Coeff n) : ℕ := coeffL1 H

/-- Exact coefficient l1 norm of `V`. -/
def nu {n : ℕ} (V : Coeff n) : ℕ := coeffL1 V

/-- Exact coefficient l1 norm of `DK`. -/
def rho (m : ℕ) : ℕ := coeffL1 (mul (D m) (K m))

/-- Secondary scale, larger than the sum of the two input norms. -/
def L {n : ℕ} (H V : Coeff n) : ℕ := F H + nu V + 1

/-- Main scale, with the unit slack needed for integer separation. -/
def M {m : ℕ} (H V : Coeff (2 * m)) : ℕ :=
  2 * (L H V * rho m + nu V) + F H + 1

/-- The multiplier filter polynomial. -/
def Q {m : ℕ} (H V : Coeff (2 * m)) : Coeff (2 * m) :=
  (M H V : ℤ) • D m + (L H V : ℤ) • mul (D m) (K m)

/-- The main scale is positive. -/
theorem M_pos {m : ℕ} (H V : Coeff (2 * m)) : 0 < M H V := by
  unfold M
  omega

/-- The distinguished coefficient of the multiplier filter is exactly `M`. -/
theorem Q_zero {m : ℕ} (hm : 0 < m) (H V : Coeff (2 * m)) :
    Q H V ⟨0, by omega⟩ = (M H V : ℤ) := by
  simp only [Q, Pi.add_apply, Pi.smul_apply, smul_eq_mul, DK_zero hm]
  simp [D, atom, show (0 : ℕ) ≠ m by omega]

/-- The filter plus error polynomial is nonzero, by its positive constant coefficient. -/
theorem Q_add_V_ne_zero {m : ℕ} (hm : 0 < m) (H V : Coeff (2 * m)) :
    Q H V + V ≠ 0 := by
  intro h
  have hi := congrFun h ⟨0, by omega⟩
  simp only [Pi.add_apply, Q_zero hm, Pi.zero_apply] at hi
  have hV : |V ⟨0, by omega⟩| ≤ (nu V : ℤ) := by
    change |V ⟨0, by omega⟩| ≤ (coeffL1 V : ℤ)
    rw [← Int.natCast_natAbs]
    exact_mod_cast (natAbs_le_coeffSup V ⟨0, by omega⟩).trans (coeffSup_le_coeffL1 V)
  have hM : (nu V : ℤ) < (M H V : ℤ) := by
    exact_mod_cast (show nu V < M H V from by unfold M; omega)
  have := abs_le.mp hV
  omega

/-- The first crude norm estimate already forces opposite-pair mass at most one. -/
theorem mass_le_one (F nu rho L M t : ℕ)
    (hM : M = 2 * (L * rho + nu) + F + 1)
    (ht : M * t ≤ M + F + (L * rho + nu) * t) : t ≤ 1 := by
  by_contra h
  have ht2 : 2 ≤ t := by omega
  have hc : 0 < M - (L * rho + nu) := by omega
  have hb : (M - (L * rho + nu)) * t ≤ M + F := by
    have he : M = (M - (L * rho + nu)) + (L * rho + nu) := by omega
    rw [he, Nat.add_mul] at ht
    omega
  have hl := Nat.mul_le_mul_left (M - (L * rho + nu)) ht2
  omega

/-- The crude norm estimate forces the filtered multiplier into the unit cube. -/
theorem filter_mass_le_one {m : ℕ} (hm : 0 < m) (H V b z : Coeff (2 * m))
    (hz : coeffSup z ≤ 1)
    (hshort : coeffSup (mul H z - mul (Q H V + V) b) ≤ M H V) :
    coeffSup (mul (D m) b) ≤ 1 := by
  let t := coeffSup (mul (D m) b)
  let R := mul H z - mul (Q H V + V) b
  have hb : coeffSup b ≤ t := coeffSup_le_D_mul hm b
  have hHz : coeffSup (mul H z) ≤ F H := by
    exact (coeffSup_mul_le H z).trans (by simpa [F] using Nat.mul_le_mul_left (coeffL1 H) hz)
  have hDK : coeffSup (mul (mul (D m) (K m)) b) ≤ rho m * t := by
    exact (coeffSup_mul_le _ b).trans (Nat.mul_le_mul_left _ hb)
  have hV : coeffSup (mul V b) ≤ nu V * t := by
    exact (coeffSup_mul_le V b).trans (Nat.mul_le_mul_left _ hb)
  have hL : coeffSup ((L H V : ℤ) • mul (mul (D m) (K m)) b) ≤
      L H V * (rho m * t) := by
    rw [coeffSup_smul]
    simpa using Nat.mul_le_mul_left (L H V) hDK
  have he : (M H V : ℤ) • mul (D m) b =
      mul H z - R - (L H V : ℤ) • mul (mul (D m) (K m)) b - mul V b := by
    dsimp only [R]
    simp only [Q, mul_add_left, mul_smul_left]
    abel
  have ht : M H V * t ≤ M H V + F H + (L H V * rho m + nu V) * t := by
    calc
      _ = coeffSup ((M H V : ℤ) • mul (D m) b) := by
        rw [coeffSup_smul]
        simp [t]
      _ = coeffSup (mul H z - R -
          (L H V : ℤ) • mul (mul (D m) (K m)) b - mul V b) := congrArg coeffSup he
      _ ≤ coeffSup (mul H z - R -
          (L H V : ℤ) • mul (mul (D m) (K m)) b) + coeffSup (mul V b) :=
        coeffSup_sub_le _ _
      _ ≤ (coeffSup (mul H z - R) +
          coeffSup ((L H V : ℤ) • mul (mul (D m) (K m)) b)) +
          coeffSup (mul V b) := Nat.add_le_add_right (coeffSup_sub_le _ _) _
      _ ≤ ((coeffSup (mul H z) + coeffSup R) +
          coeffSup ((L H V : ℤ) • mul (mul (D m) (K m)) b)) +
          coeffSup (mul V b) := Nat.add_le_add_right
            (Nat.add_le_add_right (coeffSup_sub_le _ _) _) _
      _ ≤ ((F H + M H V) + L H V * (rho m * t)) + nu V * t :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hHz hshort) hL) hV
      _ = _ := by ring
  exact mass_le_one (F H) (nu V) (rho m) (L H V) (M H V) t rfl ht

/-- A saturated coordinate forces the skew correction to point inwards. -/
theorem saturated_coordinate (M L : ℕ) (r v e : ℤ)
    (hr : |r| ≤ 1) (he : |e| < (L : ℤ))
    (h : |(M : ℤ) * r + (L : ℤ) * v + e| ≤ (M : ℤ)) : r * v ≤ 0 := by
  have hr' := abs_le.mp hr
  have he' := abs_lt.mp he
  have h' := abs_le.mp h
  have hL : 0 < (L : ℤ) := lt_of_le_of_lt (abs_nonneg e) he
  have hcases : r = -1 ∨ r = 0 ∨ r = 1 := by omega
  rcases hcases with hr | hr | hr
  · subst r
    simp only [mul_neg_one, neg_one_mul] at *
    by_contra hv
    have hv' : v ≤ -1 := by omega
    nlinarith
  · simp [hr]
  · subst r
    simp only [mul_one, one_mul] at *
    by_contra hv
    have hv' : 1 ≤ v := by omega
    nlinarith

end Power2ModuleSVPSubsetSum.Rigidity
