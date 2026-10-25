import Power2ModuleSVP.FlatFrontend.Parameters
import Power2ModuleSVP.Seed.RudinShapiro.Bounds

/-!
# Words

List implementation of the Rudin--Shapiro words. Polynomial and complex
objects occur only in the specification and proofs.

Paper: `paper/power2svp.pdf`, Appendices A.1–A.3 (the executable sampling grid and frontend).
-/
namespace Power2ModuleSVP
namespace FlatFrontend

def rsWords : ℕ → List ℤ × List ℤ
  | 0 => ([1], [1])
  | k + 1 =>
    let p := rsWords k
    (p.1 ++ p.2, p.1 ++ p.2.map Neg.neg)

theorem rsWords_length (k : ℕ) :
    (rsWords k).1.length = 2 ^ k ∧ (rsWords k).2.length = 2 ^ k := by
  induction k with
  | zero => simp [rsWords]
  | succ k ih => simp [rsWords, ih, pow_succ, Nat.mul_two]

theorem rsWords_coeff (k j : ℕ) :
    (rsWords k).1.getD j 0 = (rudinShapiroP k).coeff j ∧
    (rsWords k).2.getD j 0 = (rudinShapiroQ k).coeff j := by
  induction k generalizing j with
  | zero => cases j <;> simp [rsWords, Polynomial.coeff_one]
  | succ k ih =>
    have hl := rsWords_length k
    simp only [rsWords, rudinShapiroP_succ, rudinShapiroQ_succ,
      Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul',
      List.getD_eq_getElem?_getD, List.getElem?_append, hl.1]
    by_cases hj : j < 2 ^ k
    · simp only [hj, ↓reduceIte, show ¬ 2 ^ k ≤ j by omega, add_zero, sub_zero]
      exact ⟨(ih j).1, (ih j).1⟩
    · have htail := (rudinShapiro_coefficients k).2 j (by omega)
      simp only [hj, ↓reduceIte, show 2 ^ k ≤ j by omega, htail.1,
        zero_add, zero_sub, List.getElem?_map]
      constructor
      · exact (ih _).2
      · have hm (o : Option ℤ) : (o.map Neg.neg).getD 0 = -(o.getD 0) := by
          cases o <;> simp
        rw [hm]
        exact congrArg Neg.neg (ih _).2

def stablePrefix (m : ℕ) : List ℤ :=
  ((rsWords (Nat.log2 m + 1)).1).take m

theorem prefix_capacity (m : ℕ) : m ≤ 2 ^ (Nat.log2 m + 1) := by
  by_cases hm : m = 0
  · simp [hm]
  · simpa [Nat.log2_eq_log_two] using
      (Nat.lt_pow_succ_log_self (b := 2) (by omega) m).le

theorem stablePrefix_length (m : ℕ) : (stablePrefix m).length = m := by
  simp [stablePrefix, (rsWords_length _).1, Nat.min_eq_left (prefix_capacity m)]

theorem stablePrefix_coeff {m j : ℕ} (hj : j < m) :
    (stablePrefix m).getD j 0 = rudinShapiroCoefficient j := by
  have hcap : j < 2 ^ (Nat.log2 m + 1) := hj.trans_le (prefix_capacity m)
  rw [rudinShapiroCoefficient_eq hcap, ← (rsWords_coeff _ j).1]
  simp [stablePrefix, List.getD_eq_getElem?_getD, hj]

theorem stablePrefix_sign {m j : ℕ} (hj : j < m) :
    (stablePrefix m).getD j 0 = -1 ∨ (stablePrefix m).getD j 0 = 1 := by
  rw [stablePrefix_coeff hj]
  exact rudinShapiroCoefficient_sign j

/-- A nonzero entry selects a cosine pair; the other frequencies use the
stable sine word. Indices in these two words start with frequency two. -/
def cosineCoefficient (N j : ℕ) : ℤ :=
  let t := stage N
  let T := blockShift N
  if T ≤ j ∧ j < T + 2 ^ t then (rsWords t).1.getD (j - T) 0
  else if 2 * T ≤ j ∧ j < 2 * T + 2 ^ t then (rsWords t).2.getD (j - 2 * T) 0
  else 0

def cosineSelected (N j : ℕ) : Bool :=
  let T := blockShift N
  let m := 2 ^ stage N
  (T ≤ j && j < T + m) || (2 * T ≤ j && j < 2 * T + m)

def background (d : ℕ) : List ℤ :=
  let N := seedN d
  let p := stablePrefix (N + 1)
  (List.range d).map fun i =>
    if i = 2 * N then 1
    else if i < 4 * N + 1 ∧ i % 2 = 0 then
      let j := if i < 2 * N then (2 * N - i) / 2 else (i - 2 * N) / 2
      if cosineSelected N j then cosineCoefficient N j
      else if i < 2 * N then -(p.getD j 1) else p.getD j 1
    else 1

@[simp] theorem background_length (d : ℕ) : (background d).length = d := by
  simp [background]

end FlatFrontend
end Power2ModuleSVP
