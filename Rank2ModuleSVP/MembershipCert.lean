import Rank2ModuleSVP.Membership
import IdealCVP.IntegerPreimage

/-! Polynomial bit bounds for prime-cyclotomic module-SVP certificates. -/
noncomputable section
namespace Rank2ModuleSVP.Membership
open scoped BigOperators
open IdealCVP Turing.MultiTapeTM
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Multiplication in the power basis, after eliminating the last cyclic coefficient. -/
def powerMatrix (q : ℕ) (b : List ℤ) : Matrix (Fin (q-1)) (Fin (q-1)) ℤ :=
  fun r j => coeff q b ((r.val+q-j.val)%q) - coeff q b ((q-1+q-j.val)%q)

theorem cyclicCoeff_fin {q : ℕ} (hq : 0 < q) (a b : List ℤ) (r : ℕ) :
    cyclicCoeff q a b r = ∑ j : Fin (q-1), a.getD j.val 0 * coeff q b ((r+q-j.val)%q) := by
  unfold cyclicCoeff
  rw [list_sum_range, ← Nat.sub_add_cancel (show 1 ≤ q by omega), Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, coeff, lt_self_iff_false, ↓reduceIte, zero_mul, add_zero]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [j.isLt]

theorem powerMatrix_mulVec {q : ℕ} (hq : 0 < q) (a b : List ℤ) :
    (powerMatrix q b).mulVec (ofList a) = ofList (mul q a b) := by
  ext r
  simp only [Matrix.mulVec, dotProduct, powerMatrix, ofList, mul,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range,
    r.isLt, Option.map_some, Option.getD_some]
  rw [cyclicCoeff_fin hq, cyclicCoeff_fin hq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [List.getD_eq_getElem?_getD]
  ring

/-- Concatenate the two coordinate lists as a vector in the integral power basis. -/
def pairCoeffs (q : ℕ) (c : List ℤ × List ℤ) : Fin ((q-1)+(q-1)) → ℤ :=
  Fin.append (ofList c.1) (ofList c.2)

/-- The two generator columns expanded into `2(q-1)` integral columns. -/
def certificateMatrix (x : SVPInput) :
    Matrix (Fin ((x.q-1)+(x.q-1))) (Fin ((x.q-1)+(x.q-1))) ℤ :=
  fun i => Fin.addCases
    (fun r => Fin.append (powerMatrix x.q x.m₁.1 r) (powerMatrix x.q x.m₂.1 r))
    (fun r => Fin.append (powerMatrix x.q x.m₁.2 r) (powerMatrix x.q x.m₂.2 r)) i

theorem certificateMatrix_mulVec (x : SVPInput) (hq : 0 < x.q) (c : List ℤ × List ℤ) :
    (certificateMatrix x).mulVec (pairCoeffs x.q c) = pairCoeffs x.q (product x c) := by
  have hs (a b : List ℤ) (r : Fin (x.q-1)) :
      (∑ j, powerMatrix x.q b r j * ofList a j) = ofList (mul x.q a b) r :=
    congrFun (powerMatrix_mulVec hq a b) r
  ext i
  refine Fin.addCases (fun r => ?_) (fun r => ?_) i <;>
    simp only [Matrix.mulVec, dotProduct, certificateMatrix, pairCoeffs,
      Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_add,
      Fin.append_left, Fin.append_right, product, add, ofList_listAdd, Pi.add_apply] <;>
    rw [hs, hs]

/-- Recover two multiplier lists from an integral column vector. -/
def coefficientLists (q : ℕ) (u : Fin ((q-1)+(q-1)) → ℤ) : List ℤ × List ℤ :=
  (List.ofFn (fun i : Fin (q-1) => u (Fin.castAdd (q-1) i)),
   List.ofFn (fun i : Fin (q-1) => u (Fin.natAdd (q-1) i)))

@[simp] theorem ofList_ofFn {d : ℕ} (u : Fin d → ℤ) : ofList (List.ofFn u) = u := by
  ext i
  simp [ofList, List.getD_eq_getElem?_getD, i.isLt]

@[simp] theorem pairCoeffs_coefficientLists (q : ℕ) (u : Fin ((q-1)+(q-1)) → ℤ) :
    pairCoeffs q (coefficientLists q u) = u := by
  ext i
  refine Fin.addCases (fun r => ?_) (fun r => ?_) i <;>
    simp only [pairCoeffs, coefficientLists, ofList_ofFn,
      Fin.append_left, Fin.append_right]

theorem pairCoeffs_injective (q : ℕ) (a b : List ℤ × List ℤ)
    (ha : a.1.length = q-1 ∧ a.2.length = q-1)
    (hb : b.1.length = q-1 ∧ b.2.length = q-1)
    (h : pairCoeffs q a = pairCoeffs q b) : a = b := by
  have he (l k : List ℤ) (hl : l.length = q-1) (hk : k.length = q-1)
      (hh : ofList (d := q-1) l = ofList k) : l = k := by
    apply List.ext_getElem (hl.trans hk.symm)
    intro i hi hj
    have hi' : i < q-1 := by omega
    simpa [ofList, List.getD_eq_getElem, hi, hj] using congrFun hh ⟨i,hi'⟩
  apply Prod.ext
  · apply he _ _ ha.1 hb.1
    ext i
    simpa only [pairCoeffs, Fin.append_left] using congrFun h (Fin.castAdd (q-1) i)
  · apply he _ _ ha.2 hb.2
    ext i
    simpa only [pairCoeffs, Fin.append_right] using congrFun h (Fin.natAdd (q-1) i)

/-- Every framed input component is paid for by the complete encoding. -/
theorem input_length_bounds (x : SVPInput) :
    (encList encIntBin x.m₁.1).length ≤ (encSVP x).length ∧
    (encList encIntBin x.m₁.2).length ≤ (encSVP x).length ∧
    (encList encIntBin x.m₂.1).length ≤ (encSVP x).length ∧
    (encList encIntBin x.m₂.2).length ≤ (encSVP x).length ∧
    (encIntBin x.threshold).length ≤ (encSVP x).length := by
  simp only [SVPInput.m₁, SVPInput.m₂, SVPInput.threshold,
    encSVP, encModuleSIVP, length_encPair]
  omega

theorem coeff_abs_le_two_pow (q : ℕ) (a : List ℤ) (N : ℕ)
    (h : (encList encIntBin a).length ≤ N) (i : ℕ) :
    |coeff q a i| ≤ (2 : ℤ)^N := by
  unfold coeff
  split_ifs
  · exact getD_abs_le_two_pow a N h i
  · simp only [abs_zero]; positivity

theorem powerMatrix_entry_bound (q : ℕ) (a : List ℤ) (N : ℕ)
    (h : (encList encIntBin a).length ≤ N) (i j : Fin (q-1)) :
    |powerMatrix q a i j| ≤ (2 : ℤ)^(N+1) := by
  unfold powerMatrix
  have h₁ := coeff_abs_le_two_pow q a N h ((i.val+q-j.val)%q)
  have h₂ := coeff_abs_le_two_pow q a N h ((q-1+q-j.val)%q)
  calc
    _ ≤ |coeff q a ((i.val+q-j.val)%q)| + |coeff q a ((q-1+q-j.val)%q)| := abs_sub _ _
    _ ≤ 2^N + 2^N := add_le_add h₁ h₂
    _ = _ := by rw [pow_succ]; ring

theorem certificateMatrix_entry_bound (x : SVPInput) (i j) :
    |certificateMatrix x i j| ≤ (2 : ℤ)^((encSVP x).length+1) := by
  obtain ⟨h₁,h₂,h₃,h₄,_⟩ := input_length_bounds x
  refine Fin.addCases (fun r => ?_) (fun r => ?_) i <;>
    refine Fin.addCases (fun s => ?_) (fun s => ?_) j
  all_goals simp only [certificateMatrix, Fin.addCases_left, Fin.addCases_right,
    Fin.append_left, Fin.append_right]
  · exact powerMatrix_entry_bound x.q x.m₁.1 _ h₁ r s
  · exact powerMatrix_entry_bound x.q x.m₂.1 _ h₃ r s
  · exact powerMatrix_entry_bound x.q x.m₁.2 _ h₂ r s
  · exact powerMatrix_entry_bound x.q x.m₂.2 _ h₄ r s

/-- Power-basis coordinates of an accepted short vector fit within the input bits. -/
theorem product_coordinate_bound (x : SVPInput) (hw : x.WellFormed)
    (c : List ℤ × List ℤ) (hc : verifier (x,c) = true) (i) :
    |pairCoeffs x.q (product x c) i| ≤ (2 : ℤ)^(encSVP x).length := by
  let : NeZero x.q := ⟨(SVPInput.prime hw).ne_zero⟩
  have hn : pairNorm x.q (product x c) ≤ x.threshold := by
    have hh := hc
    simp only [verifier, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.2
  have hth : |x.threshold| ≤ (2 : ℤ)^(encSVP x).length := by
    have hlen := (input_length_bounds x).2.2.2.2
    rw [length_encIntBin] at hlen
    have hs : x.threshold.natAbs.size ≤ (encSVP x).length := by omega
    rw [← Int.natCast_natAbs]
    exact_mod_cast (Nat.size_le.mp hs).le
  have hb (a b : List ℤ) (hn : norm x.q a + norm x.q b ≤ x.threshold)
      (j : Fin (x.q-1)) : |ofList a j| ≤ (2 : ℤ)^(encSVP x).length := by
    have hj : j.val < x.q := by have := j.isLt; omega
    have he := powerCoeffs_abs_le_norm a (j.val : ZMod x.q)
    have hbn : 0 ≤ norm x.q b := by rw [norm_eq]; exact normSq_nonneg _
    have hh : |ofList a j| ≤ x.threshold := by
      have ht : norm x.q a ≤ x.threshold := by omega
      apply le_trans ?_ ht
      simpa only [powerCoeffs, ZMod.val_natCast_of_lt hj, ite_eq_left j.isLt, ofList] using he
    exact hh.trans ((le_abs_self _).trans hth)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [pairCoeffs, Fin.append_left] using hb (product x c).1 (product x c).2 hn j
  · simpa only [pairCoeffs, Fin.append_right] using
      hb (product x c).2 (product x c).1 (by dsimp [pairNorm] at hn; omega) j

/-- An explicit cubic polynomial bounding each multiplier's magnitude bits. -/
def certificateBitsPolynomial : Polynomial ℕ :=
  (Polynomial.X+1) * (16*(2*Polynomial.X+1)^2) + 1

/-- Every YES instance has an accepted certificate of polynomial coefficient bit size. -/
theorem bounded_certificate (x : SVPInput) (hx : x ∈ ModuleSVPLang) :
    ∃ c : List ℤ × List ℤ, verifier (x,c) = true ∧
      ∀ z ∈ c.1 ++ c.2,
        z.natAbs.size ≤ certificateBitsPolynomial.eval (encSVP x).length := by
  obtain ⟨c,hc⟩ := (moduleSVP_iff_exists_check x).mp hx
  let N := (encSVP x).length
  have hd := dimension_le_input_length x
  have hdim : (((x.q-1)+(x.q-1) : ℕ) : ℤ) ≤ (2 : ℤ)^(N+1) := by
    have ht : (x.q : ℤ) ≤ (2 : ℤ)^N := by
      exact_mod_cast hd.trans (Nat.lt_two_pow_self (n := N)).le
    rw [pow_succ]
    push_cast
    omega
  obtain ⟨u,hu,hbits⟩ := exists_integer_preimage_bits
    (certificateMatrix x) (pairCoeffs x.q (product x c)) (N+1) (by omega)
    hdim hdim (certificateMatrix_entry_bound x)
    (fun i => (product_coordinate_bound x hx.1 c hc i).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega : N ≤ N+1)))
    ⟨pairCoeffs x.q c, certificateMatrix_mulVec x (SVPInput.prime hx.1).pos c⟩
  let c' := coefficientLists x.q u
  have hcl : c'.1.length = x.q-1 ∧ c'.2.length = x.q-1 := by
    simp [c', coefficientLists]
  have hp : product x c' = product x c := by
    apply pairCoeffs_injective x.q _ _
      ⟨length_add _ _ _, length_add _ _ _⟩ ⟨length_add _ _ _, length_add _ _ _⟩
    rw [← certificateMatrix_mulVec x (SVPInput.prime hx.1).pos c',
      show pairCoeffs x.q c' = u from pairCoeffs_coefficientLists x.q u]
    exact hu
  refine ⟨c', ?_, ?_⟩
  · have hl := (verifier_spec x hx.1 c).mp hc
    have hlen₁ : c.1.length = x.q-1 := hl.1
    have hlen₂ : c.2.length = x.q-1 := hl.2.1
    simpa only [verifier, hp, hcl.1, hcl.2, hlen₁, hlen₂] using hc
  · have hpoly : (N+1)*(16*(((x.q-1)+(x.q-1))+1)^2)+1 ≤
        certificateBitsPolynomial.eval N := by
      simp only [certificateBitsPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
      gcongr
      omega
    intro z hz
    apply le_trans ?_ hpoly
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz
      exact hbits (Fin.castAdd (x.q-1) j)
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz
      exact hbits (Fin.natAdd (x.q-1) j)

end Rank2ModuleSVP.Membership

namespace Rank2ModuleSVP
open Cslib.Complexity
/-- Decision-SVP for the encoded rank-two prime-cyclotomic modules belongs to NP. -/
theorem moduleSVP_mem_NP : ModuleSVPLang ∈ NP encSVP :=
  moduleSVP_mem_NP_of_resource_bounds Membership.certificateBitsPolynomial
    Membership.bounded_certificate
end Rank2ModuleSVP
