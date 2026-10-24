import Rank2ModuleSVP.Asymptotics

/-! v2 §4.3, Theorem 4.4: abstract admissible representatives, without any
checker dependency. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
namespace Rank2ModuleSVP
open scoped BigOperators
noncomputable section

/-- At most twice |P| ordered pairs at an offset touch P. -/
theorem touching_pairs_card {q : ℕ} [NeZero q] (P : Finset (ZMod q)) (d : ZMod q) :
    (Finset.univ.filter fun a => a ∈ P ∨ a+d ∈ P).card ≤ 2*P.card := by
  classical
  have he : (Finset.univ.filter fun a => a ∈ P ∨ a+d ∈ P) =
      P ∪ P.image (fun b => b-d) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image]
    constructor
    · rintro (ha | ha)
      · exact Or.inl ha
      · exact Or.inr ⟨a+d, ha, by abel⟩
    · rintro (ha | ⟨b, hb, rfl⟩)
      · exact Or.inl ha
      · exact Or.inr (by simpa using hb)
  rw [he]
  have hh := Finset.card_image_le (s := P) (f := fun b => b-d)
  have hu := Finset.card_union_le P (P.image fun b => b-d)
  omega

/-- A finite quantitative union bound, using exactly the one- and two-free-endpoint counts. -/
theorem clean_event_budget {q h : ℕ} [NeZero q]
    (F : Finset (Coeff ℤ q)) (P D : Finset (ZMod q))
    (hq : 0 < q) (hF : F.Nonempty) (hD : (0 : ZMod q) ∉ D)
    (hratio : ∀ Q : Finset (ZMod q), Disjoint P Q → Q.card ≤ 2 →
      (q : ℝ)^Q.card*(completionEvent F Q).card ≤ 2*(h : ℝ)^Q.card*F.card)
    (hsmall : 2*D.card*(2*P.card*h+h^2) < q) :
    (∑ p ∈ forbiddenPairIndices P D,
      (F.filter fun x => x p.2 = 1 ∧ x (p.2+p.1) = 1).card) < F.card := by
  classical
  let e : ZMod q → ZMod q → ℝ := fun d a =>
    if a ∉ P ∨ a+d ∉ P then (F.filter fun x => x a = 1 ∧ x (a+d) = 1).card else 0
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hFR : 0 < (F.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hF
  have hpairs (d : ZMod q) (hd : d ∈ D) (a : ZMod q) :
      (q : ℝ)^2*e d a ≤
        if a ∈ P ∨ a+d ∈ P then 2*(h : ℝ)*q*F.card else 2*(h : ℝ)^2*F.card := by
    have hd0 : d ≠ 0 := fun he => hD (he ▸ hd)
    have hab : a ≠ a+d := by intro he; exact hd0 (add_left_cancel (he.symm.trans (add_zero a).symm))
    by_cases ha : a ∉ P ∨ a+d ∉ P
    · let Q : Finset (ZMod q) := {a,a+d} \ P
      have hPQ : Disjoint P Q := Finset.disjoint_left.mpr
        (fun a ha hb => (Finset.mem_sdiff.mp hb).2 ha)
      have hQ2 : Q.card ≤ 2 := (Finset.card_le_card Finset.sdiff_subset).trans_eq
        (Finset.card_pair hab)
      have hr := hratio Q hPQ hQ2
      have hsub : ((F.filter fun x => x a = 1 ∧ x (a+d) = 1).card : ℝ) ≤
          (completionEvent F Q).card := by exact_mod_cast card_pairEvent_le F P a (a+d)
      dsimp [e]
      rw [ite_eq_left ha]
      by_cases ht : a ∈ P ∨ a+d ∈ P
      · have hQ1 : Q.card = 1 := by
          rcases ht with haP | hbP
          · have hb : a+d ∉ P := ha.resolve_left (not_not.mpr haP)
            have heQ : Q = {a+d} := by
              ext b
              simp only [Q, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
              aesop
            rw [heQ, Finset.card_singleton]
          · have ha' : a ∉ P := ha.resolve_right (not_not.mpr hbP)
            have heQ : Q = {a} := by
              ext b
              simp only [Q, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
              aesop
            rw [heQ, Finset.card_singleton]
        rw [hQ1, pow_one, pow_one] at hr
        rw [ite_eq_left ht]
        have hs := mul_le_mul_of_nonneg_left hsub hqR.le
        have hs' := mul_le_mul_of_nonneg_left (hs.trans hr) hqR.le
        nlinarith only [hs']
      · have haP : a ∉ P := fun h => ht (Or.inl h)
        have hbP : a+d ∉ P := fun h => ht (Or.inr h)
        have hQ : Q = {a,a+d} := by ext b; simp [Q]; aesop
        have hcard : Q.card = 2 := by rw [hQ, Finset.card_pair hab]
        rw [hcard] at hr
        rw [ite_eq_right ht]
        exact (mul_le_mul_of_nonneg_left hsub (sq_nonneg (q : ℝ))).trans hr
    · dsimp [e]
      rw [ite_eq_right ha, mul_zero]
      split_ifs <;> positivity
  have hsum (d : ZMod q) (hd : d ∈ D) :
      (q : ℝ)^2*(∑ a, e d a) ≤
        2*(2*(P.card : ℝ)*h*q+(q : ℝ)*h^2)*F.card := by
    have hh := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (ZMod q))) => hpairs d hd a)
    rw [← Finset.mul_sum] at hh
    have hcard := touching_pairs_card P d
    have hcardR : ((Finset.univ.filter fun a => a ∈ P ∨ a+d ∈ P).card : ℝ) ≤ 2*P.card := by
      exact_mod_cast hcard
    have hcomp : ((Finset.univ.filter fun a : ZMod q => ¬(a ∈ P ∨ a+d ∈ P)).card : ℝ) ≤ q := by
      exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset (ZMod q)) _ |>.trans_eq (by simp))
    conv_rhs at hh =>
      rw [Finset.sum_ite]
      simp only [Finset.sum_const, nsmul_eq_mul]
    have hc1 := mul_le_mul_of_nonneg_right hcardR
      (show 0 ≤ 2*(h : ℝ)*q*F.card by positivity)
    have hc2 := mul_le_mul_of_nonneg_right hcomp
      (show 0 ≤ 2*(h : ℝ)^2*F.card by positivity)
    nlinarith only [hh, hc1, hc2]
  have htotal := Finset.sum_le_sum hsum
  rw [← Finset.mul_sum] at htotal
  simp only [Finset.sum_const, nsmul_eq_mul] at htotal
  have heq : ((∑ p ∈ forbiddenPairIndices P D,
      (F.filter fun x => x p.2 = 1 ∧ x (p.2+p.1) = 1).card : ℕ) : ℝ) =
      ∑ d ∈ D, ∑ a, e d a := by
    simp only [forbiddenPairIndices, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_zero, e]
    exact Finset.sum_product D Finset.univ _
  have hsmallR : 2*(D.card : ℝ)*(2*(P.card : ℝ)*h+(h : ℝ)^2) < q := by exact_mod_cast hsmall
  have hstrict := mul_lt_mul_of_pos_right hsmallR (mul_pos hqR hFR)
  have hbudget : ((∑ p ∈ forbiddenPairIndices P D,
      (F.filter fun x => x p.2 = 1 ∧ x (p.2+p.1) = 1).card : ℕ) : ℝ) < F.card := by
    rw [← heq] at htotal
    have hlt : (q : ℝ)^2 * ((∑ p ∈ forbiddenPairIndices P D,
        (F.filter fun x => x p.2 = 1 ∧ x (p.2+p.1) = 1).card : ℕ) : ℝ) <
        (q : ℝ)^2*F.card := by nlinarith only [htotal, hstrict]
    exact (mul_lt_mul_iff_right₀ (sq_pos_of_pos hqR)).mp hlt
  exact_mod_cast hbudget


/-- Explicit cubic bound for the union-bound numerator, using |P|² ≤ k. -/
theorem cnt_clean_numerator {q k : ℕ} [NeZero q] (hk : 1 ≤ k)
    (P D : Finset (ZMod q)) (hP : P.card ≤ Nat.sqrt k)
    (hD : D.card ≤ 100*P.card^2+100) :
    2*D.card*(2*P.card*cntH k+(cntH k)^2) ≤ 3200*k^3 := by
  have hPk : P.card ≤ k := hP.trans (Nat.sqrt_le_self k)
  have hPsq : P.card^2 ≤ k := by
    have hh := Nat.sqrt_le k
    have hp := Nat.pow_le_pow_left hP 2
    nlinarith only [hh, hp]
  have hh := (cntH_bounds k).2
  have hDk : D.card ≤ 200*k := by omega
  have hb : 2*P.card*cntH k+(cntH k)^2 ≤ 8*k^2 := by
    calc
      _ ≤ 2*k*(2*k)+(2*k)^2 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 2*(200*k)*(8*k^2) := by gcongr
    _ = 3200*k^3 := by ring

/-- The explicit O(n³h+n²h²)/q budget is less than one. -/
theorem cnt_clean_budget {q k : ℕ} [NeZero q] (hk : cntK0 ≤ k)
    (hpow : (2*k)^cntC0 ≤ q) (P D : Finset (ZMod q))
    (hP : P.card ≤ Nat.sqrt k) (hD : D.card ≤ 100*P.card^2+100) :
    2*D.card*(2*P.card*cntH k+(cntH k)^2) < q := by
  have hk1 : 1 ≤ k := by have : 100000000 ≤ k := hk; omega
  calc
    _ ≤ 3200*k^3 := cnt_clean_numerator hk1 P D hP hD
    _ ≤ 1000000*k^4 := Nat.mul_le_mul (by norm_num)
      (Nat.pow_le_pow_right hk1 (by omega))
    _ < q := cnt_q_polynomial hk hpow

/-- Strong form of v2 Theorem 4.4: all pairs at the supplied offsets with
at least one endpoint outside P simultaneously have zero product. -/
theorem admissible_completions (hWan : WanPowerSumEstimates)
    {q k : ℕ} [NeZero q] (hq : q.Prime) (hk : cntK0 ≤ k)
    (hpow : (2*k)^cntC0 ≤ q)
    (u : Fin k → ZMod q) (P D : Finset (ZMod q)) (η : Coeff ℤ q)
    (hP : P.card+2 ≤ Nat.sqrt k)
    (hD : D.card ≤ 100*P.card^2+100) (hD0 : (0 : ZMod q) ∉ D)
    (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1)
    (hu : u ⟨0, by have : 100000000 ≤ k := hk; omega⟩ = (cntH k : ZMod q)) :
    ∃ x ∈ completions k (cntH k) u P η,
      ∀ d ∈ D, ∀ a, a ∉ P ∨ a+d ∉ P → x a*x (a+d) = 0 := by
  apply exists_clean_products_of_budget (completions k (cntH k) u P η) P D
    (fun x hx => ((mem_completions _ _ _ _ _ _).mp hx).1)
  apply clean_event_budget (completions k (cntH k) u P η) P D hq.pos
    (uniform_completions_nonempty hWan hq hk hpow u P η (by omega) hη hu) hD0
  · intro J hPJ hJ
    exact (fixed_coordinate_ratio hWan hq hk hpow u P J η (by omega) hPJ hη hu).le
  · exact cnt_clean_budget hk hpow P D (by omega) hD

/-- Abstract v2 Theorem 4.4 for an arbitrary family of forbidden ordered pairs.
The caller supplies only their nonzero offsets and the external-endpoint property. -/
theorem admissible_representative (hWan : WanPowerSumEstimates)
    {q k : ℕ} [NeZero q] (hq : q.Prime) (hk : cntK0 ≤ k)
    (hpow : (2*k)^cntC0 ≤ q)
    (u : Fin k → ZMod q) (P D : Finset (ZMod q)) (η : Coeff ℤ q)
    (hP : P.card+2 ≤ Nat.sqrt k)
    (hD : D.card ≤ 100*P.card^2+100) (hD0 : (0 : ZMod q) ∉ D)
    (hη : ∀ a ∈ P, η a = 0 ∨ η a = 1)
    (hu : u ⟨0, by have : 100000000 ≤ k := hk; omega⟩ = (cntH k : ZMod q))
    (forbidden : ZMod q → ZMod q → Prop)
    (hforbidden : ∀ a b, forbidden a b → b-a ∈ D ∧ (a ∉ P ∨ b ∉ P)) :
    ∃ x ∈ completions k (cntH k) u P η,
      ∀ a b, forbidden a b → x a*x b = 0 := by
  obtain ⟨x, hx, hz⟩ := admissible_completions hWan hq hk hpow u P D η hP hD hD0 hη hu
  refine ⟨x, hx, ?_⟩
  intro a b hab
  obtain ⟨hd, hext⟩ := hforbidden a b hab
  have he : a+(b-a) = b := by abel
  simpa only [he] using hz (b-a) hd a (by simpa only [he] using hext)

end
end Rank2ModuleSVP
