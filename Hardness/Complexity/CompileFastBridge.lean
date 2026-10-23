import Hardness.Complexity.CompileFast
import Hardness.Complexity.CompileBridge
import Hardness.Complexity.ListRing
import Mathlib.Data.Nat.Count

/-! # The list compiler agrees coefficient by coefficient with the cubic reduction -/
namespace Hardness
namespace Fast


@[simp] theorem A_eq (S : MaskedSys) (i : Fin (M S)) (j : Fin (n S)) :
    A S i.val j.val = S.paddedSystem.A i j := by
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [A, MaskedSys.paddedSystem, MaskedSys.toSystem]

@[simp] theorem b_eq (S : MaskedSys) (i : Fin (M S)) :
    b S i.val = S.paddedSystem.b i := by
  refine Fin.cases ?_ (fun i => ?_) i <;>
    simp [b, MaskedSys.paddedSystem, MaskedSys.toSystem]

@[simp] theorem mask_eq (S : MaskedSys) (j : Fin (n S)) :
    mask S j.val = S.paddedSystem.μ j := by
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [mask, MaskedSys.paddedSystem, MaskedSys.toSystem]

/-- Counting Boolean matches is an integral sum of indicator bits. -/
theorem count_int {α : Type} (l : List α) (p : α → Bool) :
    (l.countP p : ℤ) = (l.map fun x => bit (p x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => cases hp : p a <;> simp [hp, ih, bit, add_comm]

theorem sum_product {α β : Type} (l : List α) (k : List β) (f : α × β → ℤ) :
    ((l.product k).map f).sum = (l.map fun a => (k.map fun b => f (a,b)).sum).sum := by
  induction l with
  | nil => simp [List.product]
  | cons a l ih =>
    change ((k.map (Prod.mk a) ++ l.product k).map f).sum = _
    simp only [List.map_append, List.sum_append, List.map_map, ih, Function.comp_def,
      List.map_cons, List.sum_cons]

theorem count_range (d : ℕ) (p : ℕ → Bool) :
    ((List.range d).countP p : ℤ) = ∑ i : Fin d, bit (p i.val) := by
  rw [count_int, list_sum_range, Finset.sum_range]

theorem count_entries (S : MaskedSys) (p : ℕ × ℕ → Bool) :
    ((entries S).countP p : ℤ) =
      ∑ i : Fin (M S), ∑ j : Fin (n S), bit (p (i.val,j.val)) := by
  simp only [count_int, entries, sum_product, list_sum_range, Finset.sum_range]

theorem count_crosses (S : MaskedSys) (p : (ℕ × ℕ) × ℕ → Bool) :
    ((crosses S).countP p : ℤ) =
      ∑ i : Fin (M S), ∑ j : Fin (n S), ∑ k : Fin (n S),
        bit (p ((i.val,j.val),k.val)) := by
  simp only [count_int, crosses, entries, sum_product, list_sum_range, Finset.sum_range]

@[simp] theorem sqrtCeil_eq (r : ℕ) : sqrtCeil r = ReductionData.ceilSqrt r := by
  have hb : ReductionData.ceilSqrt r ≤ r := by
    rw [ReductionData.ceilSqrt_le_iff]
    nlinarith
  have he : {k ∈ Finset.range r | k^2 < r} = Finset.range (ReductionData.ceilSqrt r) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    have hk := ReductionData.ceilSqrt_le_iff r k
    omega
  unfold sqrtCeil
  change Nat.count (fun k => k^2 < r) r = _
  rw [Nat.count_eq_card_filter_range, he, Finset.card_range]

@[simp] theorem N_eq (S : MaskedSys) : N S = S.reductionDataCubic.N := rfl

@[simp] theorem alpha_eq (S : MaskedSys) (j : Fin (n S)) :
    alpha S j.val = S.reductionDataCubic.positions.α j := rfl

@[simp] theorem rho_eq (S : MaskedSys) (i : Fin (M S)) :
    rho S i.val = S.reductionDataCubic.positions.ρ i := rfl

@[simp] theorem hExp_eq (S : MaskedSys) (i : Fin (M S)) (j : Fin (n S)) :
    hExp S i.val j.val = S.reductionDataCubic.positions.hExp i j := rfl

@[simp] theorem crossExp_eq (S : MaskedSys) (i : Fin (M S)) (j k : Fin (n S)) :
    crossExp S i.val j.val k.val = S.reductionDataCubic.positions.crossExp i j k := rfl

@[simp] theorem W_eq (S : MaskedSys) : W S = S.reductionDataCubic.W := by
  have he := S.reductionDataCubic.entry_sum (fun _ _ => 1)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at he
  apply Int.natCast_inj.mp
  rw [W, count_entries]
  simpa only [A_eq, MaskedSys.reductionDataCubic, ReductionData.W, M, n] using he.symm

@[simp] theorem nu_eq (S : MaskedSys) : nu S = S.reductionDataCubic.ν := by
  simp only [nu, W_eq]; rfl

@[simp] theorem weight_eq (S : MaskedSys) : weight S = S.reductionDataCubic.weight := by
  apply Int.natCast_inj.mp
  rw [weight, count_range]
  simpa only [mask_eq, MaskedSys.reductionDataCubic, n] using S.reductionDataCubic.sum_bit_mask

@[simp] theorem h_eq (S : MaskedSys) (r : Fin S.reductionDataCubic.N) :
    (h S r.val : ℤ) = S.reductionDataCubic.h r := by
  rw [h, count_entries, ReductionData.h, Cyclotomic.sparse_apply]
  have he := S.reductionDataCubic.entry_sum (fun i j =>
    if r.val = S.reductionDataCubic.positions.hExp i j then (1 : ℤ) else 0)
  have hr (e : S.reductionDataCubic.Entry) :
      (r = S.reductionDataCubic.hPosition e) ↔
        r.val = S.reductionDataCubic.positions.hExp e.val.1 e.val.2 := Fin.ext_iff
  simp_rw [hr]
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [A_eq, hExp_eq]
  change bit (S.reductionDataCubic.system.A i j &&
    decide (r.val = S.reductionDataCubic.positions.hExp i j)) = _
  by_cases hp : r.val = S.reductionDataCubic.positions.hExp i j <;> simp [hp, bit]

@[simp] theorem u_eq (S : MaskedSys) (r : Fin S.reductionDataCubic.N) :
    (u S r.val : ℤ) = S.reductionDataCubic.u r := by
  rw [u, count_range, ReductionData.u, ReductionData.a, Cyclotomic.sparse_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hr : (r = S.reductionDataCubic.alpha j) ↔
      r.val = S.reductionDataCubic.positions.α j := Fin.ext_iff
  simp only [mask_eq, alpha_eq, hr]
  change bit (S.reductionDataCubic.system.μ j &&
    decide (r.val = S.reductionDataCubic.positions.α j)) = _
  by_cases hp : r.val = S.reductionDataCubic.positions.α j <;> simp [hp, bit]

@[simp] theorem t_eq (S : MaskedSys) (r : Fin S.reductionDataCubic.N) :
    (t S r.val : ℤ) = S.reductionDataCubic.t r := by
  classical
  let D := S.reductionDataCubic
  have hc (e : D.Entry) :
      (∑ k : {k : Fin (n S) // k ≠ e.val.2},
        if r.val = D.positions.crossExp e.val.1 e.val.2 k.val then (1 : ℤ) else 0) =
      ∑ k : Fin (n S), if k ≠ e.val.2 then
        (if r.val = D.positions.crossExp e.val.1 e.val.2 k then (1 : ℤ) else 0) else 0 := by
    exact (Finset.sum_subtype (p := fun k : Fin (n S) => k ≠ e.val.2)
      (Finset.univ.filter (fun k => k ≠ e.val.2)) (by intro k; simp)
      (fun k => if r.val = D.positions.crossExp e.val.1 e.val.2 k then (1 : ℤ) else 0)).symm.trans
      (Finset.sum_filter _ _)
  have hcross : (∑ z : D.Cross,
      if r.val = D.positions.crossExp z.1.val.1 z.1.val.2 z.2.val then (1 : ℤ) else 0) =
      ∑ i : Fin (M S), ∑ j : Fin (n S), bit (D.system.A i j) *
        ∑ k : Fin (n S), if k ≠ j then
          (if r.val = D.positions.crossExp i j k then (1 : ℤ) else 0) else 0 := by
    rw [Fintype.sum_sigma]
    simp_rw [hc]
    exact D.entry_sum (fun i j => ∑ k : Fin (n S), if k ≠ j then
      (if r.val = D.positions.crossExp i j k then (1 : ℤ) else 0) else 0)
  rw [t, Nat.cast_add, Nat.cast_mul, count_range, count_crosses,
    ReductionData.t, Cyclotomic.sparse_apply, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ReductionData.coordinate, Fin.ext_iff]
  rw [hcross]
  apply congrArg₂ (· + ·)
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [b_eq, rho_eq]
    change (2 : ℤ) * bit (D.system.b i && decide (r.val = D.positions.ρ i)) =
      if r.val = D.positions.ρ i then 2 * bit (D.system.b i) else 0
    by_cases hr : r.val = D.positions.ρ i <;> simp [hr, bit]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [A_eq, crossExp_eq]
    change bit (D.system.A i j && decide (k.val ≠ j.val) &&
      decide (r.val = D.positions.crossExp i j k)) =
      bit (D.system.A i j) * (if k ≠ j then
        (if r.val = D.positions.crossExp i j k then 1 else 0) else 0)
    by_cases hk : k = j <;> by_cases hr : r.val = D.positions.crossExp i j k <;>
      simp [hk, hr, bit, ← Fin.ext_iff]

@[simp] theorem b_count_eq (S : MaskedSys) :
    (List.range (M S)).countP (b S) =
      (Finset.univ.filter fun i => S.reductionDataCubic.system.b i = true).card := by
  apply Int.natCast_inj.mp
  rw [count_range]
  simp only [b_eq, bit, Finset.sum_boole]
  rfl

@[simp] theorem P_eq (S : MaskedSys) : P S = S.reductionDataCubic.P := by
  simp only [P, sqrtCeil_eq, W_eq, b_count_eq, nu_eq, ReductionData.P,
    ReductionData.s, ReductionData.t_norm]
  norm_cast

@[simp] theorem gCoeff_eq (S : MaskedSys) (r : Fin S.reductionDataCubic.d) :
    gCoeff S r.val = S.reductionDataCubic.g r := by
  unfold gCoeff ReductionData.g Cyclotomic.interleave
  split_ifs <;>
    simp_all [Cyclotomic.monomial, Fin.ext_iff, ← h_eq, P_eq]

@[simp] theorem TCoeff_eq (S : MaskedSys) (r : Fin S.reductionDataCubic.d) :
    TCoeff S r.val = S.reductionDataCubic.T r := by
  unfold TCoeff ReductionData.T Cyclotomic.interleave
  split_ifs <;> simp_all [← t_eq, ← u_eq, P_eq]

theorem map_range_eq_toList {d : ℕ} (f : ℕ → ℤ) (v : Coeff d)
    (hv : ∀ i : Fin d, f i.val = v i) : (List.range d).map f = toList v := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simpa [toList] using hv ⟨i, by simpa using hi⟩

@[simp] theorem wellFormed_eq (S : MaskedSys) : wellFormed S = true ↔ S.WellFormed := by
  simp [wellFormed, MaskedSys.WellFormed, List.all_eq_true, and_assoc]

theorem compile_eq (S : MaskedSys) :
    compile S = toCVPInput S.reductionDataCubic.toPrincipalCVPInstance := by
  unfold compile toCVPInput ReductionData.toPrincipalCVPInstance
  simp only [N_eq, P_eq, weight_eq, nu_eq]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact map_range_eq_toList _ _ (gCoeff_eq S)
  · exact map_range_eq_toList _ _ (TCoeff_eq S)

end Fast

/-- The list program enumerates exactly the cubic reduction's coefficients. -/
theorem compileFast_eq (S : MaskedSys) (hw : S.WellFormed) :
    compileFast S = toCVPInput S.reductionDataCubic.toPrincipalCVPInstance := by
  simp only [compileFast, (Fast.wellFormed_eq S).mpr hw, ↓reduceIte, Fast.compile_eq]

/-- Total correctness, including zero sizes and malformed inputs. -/
theorem compileFast_correct (S : MaskedSys) :
    S.Feasible ↔ compileFast S ∈ PrincipalCVP := by
  by_cases hw : S.WellFormed
  · rw [compileFast_eq S hw, toCVPInput_mem_iff]
    change S.Feasible ↔ CVPYes S.reductionDataCubic.lattice
      S.reductionDataCubic.T S.reductionDataCubic.Δ
    rw [← S.reductionDataCubic.compiler_correct]
    exact ⟨fun h => (S.paddedSystem_hasSolution_iff).mpr h.2,
      fun h => ⟨hw, (S.paddedSystem_hasSolution_iff).mp h⟩⟩
  · have hc : Fast.wellFormed S ≠ true := fun h => hw ((Fast.wellFormed_eq S).mp h)
    simp only [MaskedSys.Feasible, hw, false_and, compileFast, hc]
    exact iff_false_intro cvpNoInput_not_mem |>.symm

end Hardness
