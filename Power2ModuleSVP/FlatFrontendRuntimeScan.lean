import Power2ModuleSVP.FlatFrontendRuntimeTaylor

/-! A capped forward run scan. The cap is the input word length and is
inactive on reachable states; it gives a uniform bounded-growth step. -/
namespace Power2ModuleSVP.FlatFrontend
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
abbrev encRun := encPair encUnary encUnary
private abbrev ScanState := List (ℕ × ℕ) × (ℕ × (Bool × ℕ))
private abbrev encScan := encPair (encList encRun) (encPair encUnary (encPair encBool encUnary))

private def scanStep (B : ℕ) (s : ScanState) (b : Bool) : ScanState :=
  let p := min s.2.1 B
  let a := min s.2.2.2 B
  (if s.2.2.1 && !b then (a, p) :: s.1 else s.1,
    (min (p + 1) B, (b, if s.2.2.1 then a else p)))

private def scanFinish (s : ScanState) : List (ℕ × ℕ) :=
  s.1.reverse ++ (if s.2.2.1 then [(s.2.2.2, s.2.1)] else [])

@[fun_prop] private theorem scanStep_polytime : ComputableTidilyInPolyTime
    (fun a : (ℕ × ScanState) × Bool => scanStep a.1.1 a.1.2 a.2)
    (encPair (encPair encUnary encScan) encBool) encScan := by
  let encIn := encPair (encPair encUnary encScan) encBool
  have hB : ComputableTidilyInPolyTime (fun a : (ℕ × ScanState) × Bool => a.1.1)
      encIn encUnary := (fst encUnary encScan).comp (fst _ _)
  have hs : ComputableTidilyInPolyTime (fun a : (ℕ × ScanState) × Bool => a.1.2)
      encIn encScan := (snd encUnary encScan).comp (fst _ _)
  have hp := unary_min.comp (hs.snd'.fst'.prod hB)
  have ha := unary_min.comp (hs.snd'.snd'.snd'.prod hB)
  have ht := hs.snd'.snd'.fst'
  have hc := bool_and.comp (ht.prod (bool_not.comp (snd _ _)))
  have hn := unary_min.comp ((unary_add.comp (hp.prod (const 1))).prod hB)
  have hcons := (cons encRun).comp ((ha.prod hp).prod hs.fst')
  exact ((hc.ite' hcons hs.fst').prod (hn.prod ((snd _ _).prod (ht.ite' ha hp)))).of_enc_eq
    (fun _ => rfl)

private theorem scanStep_growth (B : ℕ) (s : ScanState) (b : Bool) :
    (encScan (scanStep B s b)).length ≤ (encScan s).length + 30 * B + 30 := by
  rcases s with ⟨xs, p, active, a⟩
  have hp : min p B ≤ B := Nat.min_le_right _ _
  have hi : min (min p B + 1) B ≤ B := Nat.min_le_right _ _
  have ha : min a B ≤ B := Nat.min_le_right _ _
  cases active <;> cases b <;>
    simp [scanStep, encScan, encRun, length_encPair, encUnary_apply] <;> omega

private theorem scanFinish_spec (B : ℕ) (s : ScanState) (bs : List Bool)
    (hp : s.2.1 + bs.length ≤ B) (ha : s.2.2.2 ≤ B) :
    scanFinish (bs.foldl (scanStep B) s) =
      s.1.reverse ++ scanCells s.2.1 (if s.2.2.1 then some s.2.2.2 else none) bs := by
  induction bs generalizing s with
  | nil => rcases s with ⟨xs, p, active, a⟩; cases active <;> simp [scanFinish, scanCells]
  | cons b bs ih =>
    rcases s with ⟨xs, p, active, a⟩
    have hp₀ : p ≤ B := by simp only [List.length_cons] at hp; omega
    have hp₁ : p + 1 ≤ B := by simp only [List.length_cons] at hp; omega
    cases active <;> cases b <;>
      simp only [List.foldl_cons, scanStep, Nat.min_eq_left hp₀,
        Nat.min_eq_left hp₁, Nat.min_eq_left ha, Bool.false_and, Bool.true_and,
        Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;>
      rw [ih] <;> simp_all [scanCells, List.reverse_cons, List.append_assoc] <;> omega

@[fun_prop] theorem scanCells_polytime : ComputableTidilyInPolyTime
    (scanCells 0 none) (encList encBool) (encList encRun) := by
  have hloop : ComputableTidilyInPolyTime
      (fun bs : List Bool => bs.foldl (scanStep bs.length) ([], (0, (false, 0))))
      (encList encBool) encScan := by
    apply foldlWith_of_bounded_growth (encP := encUnary) (encA := encBool)
      (encL := encList encBool) (encB := encScan)
      (length encBool) id' (const ([], (0, (false, 0)))) scanStep_polytime
      (growth := fun bs => 30 * bs.length + 30)
      (((PolyBounded.const 30).mul (length encBool).polyBounded).add (.const 30))
    intro bs s b hb
    exact scanStep_growth bs.length s b
  have hf : ComputableTidilyInPolyTime scanFinish encScan (encList encRun) := by
    unfold scanFinish encScan encRun
    fun_prop
  exact (hf.comp hloop).of_enc_eq fun bs => congrArg _ (by
    simpa using (scanFinish_spec bs.length ([], (0, (false, 0))) bs (by simp) (by simp)).symm)
end Power2ModuleSVP.FlatFrontend
