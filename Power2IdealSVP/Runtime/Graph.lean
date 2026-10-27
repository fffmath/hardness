import Complexity.Computability.Complexity.Problems.Clique
import Complexity.Computability.Complexity.Problems.Graph

/-! # Executable normalization of CLIQUE instances

Declared labels are deduplicated without inspecting their magnitudes. The normalized simple
 graph has precisely the distinct declared vertices, indexed from zero.

Paper: `Power2IdealSVP/paper/power2-ideal-svp.txt`, Section 1.1.
-/


namespace Power2IdealSVP.Runtime

open Cslib.Complexity

/-- Distinct declared labels, in order of first occurrence. -/
def graphVertices (G : Graph) : List ℕ := G.distinctVertices

/-- Number of distinct declared vertices, independent of binary label magnitudes. -/
def vertexCount (G : Graph) : ℕ := (graphVertices G).length

/-- The injective lookup of an indexed vertex's original label. -/
def vertexLabel (G : Graph) : Fin (vertexCount G) ↪ ℕ :=
  ⟨(graphVertices G).get, G.nodup_distinctVertices.injective_get⟩

/-- The normalized simple graph: loops and undeclared endpoints cannot create edges. -/
def normalGraph (G : Graph) : SimpleGraph (Fin (vertexCount G)) :=
  G.toSimpleGraph.comap (vertexLabel G)

/-- One copy of each normalized edge, with zero-based endpoints in increasing order. -/
def normalEdges (G : Graph) : List (ℕ × ℕ) :=
  (List.range (vertexCount G)).flatMap fun i =>
    ((List.range (vertexCount G)).filter fun j =>
      decide (i < j) && G.adjBool ((graphVertices G).getD i 0)
        ((graphVertices G).getD j 0)).map fun j => (i, j)

/-- The paper gadget is used exactly for targets between three and the vertex count. -/
def mainCase (x : Graph × ℕ) : Bool :=
  decide (3 ≤ x.2) && decide (x.2 ≤ vertexCount x.1)

/-- Direct answer for targets zero, one, and two; other targets return false. -/
def smallAnswer (x : Graph × ℕ) : Bool :=
  decide (x.2 = 0) || (decide (x.2 = 1) && decide (0 < vertexCount x.1)) ||
    (decide (x.2 = 2) && !(normalEdges x.1).isEmpty)

/-- Normalization preserves the set of declared vertex labels. -/
@[simp] theorem mem_graphVertices {G : Graph} {a : ℕ} :
    a ∈ graphVertices G ↔ a ∈ G.1 := G.mem_distinctVertices

/-- Every indexed vertex has a declared label. -/
theorem vertexLabel_mem (G : Graph) (i : Fin (vertexCount G)) : vertexLabel G i ∈ G.1 :=
  mem_graphVertices.mp (List.get_mem ..)

/-- Every declared label has an index in the normalized graph. -/
theorem exists_vertexLabel {G : Graph} {a : ℕ} (ha : a ∈ G.1) :
    ∃ i : Fin (vertexCount G), vertexLabel G i = a :=
  List.mem_iff_get.mp (mem_graphVertices.mpr ha)

/-- Exact source semantics, including repeated labels and all target cardinalities. -/
theorem normalised_clique_iff (x : Graph × ℕ) :
    x ∈ Clique ↔ ∃ S : Finset (Fin (vertexCount x.1)),
      (normalGraph x.1).IsNClique x.2 S := by
  classical
  constructor
  · rintro ⟨S, hS, hcl⟩
    let U := Finset.univ.filter fun i => vertexLabel x.1 i ∈ S
    have himage : U.image (vertexLabel x.1) = S := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact (Finset.mem_filter.mp hi).2
      · intro ha
        obtain ⟨i, rfl⟩ := exists_vertexLabel (hS a ha)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
    refine ⟨U, ⟨?_, ?_⟩⟩
    · intro i hi j hj hij
      exact hcl.isClique ((Finset.mem_filter.mp hi).2)
        ((Finset.mem_filter.mp hj).2) (fun h => hij ((vertexLabel x.1).injective h))
    · rw [← Finset.card_image_of_injective U (vertexLabel x.1).injective, himage]
      exact hcl.card_eq
  · rintro ⟨S, hS⟩
    refine ⟨S.image (vertexLabel x.1), ?_, ⟨?_, ?_⟩⟩
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact vertexLabel_mem _ _
    · intro a ha b hb hab
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      exact hS.isClique hi hj (fun h => hab (congrArg (vertexLabel x.1) h))
    · rw [Finset.card_image_of_injective _ (vertexLabel x.1).injective]
      exact hS.card_eq

/-- The normalized count is the cardinality of the declared-label set. -/
theorem vertexCount_eq_card (G : Graph) : vertexCount G = G.1.toFinset.card :=
  G.length_distinctVertices

/-- The normalized count is bounded by the source's encoded size. -/
theorem vertexCount_le_encGraph_length (G : Graph) :
    vertexCount G ≤ (Cslib.Complexity.encGraph G).length :=
  G.length_distinctVertices_le

/-- The branch guard gives precisely the hypotheses used by the paper gadget. -/
@[simp] theorem mainCase_eq_true (x : Graph × ℕ) :
    mainCase x = true ↔ 3 ≤ x.2 ∧ x.2 ≤ vertexCount x.1 := by
  simp [mainCase]

/-- Binary targets larger than the distinct vertex count are NO instances. -/
theorem not_clique_of_vertexCount_lt {x : Graph × ℕ} (h : vertexCount x.1 < x.2) :
    x ∉ Clique := by
  intro hx
  have := Graph.le_card_of_mem_Clique hx
  rw [← vertexCount_eq_card] at this
  omega

/-- The stored edge program lists exactly the increasing adjacent indexed pairs. -/
theorem mem_normalEdges {G : Graph} {i j : ℕ} :
    (i, j) ∈ normalEdges G ↔ i < vertexCount G ∧ j < vertexCount G ∧ i < j ∧
      G.adjBool ((graphVertices G).getD i 0) ((graphVertices G).getD j 0) = true := by
  simp [normalEdges, List.mem_flatMap, List.mem_map, List.mem_filter, and_assoc]

/-- The finite-vertex embedding agrees with the total runtime lookup. -/
theorem vertexLabel_eq_getD (G : Graph) (i : Fin (vertexCount G)) :
    vertexLabel G i = (graphVertices G).getD i 0 :=
  (List.getD_eq_get (graphVertices G) (d := 0) i).symm

/-- The edge-list program and the indexed simple graph have exactly the same edges. -/
theorem normalGraph_adj_iff {G : Graph} (i j : Fin (vertexCount G)) :
    (normalGraph G).Adj i j ↔
      (i.val, j.val) ∈ normalEdges G ∨ (j.val, i.val) ∈ normalEdges G := by
  have hadj : (normalGraph G).Adj i j ↔
      G.adjBool ((graphVertices G).getD i 0) ((graphVertices G).getD j 0) = true := by
    change G.toSimpleGraph.Adj (vertexLabel G i) (vertexLabel G j) ↔ _
    rw [← Graph.adjBool_eq_true_iff, vertexLabel_eq_getD, vertexLabel_eq_getD]
  constructor
  · intro h
    have hne := (normalGraph G).ne_of_adj h
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact Or.inl (mem_normalEdges.mpr ⟨i.isLt, j.isLt, hlt, hadj.mp h⟩)
    · refine Or.inr (mem_normalEdges.mpr ⟨j.isLt, i.isLt, hlt, ?_⟩)
      rw [Graph.adjBool_eq_true_iff] at hadj ⊢
      exact (hadj.mp h).symm
  · rintro (h | h)
    · exact hadj.mpr (mem_normalEdges.mp h).2.2.2
    · apply hadj.mpr
      have h' := (mem_normalEdges.mp h).2.2.2
      rw [Graph.adjBool_eq_true_iff] at h' ⊢
      exact h'.symm

/-- The direct edge test detects exactly the existence of a normalized adjacency. -/
theorem normalEdges_nonempty_iff (G : Graph) :
    (normalEdges G).isEmpty = false ↔
      ∃ i j : Fin (vertexCount G), (normalGraph G).Adj i j := by
  rw [List.isEmpty_eq_false_iff_exists_mem]
  constructor
  · rintro ⟨⟨i, j⟩, hij⟩
    obtain ⟨hi, hj, _, hadj⟩ := mem_normalEdges.mp hij
    refine ⟨⟨i, hi⟩, ⟨j, hj⟩, ?_⟩
    change G.toSimpleGraph.Adj ((graphVertices G).get ⟨i, hi⟩)
      ((graphVertices G).get ⟨j, hj⟩)
    rw [← Graph.adjBool_eq_true_iff]
    simpa only [← List.getD_eq_get (d := 0)] using hadj
  · rintro ⟨i, j, hij⟩
    have hne : i ≠ j := (normalGraph G).ne_of_adj hij
    have hadj : G.adjBool ((graphVertices G).getD i 0)
        ((graphVertices G).getD j 0) = true := by
      change G.toSimpleGraph.Adj ((graphVertices G).get i)
        ((graphVertices G).get j) at hij
      rw [← Graph.adjBool_eq_true_iff] at hij
      simpa only [List.getD_eq_get (graphVertices G) (d := 0) i,
        List.getD_eq_get (graphVertices G) (d := 0) j] using hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact ⟨(i, j), mem_normalEdges.mpr ⟨i.isLt, j.isLt, hlt, hadj⟩⟩
    · refine ⟨(j, i), mem_normalEdges.mpr ⟨j.isLt, i.isLt, hlt, ?_⟩⟩
      rw [Graph.adjBool_eq_true_iff] at hadj ⊢
      exact hadj.symm

/-- A normalized graph has a singleton clique exactly when it has a vertex. -/
theorem clique_one_iff (G : Graph) :
    (G, 1) ∈ Clique ↔ 0 < vertexCount G := by
  rw [normalised_clique_iff]
  constructor
  · rintro ⟨S, hS⟩
    obtain ⟨i, _⟩ := Finset.card_pos.mp (by rw [hS.card_eq]; omega)
    exact Nat.zero_lt_of_lt i.isLt
  · intro h
    exact ⟨{⟨0, h⟩}, (normalGraph G).isNClique_singleton.mpr rfl⟩

/-- The target two case is exactly the direct normalized edge test. -/
theorem clique_two_iff (G : Graph) :
    (G, 2) ∈ Clique ↔ (normalEdges G).isEmpty = false := by
  rw [normalised_clique_iff, normalEdges_nonempty_iff]
  constructor
  · rintro ⟨S, hS⟩
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hS.card_eq
    exact ⟨i, j, hS.isClique (by simp) (by simp) hij⟩
  · rintro ⟨i, j, hij⟩
    refine ⟨{i, j}, ⟨?_, Finset.card_pair ((normalGraph G).ne_of_adj hij)⟩⟩
    simpa only [Finset.coe_pair] using
      (SimpleGraph.isClique_pair.mpr (fun _ => hij))

/-- Direct handling of every target below the paper's main range. -/
theorem smallAnswer_correct {x : Graph × ℕ} (hk : x.2 ≤ 2) :
    smallAnswer x = true ↔ x ∈ Clique := by
  obtain ⟨G, k⟩ := x
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by dsimp at hk; omega
  rcases hk' with rfl | rfl | rfl
  · simp only [smallAnswer, Bool.or_eq_true, decide_eq_true_eq, true_or]
    exact iff_of_true trivial ⟨∅, by simp, ⟨by simp, rfl⟩⟩
  · simpa [smallAnswer] using (clique_one_iff G).symm
  · simpa [smallAnswer] using (clique_two_iff G).symm

/-- Outside the paper's main range, the executable Boolean gives the exact CLIQUE answer. -/
theorem smallAnswer_correct_of_not_mainCase {x : Graph × ℕ} (h : mainCase x = false) :
    smallAnswer x = true ↔ x ∈ Clique := by
  by_cases hk : x.2 ≤ 2
  · exact smallAnswer_correct hk
  · have hv : vertexCount x.1 < x.2 := by
      simp only [mainCase, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
      omega
    have hx := not_clique_of_vertexCount_lt hv
    simp only [smallAnswer, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    have h0 : x.2 ≠ 0 := by omega
    have h1 : x.2 ≠ 1 := by omega
    have h2 : x.2 ≠ 2 := by omega
    simp [h0, h1, h2, hx]

end Power2IdealSVP.Runtime
