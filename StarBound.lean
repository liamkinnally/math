module

public import TreeDegree
public import Mathlib.Combinatorics.SimpleGraph.Star

@[expose] public section

namespace WOW261

open Finset SimpleGraph

variable {V : Type*} [Fintype V]

/-- Maximum number of leaves in a spanning tree. Graphs with no spanning tree
receive the default value zero of the finite supremum. -/
noncomputable def maxLeafNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact (univ : Finset (SimpleGraph V)).sup fun T =>
    if T ≤ G ∧ T.IsTree then (leaves T).card else 0

theorem leaves_le_maxLeafNumber (G T : SimpleGraph V) [dT : DecidableRel T.Adj]
    (hle : T ≤ G) (ht : T.IsTree) : (leaves T).card ≤ maxLeafNumber G := by
  classical
  unfold maxLeafNumber
  have h := Finset.le_sup (f := fun T : SimpleGraph V =>
    if T ≤ G ∧ T.IsTree then (leaves T).card else 0) (Finset.mem_univ T)
  have yes : T ≤ G ∧ T.IsTree := ⟨hle, ht⟩
  rw [Subsingleton.elim dT (fun a b => Classical.propDecidable (T.Adj a b))]
  simpa [yes] using h

omit [Fintype V] in
/-- Every edge incident with a specified vertex can be preserved when
passing to a spanning tree. -/
theorem exists_tree_preserving_neighbors (G : SimpleGraph V) (hc : G.Connected) (v : V) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ ∀ w, G.Adj v w → T.Adj v w := by
  let stars := G ⊓ starGraph v
  have ac : stars.IsAcyclic := (isAcyclic_starGraph v).anti inf_le_right
  obtain ⟨T, hle, hTG, hT⟩ := hc.exists_isTree_le_of_le_of_isAcyclic (H := stars) inf_le_left ac
  refine ⟨T, hTG, hT, fun w hw => hle ?_⟩
  exact ⟨hw, starGraph_center_adj hw.ne⟩

/-- The maximum spanning-tree leaf count bounds every vertex degree of
a nontrivial connected graph. -/
theorem degree_le_maxLeafNumber [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (v : V) : G.degree v ≤ maxLeafNumber G := by
  classical
  obtain ⟨T, hTG, hT, keep⟩ := exists_tree_preserving_neighbors G hc v
  have bound : G.degree v ≤ T.degree v := by
    apply Finset.card_le_card
    intro w hw
    exact (T.mem_neighborFinset v w).mpr (keep w ((G.mem_neighborFinset v w).mp hw))
  exact bound.trans ((degree_le_leaves_of_tree T hT v).trans (leaves_le_maxLeafNumber G T hTG hT))

/-- When a connected graph has at most two leaves in each spanning tree,
all vertices of degree different from two are leaves of every spanning tree. -/
theorem count_nondegreeTwo_le_maxLeafNumber_of_le_two [Nontrivial V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hc : G.Connected) (hL : maxLeafNumber G ≤ 2) :
    (univ.filter fun v => G.degree v ≠ 2).card ≤ maxLeafNumber G := by
  classical
  obtain ⟨T, hTG, hT⟩ := hc.exists_isTree_le
  apply le_trans _ (leaves_le_maxLeafNumber G T hTG hT)
  apply Finset.card_le_card
  intro v hv
  have ne := (Finset.mem_filter.mp hv).2
  have upper := (degree_le_maxLeafNumber G hc v).trans hL
  have compare : T.degree v ≤ G.degree v := SimpleGraph.degree_le_of_le hTG
  have pos := hT.preconnected.degree_pos_of_nontrivial v
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩

end WOW261
