module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace WOW261

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V]

/-- The set of vertices of degree two. -/
def degreeTwo (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => G.degree v = 2

/-- The neighbors of the degree-two vertices lying outside that set. -/
def degreeTwoExternalNeighbors (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] : Finset V :=
  (degreeTwo G).biUnion (fun v => G.neighborFinset v) \ degreeTwo G

theorem mem_degreeTwo_iff (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    v ∈ degreeTwo G ↔ G.degree v = 2 := by
  simp [degreeTwo]

theorem mem_degreeTwoExternalNeighbors_iff (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] (v : V) :
    v ∈ degreeTwoExternalNeighbors G ↔
      G.degree v ≠ 2 ∧ ∃ s, G.degree s = 2 ∧ G.Adj s v := by
  simp only [degreeTwoExternalNeighbors, mem_sdiff, mem_biUnion, mem_degreeTwo_iff,
    SimpleGraph.mem_neighborFinset, and_comm (b := G.degree v ≠ 2)]

/-- Each degree-two vertex contributes at most two external neighbors. -/
theorem card_degreeTwoExternalNeighbors_le (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    (degreeTwoExternalNeighbors G).card ≤ 2 * (degreeTwo G).card := by
  calc
    (degreeTwoExternalNeighbors G).card ≤
        ((degreeTwo G).biUnion fun v => G.neighborFinset v).card :=
      card_mono sdiff_subset
    _ ≤ ∑ v ∈ degreeTwo G, (G.neighborFinset v).card := card_biUnion_le
    _ = ∑ _ ∈ degreeTwo G, (2 : ℕ) := by
      apply sum_congr rfl
      intro v hv
      rw [G.card_neighborFinset_eq_degree, (mem_degreeTwo_iff G v).mp hv]
    _ = 2 * (degreeTwo G).card := by simp [Nat.mul_comm]

/-- The two counted sets are disjoint subsets of the vertex set. -/
theorem card_degreeTwoExternalNeighbors_add_le (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] :
    (degreeTwoExternalNeighbors G).card + (degreeTwo G).card ≤ Fintype.card V := by
  have externalSubset : degreeTwoExternalNeighbors G ⊆ univ \ degreeTwo G := by
    intro v hv
    exact mem_sdiff.mpr ⟨mem_univ v, (mem_sdiff.mp hv).2⟩
  calc
    (degreeTwoExternalNeighbors G).card + (degreeTwo G).card ≤
        (univ \ degreeTwo G).card + (degreeTwo G).card :=
      Nat.add_le_add_right (card_mono externalSubset) _
    _ = Fintype.card V := by
      rw [card_sdiff_add_card_eq_card (subset_univ (degreeTwo G)), card_univ]

end WOW261
