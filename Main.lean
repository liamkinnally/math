module

public import NeighborhoodBound
public import ForestBound
public import StarBound
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

namespace WOW261

private theorem arithmetic_bound {a s n g L : ℕ}
    (externalCount : a ≤ 2 * s) (disjointCount : a + s ≤ n)
    (dominationSize : 2 ≤ g) (leafCount : 3 ≤ L)
    (leafBound : n + 2 ≤ L + 2 * g) : 2 * a ≤ g * L := by
  by_cases twoDominators : g = 2
  · subst g
    by_cases twoDegreeTwoVertices : 2 ≤ s <;> omega
  by_cases threeDominators : g = 3
  · subst g
    by_cases threeLeaves : L = 3 <;> omega
  obtain ⟨extraLeaves, rfl⟩ := Nat.exists_eq_add_of_le leafCount
  have extraLeafContribution :=
    Nat.mul_le_mul_right extraLeaves (show 4 ≤ 3 * g by omega)
  rw [Nat.mul_assoc] at extraLeafContribution
  rw [Nat.mul_add, Nat.mul_comm g 3]
  omega

/-- Written on the Wall II Conjecture 261 in its cross-multiplied form.
Taking D to be a minimum total dominating set gives the stated bound on
the total domination number. -/
theorem conjecture261 {V : Type*} [Fintype V] [Nontrivial V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (connected : G.Connected)
    (D : Finset V) (dom : ∀ v, ∃ d ∈ D, G.Adj v d) :
    2 * (degreeTwoExternalNeighbors G).card ≤ D.card * maxLeafNumber G := by
  classical
  have dominationSize : 2 ≤ D.card := by
    obtain ⟨d, hd, _⟩ := dom (Classical.choice (inferInstance : Nonempty V))
    obtain ⟨e, he, adj⟩ := dom d
    exact Finset.one_lt_card.mpr ⟨d, hd, e, he, adj.ne⟩
  by_cases smallLeafCount : maxLeafNumber G ≤ 2
  · have externalSubset : degreeTwoExternalNeighbors G ⊆
        Finset.univ.filter (fun v => G.degree v ≠ 2) := by
      intro v hv
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ v, ((mem_degreeTwoExternalNeighbors_iff G v).mp hv).1⟩
    have externalCount : (degreeTwoExternalNeighbors G).card ≤ maxLeafNumber G :=
      (Finset.card_mono externalSubset).trans
        (count_nondegreeTwo_le_maxLeafNumber_of_le_two G connected smallLeafCount)
    exact (Nat.mul_le_mul_left 2 externalCount).trans
      (Nat.mul_le_mul_right (maxLeafNumber G) dominationSize)
  · obtain ⟨T, hTG, hT, treeDom⟩ :=
      exists_spanningTree_preserving_totalDomination connected D dom
    have leafBound : Fintype.card V + 2 ≤ maxLeafNumber G + 2 * D.card :=
      (leaf_lower_of_totalDomination T hT D treeDom).trans
        (Nat.add_le_add_right (leaves_le_maxLeafNumber G T hTG hT) _)
    exact arithmetic_bound (card_degreeTwoExternalNeighbors_le G)
      (card_degreeTwoExternalNeighbors_add_le G) dominationSize (by omega) leafBound

/-- The least size of a total dominating set, when one exists. -/
noncomputable def totalDominationNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ D : Finset V, D.card = k ∧ ∀ v, ∃ d ∈ D, G.Adj v d}

theorem conjecture261_totalDominationNumber {V : Type*} [Fintype V] [Nontrivial V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (connected : G.Connected) :
    2 * (degreeTwoExternalNeighbors G).card ≤ totalDominationNumber G * maxLeafNumber G := by
  let sizes : Set ℕ :=
    {k | ∃ D : Finset V, D.card = k ∧ ∀ v, ∃ d ∈ D, G.Adj v d}
  have hasSizes : sizes.Nonempty := by
    refine ⟨Fintype.card V, Finset.univ, Finset.card_univ, fun v => ?_⟩
    obtain ⟨w, adj⟩ := connected.preconnected.exists_adj_of_nontrivial v
    exact ⟨w, Finset.mem_univ w, adj⟩
  have attained : totalDominationNumber G ∈ sizes := Nat.sInf_mem hasSizes
  obtain ⟨D, hD, dom⟩ := attained
  rw [← hD]
  exact conjecture261 G connected D dom

/-- Written on the Wall II Conjecture 261 with the catalog's quotient. -/
theorem conjecture261_ratio {V : Type*} [Fintype V] [Nontrivial V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (connected : G.Connected) :
    (2 * ((degreeTwoExternalNeighbors G).card : ℚ)) / (maxLeafNumber G : ℚ) ≤
      (totalDominationNumber G : ℚ) := by
  let v : V := Classical.choice (inferInstance : Nonempty V)
  have positiveLeaves : 0 < maxLeafNumber G :=
    (connected.preconnected.degree_pos_of_nontrivial v).trans_le
      (degree_le_maxLeafNumber G connected v)
  have positiveDenominator : (0 : ℚ) < (maxLeafNumber G : ℚ) := by
    exact_mod_cast positiveLeaves
  apply (div_le_iff₀ positiveDenominator).2
  exact_mod_cast conjecture261_totalDominationNumber G connected

end WOW261
