module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace WOW261

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A total dominating set of a connected graph remains total dominating in
some spanning tree. First choose a spanning forest of the graph restricted
to edges internal to D. This forest has no isolated vertex in D. Attach
each remaining vertex to one chosen neighbor in D, then extend to a tree. -/
theorem exists_spanningTree_preserving_totalDomination (connected : G.Connected)
    (D : Finset V) (dom : ∀ v, ∃ d ∈ D, G.Adj v d) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ ∀ v, ∃ d ∈ D, T.Adj v d := by
  classical
  let J : SimpleGraph V :=
    { Adj := fun u v => u ∈ D ∧ v ∈ D ∧ G.Adj u v
      symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
      loopless := ⟨fun _ h => h.2.2.ne rfl⟩ }
  obtain ⟨K, hKJ, hK, hreach⟩ := J.exists_isAcyclic_reachable_eq_le
  have inside (v : V) (hv : v ∈ D) : ∃ d ∈ D, K.Adj v d := by
    obtain ⟨d, hd, h⟩ := dom v
    have hr : K.Reachable v d := by
      rw [hreach]
      exact (show J.Adj v d from ⟨hv, hd, h⟩).reachable
    obtain ⟨w, hw⟩ := hr.nonempty_neighborSet_left h.ne
    exact ⟨w, (hKJ hw).2.1, hw⟩
  have build (s : Finset V) : (∀ v ∈ s, v ∉ D) →
      ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
        (∀ v, v ∈ D ∨ v ∈ s → ∃ d ∈ D, F.Adj v d) ∧
        (∀ v, v ∉ D → v ∉ s → ∀ w, ¬ F.Adj v w) := by
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨K, fun _ _ h => (hKJ h).2.2, hK, ?_, ?_⟩
      · intro v hv
        exact inside v (by simpa using hv)
      · intro v hv _ w ha
        exact hv (hKJ ha).1
    | @insert x s hx ih =>
      intro hs
      have hxD : x ∉ D := hs x (Finset.mem_insert_self ..)
      obtain ⟨F, hFG, hF, dominates, isolated⟩ := ih
        (fun v hv => hs v (Finset.mem_insert_of_mem hv))
      obtain ⟨d, hd, hadj⟩ := dom x
      have disconnected : ¬ F.Reachable x d := by
        intro hr
        obtain ⟨w, hw⟩ := hr.nonempty_neighborSet_left hadj.ne
        exact isolated x hxD hx w hw
      refine ⟨F ⊔ edge x d, sup_le hFG ((edge_le_iff G).mpr (Or.inr hadj)),
        IsAcyclic.sup_edge_of_not_reachable disconnected hF, ?_, ?_⟩
      · intro v hv
        by_cases h : v = x
        · subst v
          exact ⟨d, hd, Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hadj.ne⟩)⟩
        · have hprev : v ∈ D ∨ v ∈ s := by simpa [Finset.mem_insert, h] using hv
          obtain ⟨u, huD, hu⟩ := dominates v hprev
          exact ⟨u, huD, Or.inl hu⟩
      · intro v hv hs' w he
        have hne : v ≠ x := by
          intro eq
          exact hs' (eq ▸ Finset.mem_insert_self ..)
        rcases he with h | h
        · exact isolated v hv (fun hvs => hs' (Finset.mem_insert_of_mem hvs)) w h
        · rcases ((edge_adj ..).mp h).1 with h | h
          · exact hne h.1
          · exact hv (h.1 ▸ hd)
  obtain ⟨F, hFG, hF, dominates, _⟩ := build (Finset.univ \ D)
    (fun v hv => (Finset.mem_sdiff.mp hv).2)
  obtain ⟨T, hFT, hTG, hT⟩ := connected.exists_isTree_le_of_le_of_isAcyclic hFG hF
  refine ⟨T, hTG, hT, fun v => ?_⟩
  obtain ⟨d, hd, h⟩ := dominates v (by simp [Classical.em])
  exact ⟨d, hd, hFT h⟩

end WOW261
