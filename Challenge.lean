module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Graffiti.pc, Written on the Wall II, Conjecture 261

For a finite simple connected graph with at least two vertices, let S consist
of the degree-two vertices and let L be the greatest number of leaves in any
spanning tree. The total domination number is at least twice the number of
distinct neighbors of S outside S, divided by L.

The order restriction gives the usual domain of the quotient. A connected
graph of order at least two admits a total dominating set and has positive L.
The one-vertex graph has no total dominating set and its spanning tree has
zero vertices of degree one.
-/

@[expose] public section

namespace WOW261

open Finset

section

variable {V : Type*} [Fintype V]

/-- Vertices of degree two in the original graph. -/
def degreeTwo (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => G.degree v = 2

/-- The union of the open neighborhoods of the degree-two vertices,
with the degree-two vertices removed. A common neighbor is counted once. -/
def degreeTwoExternalNeighbors (G : SimpleGraph V) [DecidableEq V]
    [DecidableRel G.Adj] : Finset V :=
  (degreeTwo G).biUnion (fun v => G.neighborFinset v) \ degreeTwo G

/-- Leaves of a graph T, measured using degrees in T. -/
def leaves (T : SimpleGraph V) [DecidableRel T.Adj] : Finset V :=
  univ.filter fun v => T.degree v = 1

/-- Maximum leaf count over trees on the same vertex type whose edges
belong to G. The finite supremum uses zero for the remaining graphs. -/
noncomputable def maxLeafNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact (univ : Finset (SimpleGraph V)).sup fun T =>
    if T ≤ G ∧ T.IsTree then (leaves T).card else 0

end

/-- The minimum size of a vertex set D such that every vertex, including
each member of D, has a neighbor in D. -/
noncomputable def totalDominationNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ D : Finset V, D.card = k ∧ ∀ v, ∃ d ∈ D, G.Adj v d}

/-- Graffiti.pc Conjecture 261, using rational division. -/
theorem conjecture261_ratio {V : Type*} [Fintype V] [Nontrivial V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (connected : G.Connected) :
    (2 * ((degreeTwoExternalNeighbors G).card : ℚ)) / (maxLeafNumber G : ℚ) ≤
      (totalDominationNumber G : ℚ) := by
  sorry

end WOW261
