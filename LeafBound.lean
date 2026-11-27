module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace WOW261

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V]

/-- Vertices of degree one in a finite simple graph. -/
def leaves (T : SimpleGraph V) [DecidableRel T.Adj] : Finset V :=
  univ.filter fun v => T.degree v = 1

/-- Any tree in which `D` totally dominates has at least `|V| + 2 - 2|D|` leaves. -/
theorem leaf_lower_of_totalDomination (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (D : Finset V) (dom : ∀ v, ∃ d ∈ D, T.Adj v d) :
    Fintype.card V + 2 ≤ (leaves T).card + 2 * D.card := by
  classical
  have covered : univ ⊆ D.biUnion (fun v => T.neighborFinset v) := by
    intro v _
    obtain ⟨d, hd, hvd⟩ := dom v
    exact mem_biUnion.mpr ⟨d, hd, (T.mem_neighborFinset d v).mpr hvd.symm⟩
  have insideSum : Fintype.card V ≤ ∑ d ∈ D, T.degree d := by
    calc
      Fintype.card V = (univ : Finset V).card := card_univ.symm
      _ ≤ (D.biUnion fun v => T.neighborFinset v).card := card_mono covered
      _ ≤ ∑ d ∈ D, T.degree d := by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
          (card_biUnion_le (s := D) (t := fun v => T.neighborFinset v))

  let outside : Finset V := univ \ D
  have outsideCard : outside.card + D.card = Fintype.card V := by
    simpa only [outside, card_univ] using card_sdiff_add_card_eq_card (subset_univ D)
  have splitSum :
      (∑ v ∈ outside, T.degree v) + (∑ v ∈ D, T.degree v) = ∑ v, T.degree v :=
    sum_sdiff (subset_univ D)
  have degreeSum : (∑ v, T.degree v) + 2 = 2 * Fintype.card V := by
    have edges := hT.card_edgeFinset
    rw [T.sum_degrees_eq_twice_card_edges]
    omega

  have leavesOutside : (outside.filter fun v => T.degree v = 1).card ≤ (leaves T).card := by
    apply card_mono
    intro v hv
    exact mem_filter.mpr ⟨mem_univ v, (mem_filter.mp hv).2⟩
  have outsideLeafSum :
      (∑ v ∈ outside, (if T.degree v = 1 then 1 else 0 : ℕ)) =
        (outside.filter fun v => T.degree v = 1).card := by
    rw [← sum_filter]
    simp
  have outsideLower : 2 * outside.card ≤ (∑ v ∈ outside, T.degree v) + (leaves T).card := by
    calc
      2 * outside.card = ∑ _ ∈ outside, (2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ outside, (T.degree v + if T.degree v = 1 then 1 else 0) := by
        apply sum_le_sum
        intro v _
        have positive : 0 < T.degree v := by
          obtain ⟨d, _, hd⟩ := dom v
          exact hd.degree_pos_left
        split <;> omega
      _ = (∑ v ∈ outside, T.degree v) + (outside.filter fun v => T.degree v = 1).card := by
        rw [sum_add_distrib, outsideLeafSum]
      _ ≤ (∑ v ∈ outside, T.degree v) + (leaves T).card := Nat.add_le_add_left leavesOutside _
  omega

end WOW261
