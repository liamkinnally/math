module

public import LeafBound

@[expose] public section

namespace WOW261

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [Nontrivial V]

/-- In a finite nontrivial tree, the degree of any vertex is at most the number of leaves. -/
theorem degree_le_leaves_of_tree (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (v : V) : T.degree v ≤ (leaves T).card := by
  classical
  let other := (univ : Finset V).erase v
  have cardOther : other.card + 1 = Fintype.card V := by
    simpa only [other, card_univ] using (card_erase_add_one (mem_univ v))
  have degreeSum : (∑ w, T.degree w) + 2 = 2 * Fintype.card V := by
    have edges := hT.card_edgeFinset
    rw [T.sum_degrees_eq_twice_card_edges]
    omega
  have splitSum : (∑ w ∈ other, T.degree w) + T.degree v = ∑ w, T.degree w :=
    sum_erase_add (univ : Finset V) (fun w => T.degree w) (mem_univ v)
  have leavesOther : (other.filter fun w => T.degree w = 1).card ≤ (leaves T).card := by
    apply card_mono
    intro w hw
    exact mem_filter.mpr ⟨mem_univ w, (mem_filter.mp hw).2⟩
  have otherLeafSum :
      (∑ w ∈ other, (if T.degree w = 1 then 1 else 0 : ℕ)) =
        (other.filter fun w => T.degree w = 1).card := by
    rw [← sum_filter]
    simp
  have otherLower : 2 * other.card ≤ (∑ w ∈ other, T.degree w) + (leaves T).card := by
    calc
      2 * other.card = ∑ _ ∈ other, (2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ w ∈ other, (T.degree w + if T.degree w = 1 then 1 else 0) := by
        apply sum_le_sum
        intro w _
        obtain ⟨u, huw⟩ := hT.preconnected.exists_adj_of_nontrivial w
        have positive : 0 < T.degree w := huw.degree_pos_left
        split <;> omega
      _ = (∑ w ∈ other, T.degree w) + (other.filter fun w => T.degree w = 1).card := by
        rw [sum_add_distrib, otherLeafSum]
      _ ≤ (∑ w ∈ other, T.degree w) + (leaves T).card := Nat.add_le_add_left leavesOther _
  omega

end WOW261
