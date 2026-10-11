import Lax342547.PartitionLists
import Lax342547Proofs.SmallExposure

namespace Lax342547Proofs.PartitionLists
open Lax342547.PartitionLists

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.PartitionLists.take_drop_disjoint
---
-/
theorem take_drop_disjoint {ι : Type} [DecidableEq ι] (l : List ι) (hl : l.Nodup) (t : ℕ) :
    Disjoint (l.take t).toFinset (l.drop t).toFinset := by
  have hh : ((l.take t)++l.drop t).Nodup := by rw [List.take_append_drop]; exact hl
  have hd := List.disjoint_of_nodup_append hh
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hd (List.mem_toFinset.mp hi) (List.mem_toFinset.mp hj)

/--
---
conclusion: Lax342547.PartitionLists.take_drop_union
---
-/
theorem take_drop_union {ι : Type} [DecidableEq ι] (l : List ι) (t : ℕ) :
    (l.take t).toFinset ∪ (l.drop t).toFinset = l.toFinset := by
  rw [← List.toFinset_append,List.take_append_drop]

/--
---
conclusion: Lax342547.PartitionLists.take_drop_card
---
-/
theorem take_drop_card {ι : Type} [DecidableEq ι] (l : List ι) (hl : l.Nodup)
    (b : ℕ) (hb : b ≤ l.length) : (l.drop (l.length-b)).toFinset.card = b := by
  rw [List.toFinset_card_of_nodup (hl.drop),List.length_drop,Nat.sub_sub_self hb]

end Lax342547Proofs.PartitionLists
