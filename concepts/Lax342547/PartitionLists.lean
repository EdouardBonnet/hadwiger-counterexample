import Lax342547.SmallExposure

/-!
---
title: Finite exposure partitions
type: lemma
---
A distinct ordering splits into disjoint exposed and remaining index sets, with their exact union and tail cardinality.
-/

namespace Lax342547.PartitionLists



axiom take_drop_disjoint {ι : Type} [DecidableEq ι] (l : List ι) (hl : l.Nodup) (t : ℕ) :
    Disjoint (l.take t).toFinset (l.drop t).toFinset

axiom take_drop_union {ι : Type} [DecidableEq ι] (l : List ι) (t : ℕ) :
    (l.take t).toFinset ∪ (l.drop t).toFinset = l.toFinset

axiom take_drop_card {ι : Type} [DecidableEq ι] (l : List ι) (hl : l.Nodup)
    (b : ℕ) (hb : b ≤ l.length) : (l.drop (l.length-b)).toFinset.card = b

end Lax342547.PartitionLists
