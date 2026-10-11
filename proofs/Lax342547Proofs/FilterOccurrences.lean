import Lax342547.FilterOccurrences
import Lax342547Proofs.CoverCounts

namespace Lax342547Proofs.FilterOccurrences
open Lax342547.FilterOccurrences

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.FilterOccurrences.filter_subtype_card
---
-/
theorem filter_subtype_card {ι : Type} [DecidableEq ι] (I : Finset ι) (P : ι → Prop) : by
    classical
    exact (Finset.univ.filter (fun i : I => P i.val)).card = (I.filter P).card := by
  classical
  rw [Finset.card_filter,Finset.card_filter,
    Finset.sum_coe_sort I (fun i => if P i then (1 : ℕ) else 0)]

end Lax342547Proofs.FilterOccurrences
