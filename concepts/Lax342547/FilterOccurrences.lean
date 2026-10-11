import Lax342547.CoverCounts

/-!
---
title: Count tested index occurrences
type: definition and theorem
---
Filtering subtype indices and filtering their underlying finite set have identical cardinalities.
-/

namespace Lax342547.FilterOccurrences



axiom filter_subtype_card {ι : Type} [DecidableEq ι] (I : Finset ι) (P : ι → Prop) : by
    classical
    exact (Finset.univ.filter (fun i : I => P i.val)).card = (I.filter P).card

end Lax342547.FilterOccurrences
