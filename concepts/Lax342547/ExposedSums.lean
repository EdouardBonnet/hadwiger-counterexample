import Lax342547.PartitionLists
import Lax342547.CoverProjection
import Lax342547.ListDeficits

/-!
---
title: Projection removes the exposed terms
type: definition and theorem
---
The projection of the actual remaining sum equals the projection of the full sum because the exposed column span kills each exposed term.
-/

namespace Lax342547.ExposedSums

open Lax342547.GreedySpans Lax342547.CoverProjection
open scoped BigOperators

axiom remaining_projection_sum {K V W ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : ι → V →ₗ[K] W) (l : List ι) (hl : l.Nodup) (hI : l.toFinset = Finset.univ) (t : ℕ) :
    let S := spanAfter (fun i => LinearMap.range (M i)) ⊥ (l.take t)
    let T := spanAfter (fun i => LinearMap.range (M i).dualMap) ⊥ (l.take t)
    projection (∑ i : (l.drop t).toFinset, M i.val) S T = projection (∑ i, M i) S T

end Lax342547.ExposedSums
