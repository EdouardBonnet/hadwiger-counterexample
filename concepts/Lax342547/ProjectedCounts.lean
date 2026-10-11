import Lax342547.ListDeficits
import Lax342547.CoverProjection

/-!
---
title: Projected nonzero terms in the actual remaining sum
type: lemma
---
The rank-deficit inequality applied to actual column quotients and row restrictions bounds nonzero remaining terms by the projected sum rank and both original-space exposure deficits.
-/

namespace Lax342547.ProjectedCounts

open Lax342547.CoverProjection Lax342547.GreedyTails
open scoped BigOperators

axiom projected_nonzero_count {K V W ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : ι → V →ₗ[K] W) (S : Submodule K W) (T : Submodule K (Module.Dual K V))
    (l : List ι) (hl : l.Nodup) : by
      classical
      exact ((Finset.univ.filter (fun i : l.toFinset => projection (M i.val) S T ≠ 0)).card : ℝ) ≤
        Module.finrank K (LinearMap.range (projection (∑ i : l.toFinset, M i.val) S T))+
        deficit (fun i => LinearMap.range (M i)) S l+
        deficit (fun i => LinearMap.range (M i).dualMap) T l

end Lax342547.ProjectedCounts
