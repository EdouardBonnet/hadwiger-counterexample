import Lax342547.ProjectedCounts
import Lax342547.CoverProjection
import Lax342547.ListDeficits
import Lax342547.MappedSpans
import Lax342547.SumEnvelope

namespace Lax342547Proofs.ProjectedCounts
open Lax342547.ProjectedCounts

set_option backward.isDefEq.respectTransparency false
open Lax342547.CoverProjection Lax342547.GreedyTails
open scoped BigOperators

/--
---
conclusion: Lax342547.ProjectedCounts.projected_nonzero_count
---
-/
theorem projected_nonzero_count {K V W ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : ι → V →ₗ[K] W) (S : Submodule K W) (T : Submodule K (Module.Dual K V))
    (l : List ι) (hl : l.Nodup) : by
      classical
      exact ((Finset.univ.filter (fun i : l.toFinset => projection (M i.val) S T ≠ 0)).card : ℝ) ≤
        Module.finrank K (LinearMap.range (projection (∑ i : l.toFinset, M i.val) S T))+
        deficit (fun i => LinearMap.range (M i)) S l+
        deficit (fun i => LinearMap.range (M i).dualMap) T l := by
  classical
  let C := fun i => LinearMap.range (M i)
  let R := fun i => LinearMap.range (M i).dualMap
  have hh := Lax342547.SumEnvelope.nonzero_sum_envelope
    (fun i : l.toFinset => projection (M i.val) S T)
    (fun i : l.toFinset => (C i.val).map S.mkQ)
    (fun i : l.toFinset => (R i.val).map T.dualCoannihilator.subtype.dualMap)
    (fun i => Lax342547.CoverProjection.projected_column_envelope (M i.val) S T)
    (fun i => Lax342547.CoverProjection.projected_row_envelope (M i.val) S T)
  rw [Lax342547.ListDeficits.list_mapped_deficit C S.mkQ l hl,
    Lax342547.ListDeficits.list_mapped_deficit R T.dualCoannihilator.subtype.dualMap l hl,
    Lax342547.MappedSpans.mapped_deficit_eq,
    Lax342547.MappedSpans.mapped_deficit_eq,
    Submodule.ker_mkQ,Lax342547.CoverProjection.cover_restriction_kernel,
    ← Lax342547.CoverProjection.projection_sum] at hh
  exact hh

end Lax342547Proofs.ProjectedCounts
