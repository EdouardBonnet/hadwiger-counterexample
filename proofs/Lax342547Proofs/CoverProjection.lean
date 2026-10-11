import Lax342547.CoverProjection
import Lax342547Proofs.ProjectedSpans
import Lax342547Proofs.RankLoss

namespace Lax342547Proofs.CoverProjection
open Lax342547.CoverProjection

set_option backward.isDefEq.respectTransparency false
open Lax342547.GreedySpans
open scoped BigOperators

/--
---
conclusion: Lax342547.CoverProjection.cover_restriction_kernel
---
-/
theorem cover_restriction_kernel {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Submodule K (Module.Dual K V)) :
    LinearMap.ker T.dualCoannihilator.subtype.dualMap = T := by
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range,Submodule.range_subtype,Subspace.dualCoannihilator_dualAnnihilator_eq]

/--
---
conclusion: Lax342547.CoverProjection.projected_column_envelope
---
-/
theorem projected_column_envelope {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (M : V →ₗ[K] W)
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    LinearMap.range (projection M S T) ≤ (LinearMap.range M).map S.mkQ := by
  rw [projection,LinearMap.range_comp]
  apply Submodule.map_mono
  rw [LinearMap.range_comp]
  rintro v ⟨x,hx,rfl⟩
  exact LinearMap.mem_range_self _ x

/--
---
conclusion: Lax342547.CoverProjection.projected_row_envelope
---
-/
theorem projected_row_envelope {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (M : V →ₗ[K] W)
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    LinearMap.range (projection M S T).dualMap ≤
      (LinearMap.range M.dualMap).map T.dualCoannihilator.subtype.dualMap := by
  rw [projection,← LinearMap.dualMap_comp_dualMap,← LinearMap.dualMap_comp_dualMap,
    LinearMap.range_comp,Submodule.map_comp]
  apply Submodule.map_mono
  rintro v ⟨x,hx,rfl⟩
  exact LinearMap.mem_range_self _ x

/--
---
conclusion: Lax342547.CoverProjection.projection_rank_le
---
-/
theorem projection_rank_le {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (M : V →ₗ[K] W) (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    Module.finrank K (LinearMap.range (projection M S T)) ≤ Module.finrank K (LinearMap.range M) := by
  apply (Submodule.finrank_mono (projected_column_envelope M S T)).trans
  exact Submodule.finrank_map_le _ _

/--
---
conclusion: Lax342547.CoverProjection.projection_zero_of_columns
---
-/
theorem projection_zero_of_columns {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (M : V →ₗ[K] W)
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) (h : LinearMap.range M ≤ S) :
    projection M S T = 0 := by
  ext v
  change S.mkQ (M v.val) = 0
  apply LinearMap.mem_ker.mp
  rw [Submodule.ker_mkQ]
  exact h (LinearMap.mem_range_self _ _)

/--
---
conclusion: Lax342547.CoverProjection.projection_sum
---
-/
theorem projection_sum {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : ι → V →ₗ[K] W) (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    projection (∑ i, M i) S T = ∑ i, projection (M i) S T := by
  ext v
  simp [projection]

end Lax342547Proofs.CoverProjection
