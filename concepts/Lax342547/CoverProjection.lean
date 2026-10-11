import Lax342547.ProjectedSpans
import Lax342547.RankLoss

/-!
---
title: Actual exposure cover projection
type: definition and theorem
---
Quotienting the exposed columns and restricting to the annihilator of exposed rows gives the actual covered-tensor projection, its mode envelopes, rank monotonicity, and sum identity.
-/

namespace Lax342547.CoverProjection

open Lax342547.GreedySpans
open scoped BigOperators

noncomputable def projection {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (M : V →ₗ[K] W)
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    T.dualCoannihilator →ₗ[K] (W ⧸ S) := S.mkQ.comp (M.comp T.dualCoannihilator.subtype)

axiom cover_restriction_kernel {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Submodule K (Module.Dual K V)) :
    LinearMap.ker T.dualCoannihilator.subtype.dualMap = T

axiom projected_column_envelope {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (M : V →ₗ[K] W)
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    LinearMap.range (projection M S T) ≤ (LinearMap.range M).map S.mkQ

axiom projected_row_envelope {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (M : V →ₗ[K] W)
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    LinearMap.range (projection M S T).dualMap ≤
      (LinearMap.range M.dualMap).map T.dualCoannihilator.subtype.dualMap

axiom projection_rank_le {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (M : V →ₗ[K] W) (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    Module.finrank K (LinearMap.range (projection M S T)) ≤ Module.finrank K (LinearMap.range M)

axiom projection_zero_of_columns {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (M : V →ₗ[K] W)
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) (h : LinearMap.range M ≤ S) :
    projection M S T = 0

axiom projection_sum {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : ι → V →ₗ[K] W) (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    projection (∑ i, M i) S T = ∑ i, projection (M i) S T

end Lax342547.CoverProjection
