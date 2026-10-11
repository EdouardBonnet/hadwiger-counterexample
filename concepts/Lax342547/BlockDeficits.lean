import Lax342547.RankLoss
import Lax342547.DirectRanks
import Lax342547.SpanDeficits

/-!
---
title: Rank of a lifted tensor sum
type: definition and theorem
---
A lifted block sum has rank at least its number of nonzero blocks minus the actual column and row span deficits.
-/

namespace Lax342547.BlockDeficits

open Lax342547.SpanDeficits
open scoped BigOperators

noncomputable def liftedSum {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : ι → Submodule K W) (T : ι → Submodule K V)
    (M : ∀ i, Module.Dual K (T i) →ₗ[K] S i) : Module.Dual K V →ₗ[K] W := by
  classical
  let B := (LinearMap.lsum K (fun i => T i) K).symm.toLinearMap.comp (addition T).dualMap
  exact (addition S).comp ((LinearMap.piMap M).comp B)

axiom lifted_sum_rank_deficit {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : ι → Submodule K W) (T : ι → Submodule K V)
    (M : ∀ i, Module.Dual K (T i) →ₗ[K] S i) :
    (∑ i, Module.finrank K (LinearMap.range (M i))) ≤
      Module.finrank K (LinearMap.range (liftedSum S T M)) +
      ((∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K W)) +
      ((∑ i, Module.finrank K (T i))-Module.finrank K (⨆ i, T i : Submodule K V))

axiom nonzero_map_rank {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (M : V →ₗ[K] W) (hM : M ≠ 0) :
    1 ≤ Module.finrank K (LinearMap.range M)

axiom nonzero_block_count_deficit {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : ι → Submodule K W) (T : ι → Submodule K V)
    (M : ∀ i, Module.Dual K (T i) →ₗ[K] S i) : by
      classical
      exact (Finset.univ.filter (fun i => M i ≠ 0)).card ≤
        Module.finrank K (LinearMap.range (liftedSum S T M)) +
        ((∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K W)) +
        ((∑ i, Module.finrank K (T i))-Module.finrank K (⨆ i, T i : Submodule K V))

end Lax342547.BlockDeficits
