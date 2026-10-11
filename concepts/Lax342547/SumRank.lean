import Lax342547.SpanDeficits
import Lax342547.RestrictionRank
import Lax342547.BlockDeficits

/-!
---
title: Rank of an actual linear map sum
type: definition and theorem
---
Stacking maps identifies the joint row span, and addition loses at most the actual mode-space deficit. This gives the rank-deficit inequality for the actual sum.
-/

namespace Lax342547.SumRank

open Lax342547.SpanDeficits
open scoped BigOperators

axiom stacked_rank {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : ι → V →ₗ[K] W) (S : ι → Submodule K W) (hS : ∀ i, LinearMap.range (M i) ≤ S i) :
    Module.finrank K (LinearMap.range (LinearMap.pi (fun i => (M i).codRestrict (S i)
      (fun v => hS i (LinearMap.mem_range_self _ v))))) =
      Module.finrank K (⨆ i, LinearMap.range (M i).dualMap : Submodule K (Module.Dual K V))

axiom sum_rank_deficit {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : ι → V →ₗ[K] W) (S : ι → Submodule K W) (hS : ∀ i, LinearMap.range (M i) ≤ S i) :
    (∑ i, Module.finrank K (LinearMap.range (M i))) ≤
      Module.finrank K (LinearMap.range (∑ i, M i))+
      ((∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K W))+
      ((∑ i, Module.finrank K (LinearMap.range (M i).dualMap))-
        Module.finrank K (⨆ i, LinearMap.range (M i).dualMap : Submodule K (Module.Dual K V)))

end Lax342547.SumRank
