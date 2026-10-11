import Lax342547.BlockDeficits
import Lax342547.DirectRanks
import Lax342547.RankLoss
import Lax342547.SpanDeficits

namespace Lax342547Proofs.BlockDeficits
open Lax342547.BlockDeficits

set_option backward.isDefEq.respectTransparency false
open Lax342547.SpanDeficits
open scoped BigOperators

/--
---
conclusion: Lax342547.BlockDeficits.lifted_sum_rank_deficit
---
-/
theorem lifted_sum_rank_deficit {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : ι → Submodule K W) (T : ι → Submodule K V)
    (M : ∀ i, Module.Dual K (T i) →ₗ[K] S i) :
    (∑ i, Module.finrank K (LinearMap.range (M i))) ≤
      Module.finrank K (LinearMap.range (liftedSum S T M)) +
      ((∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K W)) +
      ((∑ i, Module.finrank K (T i))-Module.finrank K (⨆ i, T i : Submodule K V)) := by
  classical
  let E : (∀ i, Module.Dual K (T i)) ≃ₗ[K] Module.Dual K (∀ i, T i) :=
    LinearMap.lsum K (fun i => T i) K
  let B := E.symm.toLinearMap.comp (addition T).dualMap
  have hB : Module.finrank K (LinearMap.range B) = Module.finrank K (⨆ i, T i : Submodule K V) := by
    dsimp [B]
    rw [LinearMap.range_comp,LinearEquiv.finrank_map_eq,
      LinearMap.finrank_range_dualMap_eq_finrank_range,Lax342547.SpanDeficits.addition_range]
  have hdom : Module.finrank K (∀ i, Module.Dual K (T i)) = ∑ i, Module.finrank K (T i) := by
    rw [Module.finrank_pi_fintype]
    simp only [Subspace.dual_finrank_eq]
  have hh := Lax342547.RankLoss.composition_rank_loss (addition S) (LinearMap.piMap M) B
  rw [Lax342547.DirectRanks.diagonal_rank_sum,Lax342547.SpanDeficits.addition_kernel_deficit,hdom,hB] at hh
  exact hh

/--
---
conclusion: Lax342547.BlockDeficits.nonzero_map_rank
---
-/
theorem nonzero_map_rank {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (M : V →ₗ[K] W) (hM : M ≠ 0) :
    1 ≤ Module.finrank K (LinearMap.range M) := by
  by_contra hn
  have hz : Module.finrank K (LinearMap.range M) = 0 := by omega
  exact hM (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))

/--
---
conclusion: Lax342547.BlockDeficits.nonzero_block_count_deficit
---
-/
theorem nonzero_block_count_deficit {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : ι → Submodule K W) (T : ι → Submodule K V)
    (M : ∀ i, Module.Dual K (T i) →ₗ[K] S i) : by
      classical
      exact (Finset.univ.filter (fun i => M i ≠ 0)).card ≤
        Module.finrank K (LinearMap.range (liftedSum S T M)) +
        ((∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K W)) +
        ((∑ i, Module.finrank K (T i))-Module.finrank K (⨆ i, T i : Submodule K V)) := by
  classical
  have hcount : (Finset.univ.filter (fun i => M i ≠ 0)).card ≤ ∑ i, Module.finrank K (LinearMap.range (M i)) := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · exact Lax342547.BlockDeficits.nonzero_map_rank (M i) hi
    · exact Nat.zero_le _
  exact hcount.trans (Lax342547.BlockDeficits.lifted_sum_rank_deficit S T M)

end Lax342547Proofs.BlockDeficits
