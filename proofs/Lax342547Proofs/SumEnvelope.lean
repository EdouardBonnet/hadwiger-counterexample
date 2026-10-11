import Lax342547.SumEnvelope
import Lax342547Proofs.SumRank
import Lax342547Proofs.SpanDeficitMono
import Mathlib.Data.Real.Basic

namespace Lax342547Proofs.SumEnvelope
open Lax342547.SumEnvelope

set_option backward.isDefEq.respectTransparency false
open Lax342547.SpanDeficits
open scoped BigOperators

/--
---
conclusion: Lax342547.SumEnvelope.span_dimension_sum_bound
---
-/
theorem span_dimension_sum_bound {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : ι → Submodule K V) :
    Module.finrank K (⨆ i, S i : Submodule K V) ≤ ∑ i, Module.finrank K (S i) := by
  have hh := (addition S).finrank_range_add_finrank_ker
  rw [Lax342547Proofs.SpanDeficits.addition_range,Module.finrank_pi_fintype] at hh
  omega

/--
---
conclusion: Lax342547.SumEnvelope.natural_deficit_cast
---
-/
theorem natural_deficit_cast {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : ι → Submodule K V) :
    (((∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K V) : ℕ) : ℝ) =
      dimensionDeficit S := by
  rw [Nat.cast_sub (span_dimension_sum_bound S),Nat.cast_sum]
  rfl

/--
---
conclusion: Lax342547.SumEnvelope.nonzero_sum_envelope
---
-/
theorem nonzero_sum_envelope {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : ι → V →ₗ[K] W) (S : ι → Submodule K W) (T : ι → Submodule K (Module.Dual K V))
    (hS : ∀ i, LinearMap.range (M i) ≤ S i) (hT : ∀ i, LinearMap.range (M i).dualMap ≤ T i) : by
      classical
      exact ((Finset.univ.filter (fun i => M i ≠ 0)).card : ℝ) ≤
        Module.finrank K (LinearMap.range (∑ i, M i))+dimensionDeficit S+dimensionDeficit T := by
  classical
  have hr := Lax342547Proofs.SumRank.sum_rank_deficit M S hS
  have ht := Lax342547Proofs.SpanDeficitMono.deficit_monotone (fun i => LinearMap.range (M i).dualMap) T hT
  have hc : (Finset.univ.filter (fun i => M i ≠ 0)).card ≤ ∑ i, Module.finrank K (LinearMap.range (M i)) := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · exact Lax342547Proofs.BlockDeficits.nonzero_map_rank (M i) hi
    · exact Nat.zero_le _
  have hn : (Finset.univ.filter (fun i => M i ≠ 0)).card ≤
      Module.finrank K (LinearMap.range (∑ i, M i))+
      ((∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K W))+
      ((∑ i, Module.finrank K (T i))-Module.finrank K (⨆ i, T i : Submodule K (Module.Dual K V))) := by omega
  have hn' := (Nat.cast_le (α := ℝ)).mpr hn
  push_cast at hn'
  rw [natural_deficit_cast,natural_deficit_cast] at hn'
  exact hn'

end Lax342547Proofs.SumEnvelope
