import Lax342547.SumRank
import Lax342547.SpanDeficitMono
import Mathlib.Data.Real.Basic

/-!
---
title: Nonzero tensor count from span deficits
type: definition and theorem
---
For the actual sum of maps, column and row envelopes bound the number of nonzero terms by the sum rank plus their two actual dimension deficits.
-/

namespace Lax342547.SumEnvelope

open Lax342547.SpanDeficits
open scoped BigOperators

noncomputable def dimensionDeficit {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : ι → Submodule K V) : ℝ :=
    (∑ i, (Module.finrank K (S i) : ℝ))-Module.finrank K (⨆ i, S i : Submodule K V)

axiom span_dimension_sum_bound {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : ι → Submodule K V) :
    Module.finrank K (⨆ i, S i : Submodule K V) ≤ ∑ i, Module.finrank K (S i)

axiom natural_deficit_cast {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : ι → Submodule K V) :
    (((∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K V) : ℕ) : ℝ) =
      dimensionDeficit S

axiom nonzero_sum_envelope {K V W ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : ι → V →ₗ[K] W) (S : ι → Submodule K W) (T : ι → Submodule K (Module.Dual K V))
    (hS : ∀ i, LinearMap.range (M i) ≤ S i) (hT : ∀ i, LinearMap.range (M i).dualMap ≤ T i) : by
      classical
      exact ((Finset.univ.filter (fun i => M i ≠ 0)).card : ℝ) ≤
        Module.finrank K (LinearMap.range (∑ i, M i))+dimensionDeficit S+dimensionDeficit T

end Lax342547.SumEnvelope
