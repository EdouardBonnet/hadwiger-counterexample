import Lax342547.NoCoverRank
import Lax342547.ComponentDuals

/-!
---
title: No-cover rank growth on arbitrary finite indices
type: lemma
---
The componentwise no-cover bound depends on the finite sample cardinality and applies to any index type of the prescribed dyadic size, including even moment samples.
-/

namespace Lax342547.IndexedRankGrowth

open Lax342547.ComponentSpaces Lax342547.ComponentDuals Lax342547.CoverProjection
open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

axiom component_no_cover_rank_indexed {K e Ω ι : Type} [Field K] [Fintype e] [DecidableEq e] [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {V W : e → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (V i)] [∀ i, FiniteDimensional K (W i)]
    (μ : Ω → ℝ) (M : Ω → ∀ i, V i →ₗ[K] W i) (r k : ℕ) (p : ℝ)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r)
    (hM : ∀ x, ∑ i, Module.finrank K (LinearMap.range (M x i)) ≤ r)
    (hk : 100*r+10 ≤ k) (hcard : Fintype.card ι = 2^k)
    (hcover : ∀ S : Submodule K (∀ i, W i), ∀ T : Submodule K (Module.Dual K (∀ i, V i)),
      Componentwise S → DualComponentwise T →
      (Module.finrank K S : ℝ) ≤ (r : ℝ)*Fintype.card ι →
      (Module.finrank K T : ℝ) ≤ (r : ℝ)*Fintype.card ι →
      cellMass μ (fun x => projection (LinearMap.piMap (M x)) S T = 0) ≤ p) :
    cellMass (productLaw (fun _ : ι => μ))
      (fun sample => ((∑ i, Module.finrank K (LinearMap.range (∑ j : ι, M (sample j) i))) : ℝ) <
        (2^(k-(100*r+10)) : ℝ)/4) ≤
      (4 : ℝ)^Fintype.card ι*p^(2^(k-(100*r+10)))

end Lax342547.IndexedRankGrowth
