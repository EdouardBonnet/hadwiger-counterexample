import Lax342547.NoCoverRank
import Lax342547.ComponentDuals

/-!
---
title: Componentwise no-cover rank growth
type: lemma
---
At the paper rank and dyadic size budgets, the full no-cover rank bound applies to actual diagonal component tensors, with the sum of their component ranks and componentwise exposed mode spaces.
-/

namespace Lax342547.ComponentRankGrowth

open Lax342547.ComponentSpaces Lax342547.ComponentDuals Lax342547.CoverProjection
open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

axiom component_no_cover_rank {K e Ω : Type} [Field K] [Fintype e] [DecidableEq e] [Fintype Ω]
    {V W : e → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (V i)] [∀ i, FiniteDimensional K (W i)]
    (μ : Ω → ℝ) (M : Ω → ∀ i, V i →ₗ[K] W i) (r k : ℕ) (p : ℝ)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r)
    (hM : ∀ x, ∑ i, Module.finrank K (LinearMap.range (M x i)) ≤ r)
    (hk : 100*r+10 ≤ k)
    (hcover : ∀ S : Submodule K (∀ i, W i), ∀ T : Submodule K (Module.Dual K (∀ i, V i)),
      Componentwise S → DualComponentwise T →
      (Module.finrank K S : ℝ) ≤ (r : ℝ)*2^k →
      (Module.finrank K T : ℝ) ≤ (r : ℝ)*2^k →
      cellMass μ (fun x => projection (LinearMap.piMap (M x)) S T = 0) ≤ p) :
    cellMass (productLaw (fun _ : Fin (2^k) => μ))
      (fun sample => ((∑ i, Module.finrank K (LinearMap.range (∑ j : Fin (2^k), M (sample j) i))) : ℝ) <
        (2^(k-(100*r+10)) : ℝ)/4) ≤
      (4 : ℝ)^(2^k)*p^(2^(k-(100*r+10)))

end Lax342547.ComponentRankGrowth
