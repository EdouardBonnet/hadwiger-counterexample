import Lax342547.IndexedRankGrowth
import Lax342547Proofs.NoCoverRank
import Lax342547Proofs.ComponentDuals

namespace Lax342547Proofs.IndexedRankGrowth
open Lax342547.IndexedRankGrowth

set_option backward.isDefEq.respectTransparency false
open Lax342547.ComponentSpaces Lax342547.ComponentDuals Lax342547.CoverProjection
open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.IndexedRankGrowth.component_no_cover_rank_indexed
---
-/
theorem component_no_cover_rank_indexed {K e Ω ι : Type} [Field K] [Fintype e] [DecidableEq e] [Fintype Ω] [Fintype ι] [DecidableEq ι]
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
      (4 : ℝ)^Fintype.card ι*p^(2^(k-(100*r+10))) := by
  classical
  have hC : ∀ x, Componentwise (LinearMap.range (LinearMap.piMap (M x))) := by
    intro x
    exact ⟨fun i => LinearMap.range (M x i),Lax342547Proofs.ComponentSpaces.diagonal_range _⟩
  have hR : ∀ x, DualComponentwise (LinearMap.range (LinearMap.piMap (M x)).dualMap) := by
    intro x
    unfold DualComponentwise
    rw [Lax342547Proofs.ComponentDuals.diagonal_dual_range]
    exact ⟨_,rfl⟩
  have hsum (sample : ι → Ω) : (∑ j, LinearMap.piMap (M (sample j))) =
      LinearMap.piMap (fun i => ∑ j, M (sample j) i) := by
    ext v i
    simp
  have h := Lax342547Proofs.NoCoverRank.no_cover_rank_probability (ι := ι) μ
    (fun x => LinearMap.piMap (M x)) Componentwise DualComponentwise (r : ℝ) p k (100*r+10)
    hμ hp0 hp1 (by positivity)
    (fun x => by rw [Lax342547Proofs.DirectRanks.diagonal_rank_sum]; exact_mod_cast hM x)
    Lax342547Proofs.ComponentSpaces.componentwise_join_closed
    Lax342547Proofs.ComponentDuals.dual_componentwise_join_closed hC hR
    hcard hk (by push_cast; linarith)
    (by
      intro S T hS hT hdS hdT
      exact hcover S T hS hT
        hdS
        hdT)
  have he (sample : ι → Ω) : Module.finrank K (LinearMap.range (∑ j, LinearMap.piMap (M (sample j)))) =
      ∑ i, Module.finrank K (LinearMap.range (∑ j, M (sample j) i)) := by
    rw [hsum,Lax342547Proofs.DirectRanks.diagonal_rank_sum]
  simpa only [he,Nat.cast_sum] using h

end Lax342547Proofs.IndexedRankGrowth
