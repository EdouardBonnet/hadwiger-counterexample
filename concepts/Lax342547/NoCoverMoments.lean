import Lax342547.ComponentMoments
import Lax342547.IndexedRankGrowth

/-!
---
title: No-cover phase moments
type: definition and theorem
---
Actual componentwise binary channel moments and phase-tail bounds from finite rank growth, under the explicit small-cover exclusion.
-/

namespace Lax342547.NoCoverMoments

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open Lax342547.ChannelCharacters Lax342547.TensorCharacters Lax342547.ComponentSpaces
open Lax342547.ComponentDuals Lax342547.CoverProjection
open scoped BigOperators

axiom sum_matrix_rank {I J ι : Type} [Fintype I] [Fintype J] [Fintype ι]
    (A : ι → Matrix I J Binary) :
    Module.finrank Binary (LinearMap.range (∑ i, (A i).mulVecLin)) = (∑ i, A i).rank

axiom no_cover_even_moment {e I J Ω : Type} [Fintype e] [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq e] [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → e → Matrix I J Binary) (ψ : Ω → ℝ) (r h t k : ℕ) (p : ℝ)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r)
    (hA : ∀ x, ∑ i, (A x i).rank ≤ r) (hψ : ∀ x, |ψ x| ≤ 1)
    (hsize : 2*t = 2^k) (hk : 100*r+12 ≤ k)
    (hcover : ∀ S : Submodule Binary (e → I → Binary),
      ∀ T : Submodule Binary (Module.Dual Binary (e → J → Binary)),
      Componentwise S → DualComponentwise T →
      (Module.finrank Binary S : ℝ) ≤ (r : ℝ)*(2*t) →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(2*t) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) S T = 0) ≤ p) :
    (∑ c, productLaw (fun _ : e × Fin h => channelLaw) c*
      |∑ x, μ x*ψ x*tensorCharacter h (A x) c|^(2*t)) ≤
      (4 : ℝ)^(2*t)*p^(2^(k-(100*r+10)))+1/(2 : ℝ)^(h*2^(k-(100*r+12)))

axiom no_cover_phase_tail {e I J Ω : Type} [Fintype e] [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq e] [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → e → Matrix I J Binary) (ψ : Ω → ℝ) (r h t k : ℕ) (p θ : ℝ)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r)
    (hA : ∀ x, ∑ i, (A x i).rank ≤ r) (hψ : ∀ x, |ψ x| ≤ 1)
    (hsize : 2*t = 2^k) (hk : 100*r+12 ≤ k)
    (hcover : ∀ S : Submodule Binary (e → I → Binary),
      ∀ T : Submodule Binary (Module.Dual Binary (e → J → Binary)),
      Componentwise S → DualComponentwise T →
      (Module.finrank Binary S : ℝ) ≤ (r : ℝ)*(2*t) →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(2*t) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) S T = 0) ≤ p)
    (hθ : 0 < θ) :
    cellMass (productLaw (fun _ : e × Fin h => channelLaw))
      (fun c => θ ≤ |∑ x, μ x*ψ x*tensorCharacter h (A x) c|) ≤
      ((4 : ℝ)^(2*t)*p^(2^(k-(100*r+10)))+1/(2 : ℝ)^(h*2^(k-(100*r+12))))/θ^(2*t)

end Lax342547.NoCoverMoments
