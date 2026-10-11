import Lax342547.TensorCharacters
import Lax342547.MomentTails

/-!
---
title: Moment estimates for actual component tensor phases
type: definition and theorem
---
The finite high moment and Markov tail are bounded by the actual summed component rank under independent uniform component channels, with arbitrary bounded unit-side signs.
-/

namespace Lax342547.ComponentMoments

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open Lax342547.ChannelCharacters Lax342547.TensorCharacters
open scoped BigOperators

axiom component_even_moment_bound {e I J Ω : Type} [Fintype e] [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq e] [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → e → Matrix I J Binary) (ψ : Ω → ℝ) (h t : ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hψ : ∀ x, |ψ x| ≤ 1) :
    (∑ c, productLaw (fun _ : e × Fin h => channelLaw) c*
      |∑ x, μ x*ψ x*tensorCharacter h (A x) c|^(2*t)) ≤
      ∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample/
        (2 : ℝ)^(h*∑ a : e, (∑ i, A (sample i) a).rank)

axiom component_phase_tail {e I J Ω : Type} [Fintype e] [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq e] [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → e → Matrix I J Binary) (ψ : Ω → ℝ) (h t : ℕ) (θ : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hψ : ∀ x, |ψ x| ≤ 1) (hθ : 0 < θ) :
    cellMass (productLaw (fun _ : e × Fin h => channelLaw))
      (fun c => θ ≤ |∑ x, μ x*ψ x*tensorCharacter h (A x) c|) ≤
      (∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample/
        (2 : ℝ)^(h*∑ a : e, (∑ i, A (sample i) a).rank))/θ^(2*t)

end Lax342547.ComponentMoments
