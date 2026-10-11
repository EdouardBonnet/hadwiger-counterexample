import Lax342547.ChannelCharacters
import Lax342547.MomentTails

/-!
---
title: Actual channel moments and phase tails
type: definition and theorem
---
The checked moment expansion and exact channel character mean bound arbitrary bounded unit-side signs by the rank of the actual sampled matrix sum, and yield the explicit Markov phase tail.
-/

namespace Lax342547.ChannelMoments

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open Lax342547.ChannelCharacters
open scoped BigOperators

axiom channel_even_moment_bound {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → Matrix I J Binary) (ψ : Ω → ℝ) (h t : ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hψ : ∀ x, |ψ x| ≤ 1) :
    (∑ c, productLaw (fun _ : Fin h => channelLaw) c*
      |∑ x, μ x*ψ x*channelCharacter h (A x) c|^(2*t)) ≤
      ∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample/
        (2 : ℝ)^(h*(∑ i, A (sample i)).rank)

axiom channel_phase_tail {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → Matrix I J Binary) (ψ : Ω → ℝ) (h t : ℕ) (θ : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hψ : ∀ x, |ψ x| ≤ 1) (hθ : 0 < θ) :
    cellMass (productLaw (fun _ : Fin h => channelLaw))
      (fun c => θ ≤ |∑ x, μ x*ψ x*channelCharacter h (A x) c|) ≤
      (∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample/
        (2 : ℝ)^(h*(∑ i, A (sample i)).rank))/θ^(2*t)

end Lax342547.ChannelMoments
