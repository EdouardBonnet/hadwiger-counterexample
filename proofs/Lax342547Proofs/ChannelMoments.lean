import Lax342547.ChannelMoments
import Lax342547.ChannelCharacters
import Lax342547.FiniteMoments
import Lax342547.FiniteSampling
import Lax342547.MomentTails

namespace Lax342547Proofs.ChannelMoments
open Lax342547.ChannelMoments

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open Lax342547.ChannelCharacters
open scoped BigOperators

/--
---
conclusion: Lax342547.ChannelMoments.channel_even_moment_bound
---
-/
theorem channel_even_moment_bound {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → Matrix I J Binary) (ψ : Ω → ℝ) (h t : ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hψ : ∀ x, |ψ x| ≤ 1) :
    (∑ c, productLaw (fun _ : Fin h => channelLaw) c*
      |∑ x, μ x*ψ x*channelCharacter h (A x) c|^(2*t)) ≤
      ∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample/
        (2 : ℝ)^(h*(∑ i, A (sample i)).rank) := by
  classical
  have havg (sample : Fin (2*t) → Ω) :
      (∑ c, productLaw (fun _ : Fin h => channelLaw) c*∏ i, channelCharacter h (A (sample i)) c) =
        1/(2 : ℝ)^(h*(∑ i, A (sample i)).rank) := by
    simp_rw [Lax342547.ChannelCharacters.product_channel_characters (fun i => A (sample i)) h]
    exact Lax342547.ChannelCharacters.repeated_character_average _ _
  have hh := Lax342547.FiniteMoments.weighted_character_moment_bound μ
    (productLaw (fun _ : Fin h => channelLaw)) ψ (fun x c => channelCharacter h (A x) c) t hμ hψ
    (fun sample => by rw [havg]; positivity)
  calc
    _ ≤ _ := hh
    _ = _ := by
      apply Finset.sum_congr rfl
      intro sample _
      rw [havg]
      ring

/--
---
conclusion: Lax342547.ChannelMoments.channel_phase_tail
---
-/
theorem channel_phase_tail {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → Matrix I J Binary) (ψ : Ω → ℝ) (h t : ℕ) (θ : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hψ : ∀ x, |ψ x| ≤ 1) (hθ : 0 < θ) :
    cellMass (productLaw (fun _ : Fin h => channelLaw))
      (fun c => θ ≤ |∑ x, μ x*ψ x*channelCharacter h (A x) c|) ≤
      (∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample/
        (2 : ℝ)^(h*(∑ i, A (sample i)).rank))/θ^(2*t) := by
  classical
  have hprob := Lax342547.FiniteSampling.product_probability
    (fun _ : Fin h => (channelLaw (I := I) (J := J))) (fun _ => Lax342547.ChannelCharacters.channel_probability)
  exact (Lax342547.MomentTails.finite_moment_markov _ _ θ (2*t) hprob.1 hθ).trans
    (div_le_div_of_nonneg_right (Lax342547.ChannelMoments.channel_even_moment_bound μ A ψ h t hμ hψ) (by positivity))

end Lax342547Proofs.ChannelMoments
