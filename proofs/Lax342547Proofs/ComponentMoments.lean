import Lax342547.ComponentMoments
import Lax342547Proofs.TensorCharacters
import Lax342547Proofs.MomentTails

namespace Lax342547Proofs.ComponentMoments
open Lax342547.ComponentMoments

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open Lax342547.ChannelCharacters Lax342547.TensorCharacters
open scoped BigOperators

/--
---
conclusion: Lax342547.ComponentMoments.component_even_moment_bound
---
-/
theorem component_even_moment_bound {e I J Ω : Type} [Fintype e] [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq e] [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → e → Matrix I J Binary) (ψ : Ω → ℝ) (h t : ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hψ : ∀ x, |ψ x| ≤ 1) :
    (∑ c, productLaw (fun _ : e × Fin h => channelLaw) c*
      |∑ x, μ x*ψ x*tensorCharacter h (A x) c|^(2*t)) ≤
      ∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample/
        (2 : ℝ)^(h*∑ a : e, (∑ i, A (sample i) a).rank) := by
  classical
  have havg (sample : Fin (2*t) → Ω) :
      (∑ c, productLaw (fun _ : e × Fin h => channelLaw) c*∏ i, tensorCharacter h (A (sample i)) c) =
        1/(2 : ℝ)^(h*∑ a : e, (∑ i, A (sample i) a).rank) := by
    simp_rw [Lax342547Proofs.TensorCharacters.product_tensor_characters (fun i => A (sample i)) h]
    exact Lax342547Proofs.TensorCharacters.tensor_character_average _ _
  have hh := Lax342547Proofs.FiniteMoments.weighted_character_moment_bound μ
    (productLaw (fun _ : e × Fin h => channelLaw)) ψ (fun x c => tensorCharacter h (A x) c) t hμ hψ
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
conclusion: Lax342547.ComponentMoments.component_phase_tail
---
-/
theorem component_phase_tail {e I J Ω : Type} [Fintype e] [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq e] [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → e → Matrix I J Binary) (ψ : Ω → ℝ) (h t : ℕ) (θ : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hψ : ∀ x, |ψ x| ≤ 1) (hθ : 0 < θ) :
    cellMass (productLaw (fun _ : e × Fin h => channelLaw))
      (fun c => θ ≤ |∑ x, μ x*ψ x*tensorCharacter h (A x) c|) ≤
      (∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample/
        (2 : ℝ)^(h*∑ a : e, (∑ i, A (sample i) a).rank))/θ^(2*t) := by
  classical
  have hprob := Lax342547Proofs.FiniteSampling.product_probability
    (fun _ : e × Fin h => (channelLaw (I := I) (J := J))) (fun _ => Lax342547Proofs.ChannelCharacters.channel_probability)
  exact (Lax342547Proofs.MomentTails.finite_moment_markov _ _ θ (2*t) hprob.1 hθ).trans
    (div_le_div_of_nonneg_right (component_even_moment_bound μ A ψ h t hμ hψ) (by positivity))

end Lax342547Proofs.ComponentMoments
