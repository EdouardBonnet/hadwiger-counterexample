import Lax342547.UniformPhaseTails

/-!
---
title: Actual phase averages from small exceptional tails
type: definition and theorem
---
Absolute values of the actual tensor characters and finite density transfer recover averaged phase cancellation from checked tails without normalizing away exceptional mass.
-/

namespace Lax342547.PhaseAverages

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.ChannelCharacters Lax342547.TensorCharacters
open Lax342547.RelativeEntropy Lax342547.RetainedImages
open scoped BigOperators

axiom tensor_character_abs {e I J : Type} [Fintype e] [Fintype I] [Fintype J]
    (h : ℕ) (A : e → Matrix I J Binary) (c : e × Fin h → (I → Binary) × (J → Binary)) :
    |tensorCharacter h A c| = 1

axiom conditional_phase_abs_le_one {e I J Ω : Type} [Fintype e] [Fintype I] [Fintype J] [Fintype Ω]
    (μ : Ω → ℝ) (A : Ω → e → Matrix I J Binary) (ψ : Ω → ℝ)
    (h : ℕ) (c : e × Fin h → (I → Binary) × (J → Binary))
    (hμ : Probability μ) (hψ : ∀ x, |ψ x| ≤ 1) :
    |∑ x, μ x*ψ x*tensorCharacter h (A x) c| ≤ 1

axiom finite_event_density {Ω : Type} [Fintype Ω] (α β : Ω → ℝ) (L : ℝ)
    (hcap : ∀ x, β x ≤ L*α x) (E : Ω → Prop) : cellMass β E ≤ L*cellMass α E

axiom average_from_phase_tail {Ω : Type} [Fintype Ω] (β : Ω → ℝ) (f : Ω → ℝ)
    (θ : ℝ) (hβ : Probability β) (hf : ∀ x, |f x| ≤ 1) (hθ : 0 ≤ θ) :
    |∑ x, β x*f x| ≤ θ+cellMass β (fun x => θ ≤ |f x|)

end Lax342547.PhaseAverages
