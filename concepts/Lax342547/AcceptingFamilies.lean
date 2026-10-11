import Lax342547.FiniteSampling
import Lax342547.RetainedImages

/-!
---
title: Finite accepting-family losses
type: lemma
---
Conditional event identities and finite family unions charge small accepted sets once and retain the actual accepting-pair mass.
-/

namespace Lax342547.AcceptingFamilies

open Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling
open scoped BigOperators

axiom conditional_event_mass {A : Type} [Fintype A] (α : A → ℝ) (C F : A → Prop) :
    cellMass (conditionalLaw α C) F = cellMass α (fun a => C a ∧ F a) / cellMass α C

axiom conditional_probability {A : Type} [Fintype A] (α : A → ℝ) (C : A → Prop)
    (hα : Probability α) (hC : 0 < cellMass α C) : Probability (conditionalLaw α C)

axiom accepting_family_loss {A B I : Type} [Fintype A] [Fintype B] [Fintype I]
    (α : A → ℝ) (β : B → ℝ) (C : I → A → Prop) (key : B → I) (F : B → A → Prop)
    (η τ U : ℝ) (hα : Probability α) (hβ : Probability β)
    (hη : 0 ≤ η) (hτ : 0 < τ) (hU : 0 ≤ U)
    (hex : ∀ i, τ ≤ cellMass α (C i) →
      cellMass β (fun b => η ≤ cellMass (conditionalLaw α (C i)) (F b)) ≤ U) :
    (∑ b, β b * cellMass α (fun a => C (key b) a ∧ F b a)) ≤
      η * (∑ b, β b * cellMass α (C (key b))) + τ + Fintype.card I * U

end Lax342547.AcceptingFamilies
