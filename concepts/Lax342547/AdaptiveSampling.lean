import Lax342547.CoordinateRestrictions

/-!
---
title: Sampling after exposed coordinates
type: definition and theorem
---
For independent product samples, a cylinder event defined by exposed coordinates has the exact averaged power probability and the uniform power bound.
-/

namespace Lax342547.AdaptiveSampling

open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

axiom adaptive_cylinder_probability {J K Ω : Type} [Fintype J] [Fintype K] [Fintype Ω]
    [DecidableEq J] [DecidableEq K] (μ : Ω → ℝ) (A : (J → Ω) → Ω → Prop) :
    cellMass (productLaw (fun _ : J ⊕ K => μ))
      (fun sample => ∀ k, A (fun j => sample (.inl j)) (sample (.inr k))) =
      ∑ exposed : J → Ω, productLaw (fun _ : J => μ) exposed*(cellMass μ (A exposed))^Fintype.card K

axiom adaptive_cylinder_bound {J K Ω : Type} [Fintype J] [Fintype K] [Fintype Ω]
    [DecidableEq J] [DecidableEq K] (μ : Ω → ℝ) (A : (J → Ω) → Ω → Prop) (p : ℝ)
    (hμ : Probability μ) (hp : ∀ exposed, cellMass μ (A exposed) ≤ p) :
    cellMass (productLaw (fun _ : J ⊕ K => μ))
      (fun sample => ∀ k, A (fun j => sample (.inl j)) (sample (.inr k))) ≤ p^Fintype.card K

end Lax342547.AdaptiveSampling
