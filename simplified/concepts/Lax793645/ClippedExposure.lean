import Lax793645.ConstructionData

/-!
---
title: The loss from revealing a matching edge
type: lemma
---
Both marginals of the joint law are the same, and conflicting pairs have zero joint
mass. On the part of the space satisfying the density cap, half the independent
conflict probability, after the lowest threshold is subtracted, bounds the expected
loss of the clipped potential.
-/

namespace Lax793645.ClippedExposure

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open scoped BigOperators
variable {X I : Type*} [Fintype X] [Fintype I]

axiom dyadic_exposure_joint (q σ : Wgt X) (P : X → X → ℝ)
    (hq : IsLaw q) (hσ : IsLaw σ)
    (hP : ∀ y x, 0 ≤ P y x) (hrow : ∀ y, ∑ x, P y x = σ y)
    (hcol : ∀ x, ∑ y, P y x = σ x)
    (C : X → X → Prop) (hzero : ∀ y x, C y x → P y x = 0)
    (A : X → Prop) (γ κ : ℝ) (hγ : 0 ≤ γ)
    (b : ℕ) (hb : 0 < b) (hκ : κ ≤ (2:ℝ)^b*γ)
    (hcap : ∀ x, A x → σ x ≤ κ* q x) :
    (∑ x, σ x * ind (A x) * pr σ (fun y => C y x)) - γ ≤
      2*(clippedPotential q (fun i : Fin b => (2:ℝ)^i.val*γ) σ -
        avg σ (clippedPotential q (fun i : Fin b => (2:ℝ)^i.val*γ) ∘ posterior P σ))

end

end Lax793645.ClippedExposure
