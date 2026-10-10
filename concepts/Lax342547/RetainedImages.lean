import Lax342547.PushforwardWalsh
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Image caps inside original retained cells
type: definition and theorem
---
Conditioning an original unary record cell costs only its own mass. The joint key and fresh-image cap gives the .95tN exponent, without intersecting cells over opposite parameters.
-/

namespace Lax342547.RetainedImages

open Lax342547.PushforwardWalsh

noncomputable def cellMass {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if C ω then ρ ω else 0

noncomputable def conditionalLaw {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop) : Ω → ℝ := by
  classical
  exact fun ω => (if C ω then ρ ω else 0) / cellMass ρ C

axiom conditional_law_nonneg {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop)
    (hρ : ∀ ω, 0 ≤ ρ ω) (ω : Ω) : 0 ≤ conditionalLaw ρ C ω

axiom conditional_law_total {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop)
    (hC : 0 < cellMass ρ C) : ∑ ω, conditionalLaw ρ C ω = 1

axiom conditional_image_cap {Ω X : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (image : Ω → X) (joint : Ω → Prop)
    (τ cap : ℝ) (hρ : ∀ ω, 0 ≤ ρ ω) (hτ : 0 < τ)
    (hC : τ ≤ cellMass ρ C) (hCJ : ∀ ω, C ω → joint ω)
    (hcap : ∀ x, cellMass ρ (fun ω => joint ω ∧ image ω = x) ≤ cap) (x : X) :
    push (conditionalLaw ρ C) image x ≤ cap / τ

axiom paper_cell_exponent (ζ k t : ℝ) (_hζ : 0 ≤ ζ)
    (hζsmall : ζ ≤ 1 / 1000) (hk : 2 * ζ * k ≤ 1 / 500) (ht : 1 ≤ t) :
    -(1 - 2 * ζ) * (k + t) + (k + 1 / 100) ≤ -(95 / 100 : ℝ) * t

axiom paper_conditional_cap (ζ k t N : ℝ) (hζ : 0 ≤ ζ)
    (hζsmall : ζ ≤ 1 / 1000) (hk : 2 * ζ * k ≤ 1 / 500) (ht : 1 ≤ t) (hN : 0 ≤ N) :
    (2 : ℝ) ^ (-(1 - 2 * ζ) * (k + t) * N) /
        (2 : ℝ) ^ (-(k + 1 / 100) * N) ≤ (2 : ℝ) ^ (-(95 / 100 : ℝ) * t * N)

end Lax342547.RetainedImages
