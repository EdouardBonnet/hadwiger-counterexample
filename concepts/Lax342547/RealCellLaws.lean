import Lax342547.RetainedImages
import Lax342547.Conditioning
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
---
title: Original retained-cell laws from finite PMFs
type: definition and theorem
---
Finite PMF events convert to real weights and normalized laws supported on the original retained cell. Joint image caps yield the paper conditional exponent without intersecting or changing that cell.
-/

namespace Lax342547.RealCellLaws

open Lax342547.RetainedImages Lax342547.PushforwardWalsh
open scoped ENNReal

noncomputable def weights {Ω : Type} (p : PMF Ω) : Ω → ℝ := fun ω => (p ω).toReal

axiom weights_nonneg {Ω : Type} (p : PMF Ω) (ω : Ω) : 0 ≤ weights p ω

axiom weights_total {Ω : Type} [Fintype Ω] (p : PMF Ω) : ∑ ω, weights p ω = 1

axiom event_mass {Ω : Type} [Fintype Ω] (p : PMF Ω) (C : Ω → Prop) :
    cellMass (weights p) C = (p.toOuterMeasure {ω | C ω}).toReal

noncomputable def subtypeWeights {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (C : Ω → Prop) :
    {ω // C ω} → ℝ := fun ω => ρ ω.val / cellMass ρ C

axiom subtype_integral {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (f : Ω → ℝ) : by
      classical
      exact (∑ ω : {ω // C ω}, subtypeWeights ρ C ω * f ω.val) =
        ∑ ω, conditionalLaw ρ C ω * f ω

axiom subtype_weights_total {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (hC : 0 < cellMass ρ C) : by
      classical
      exact (∑ ω : {ω // C ω}, subtypeWeights ρ C ω) = 1

axiom subtype_weights_nonneg {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (hρ : ∀ ω, 0 ≤ ρ ω) (hC : 0 < cellMass ρ C)
    (ω : {ω // C ω}) : 0 ≤ subtypeWeights ρ C ω

axiom subtype_image_push {Ω X : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (image : Ω → X) (x : X) : by
      classical
      exact push (subtypeWeights ρ C) (fun ω => image ω.val) x = push (conditionalLaw ρ C) image x

axiom subtype_conditional_cap {Ω X : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (image : Ω → X) (joint : Ω → Prop)
    (τ cap : ℝ) (hρ : ∀ ω, 0 ≤ ρ ω) (hτ : 0 < τ)
    (hC : τ ≤ cellMass ρ C) (hCJ : ∀ ω, C ω → joint ω)
    (hcap : ∀ x, cellMass ρ (fun ω => joint ω ∧ image ω = x) ≤ cap) (x : X) : by
      classical
      exact push (subtypeWeights ρ C) (fun ω => image ω.val) x ≤ cap / τ

axiom pmf_subtype_conditional_cap {Ω X : Type} [Fintype Ω]
    (p : PMF Ω) (C : Ω → Prop) (image : Ω → X) (joint : Ω → Prop)
    (τ : ℝ) (cap : ℝ≥0∞) (hcapTop : cap ≠ ⊤) (hτ : 0 < τ)
    (hC : τ ≤ (p.toOuterMeasure {ω | C ω}).toReal) (hCJ : ∀ ω, C ω → joint ω)
    (hcap : ∀ x, p.toOuterMeasure {ω | joint ω ∧ image ω = x} ≤ cap) (x : X) : by
      classical
      exact push (subtypeWeights (weights p) C) (fun ω => image ω.val) x ≤ cap.toReal / τ

axiom pmf_paper_subtype_cap {Ω X : Type} [Fintype Ω]
    (p : PMF Ω) (C : Ω → Prop) (image : Ω → X) (joint : Ω → Prop)
    (ζ k t N : ℝ) (hζ : 0 ≤ ζ) (hζsmall : ζ ≤ 1 / 1000)
    (hk : 2 * ζ * k ≤ 1 / 500) (ht : 1 ≤ t) (hN : 0 ≤ N)
    (hC : (2 : ℝ) ^ (-(k + 1 / 100) * N) ≤ (p.toOuterMeasure {ω | C ω}).toReal)
    (hCJ : ∀ ω, C ω → joint ω)
    (hcap : ∀ x, p.toOuterMeasure {ω | joint ω ∧ image ω = x} ≤
      (2 : ℝ≥0∞) ^ (-(1 - 2 * ζ) * (k + t) * N)) (x : X) : by
      classical
      exact push (subtypeWeights (weights p) C) (fun ω => image ω.val) x ≤
        (2 : ℝ) ^ (-(95 / 100 : ℝ) * t * N)

end Lax342547.RealCellLaws
