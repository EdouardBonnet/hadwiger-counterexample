import Lax342547.LeafTrimming
import Lax342547.MetadataPins

/-!
---
title: Mass and density costs of splitting by metadata and images
type: theorem
---
Discarding small fibers costs at most the number of split records times
the threshold. The remaining fibers have an absolute joint density cap
suitable for a fresh peeling, even after a preceding leaf restriction.
-/

namespace Lax342547.SplitTrimming

open Lax342547.MomentSpace Lax342547.MetadataPins
open scoped ENNReal

axiom small_fibers {Ω K : Type} [Fintype K] (p : PMF Ω) (f : Ω → K) (τ : ℝ≥0∞) :
    p.toOuterMeasure {o | p.toOuterMeasure {x | f x = f o} < τ} ≤ Fintype.card K * τ

axiom metadata_discard {Ω J Axis I N : Type}
    [Fintype J] [Fintype Axis] [Fintype I] [Fintype N]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (choice : Ω → J) (S : J → Axis → Submodule Binary (I → Binary)) (a n u : ℕ)
    (hchoices : Fintype.card J ≤ 2 ^ (a * n))
    (hu : ∀ j, ∑ b, Module.finrank Binary (S j b) ≤ u) :
    p.toOuterMeasure {o | p.toOuterMeasure {x | record A choice S x = record A choice S o} <
        (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * Fintype.card N))} ≤
      (2 : ℝ≥0∞) ^ ((a * n : ℕ) - (Fintype.card N : ℝ))

axiom exponential_discard {Ω J Axis I N : Type}
    [Fintype J] [Fintype Axis] [Fintype I] [Fintype N]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (choice : Ω → J) (S : J → Axis → Submodule Binary (I → Binary)) (a n u : ℕ)
    (hchoices : Fintype.card J ≤ 2 ^ (a * n))
    (hu : ∀ j, ∑ b, Module.finrank Binary (S j b) ≤ u)
    (hscale : 2 * a * n ≤ Fintype.card N) :
    p.toOuterMeasure {o | p.toOuterMeasure {x | record A choice S x = record A choice S o} <
        (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * Fintype.card N))} ≤
      (2 : ℝ≥0∞) ^ (-(Fintype.card N : ℝ) / 2)

axiom repinning_density {Ω : Type} (p μ : PMF Ω) (S T : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support)
    (hT : ∃ o ∈ T, o ∈ (p.filter S hS).support)
    (D ζ : ℝ) (N K₁ u : ℕ) (hζ : ζ ≤ 1)
    (hSbound : (2 : ℝ≥0∞) ^ (-(ζ * N)) ≤ p.toOuterMeasure S)
    (hTbound : (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * N)) ≤ (p.filter S hS).toOuterMeasure T)
    (hp : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ ((D + K₁ + 1) * N) * μ o) :
    ∀ o, ((p.filter S hS).filter T hT) o ≤
      (2 : ℝ≥0∞) ^ ((D + K₁ + u + 5) * N) * μ o

end Lax342547.SplitTrimming
