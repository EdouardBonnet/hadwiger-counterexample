import Lax342547.Conditioning
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
---
title: Quantitative trimming after restrictions of a leaf mixture
type: theorem
---
Small retained fractions are discarded with their actual mixture weights.
The normalized surviving leaves preserve image bounds with an explicit
loss, while marginal bounds are tracked on the restricted mixed law.
-/

namespace Lax342547.LeafTrimming

open scoped ENNReal

noncomputable def discardedMass {J : Type} [Fintype J]
    (w q : J → ℝ≥0∞) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j, if q j < δ then w j * q j else 0

axiom weighted_discard {J : Type} [Fintype J] (w q : J → ℝ≥0∞)
    (δ : ℝ≥0∞) (hw : ∑ j, w j ≤ 1) : discardedMass w q δ ≤ δ

axiom restricted_discard {J : Type} [Fintype J] (w q : J → ℝ≥0∞)
    (ζ η : ℝ) (N : ℕ) (hw : ∑ j, w j ≤ 1)
    (hq : (2 : ℝ≥0∞) ^ (-(η * N)) ≤ ∑ j, w j * q j) :
    discardedMass w q ((2 : ℝ≥0∞) ^ (-(ζ * N))) / (∑ j, w j * q j) ≤
      (2 : ℝ≥0∞) ^ (-((ζ - η) * N))

axiom event_after_restriction {Ω : Type} [Fintype Ω] (p : PMF Ω)
    (S T : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support) (τ b : ℝ≥0∞)
    (hτ : τ ≤ p.toOuterMeasure S) (hb : p.toOuterMeasure T ≤ b) :
    (p.filter S hS).toOuterMeasure T ≤ b / τ

axiom minentropy_after_restriction {Ω : Type} [Fintype Ω] (p : PMF Ω)
    (S T : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support) (ζ : ℝ) (N t : ℕ)
    (hζ : 0 ≤ ζ) (ht : 1 ≤ t)
    (hSbound : (2 : ℝ≥0∞) ^ (-(ζ * N)) ≤ p.toOuterMeasure S)
    (hTbound : p.toOuterMeasure T ≤ (2 : ℝ≥0∞) ^ (-((1 - ζ) * t * N))) :
    (p.filter S hS).toOuterMeasure T ≤ (2 : ℝ≥0∞) ^ (-((1 - 2 * ζ) * t * N))

axiom density_after_restriction {Ω : Type} (p μ : PMF Ω)
    (S : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support) (C ζ : ℝ) (N : ℕ)
    (hSbound : (2 : ℝ≥0∞) ^ (-(ζ * N)) ≤ p.toOuterMeasure S)
    (hp : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ (C * N) * μ o) :
    ∀ o, (p.filter S hS) o ≤ (2 : ℝ≥0∞) ^ ((C + ζ) * N) * μ o

axiom filtered_marginal {Ω V : Type} [Fintype Ω] (p : PMF Ω) (μ : PMF V)
    (f : Ω → V) (S : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support)
    (M : ℝ≥0∞) (hp : ∀ v, p.map f v ≤ M * μ v) :
    ∀ v, (p.filter S hS).map f v ≤ (M / p.toOuterMeasure S) * μ v

axiom combined_restriction {Ω : Type} [Fintype Ω] (p : PMF Ω) (S T : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support)
    (hT : ∃ o ∈ T, o ∈ (p.filter S hS).support)
    (hST : ∃ o ∈ S ∩ T, o ∈ p.support) :
    (p.filter S hS).filter T hT = p.filter (S ∩ T) hST

end Lax342547.LeafTrimming
