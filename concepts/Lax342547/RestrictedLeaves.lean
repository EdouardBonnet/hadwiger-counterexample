import Lax342547.LeafTrimming
import Lax342547.BoundedPeeling

/-!
---
title: Trimming a restricted family of exact-pin leaves
type: lemma
---
Retained fractions are weighted by the actual original leaf masses.
A bound on their combined cost suffices to keep every surviving leaf's
image and density estimates, with a uniform explicit discarded fraction.
-/

namespace Lax342547.RestrictedLeaves

open Lax342547.MomentSpace Lax342547.ExactPins
open Lax342547.LeafTrimming Lax342547.BoundedPeeling
open scoped ENNReal

axiom restricted_family {Ω J Axis I N : Type}
    [Fintype Ω] [Fintype J] [Fintype Axis]
    (p : J → PMF Ω) (μ : PMF Ω)
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : J → Pin Axis I N) (S : J → Set Ω) (w : J → ℝ≥0∞)
    (C ζ η : ℝ) (n : ℕ) (hζ : 0 ≤ ζ) (hw : ∑ j, w j ≤ 1)
    (hq : (2 : ℝ≥0∞) ^ (-(η * n)) ≤ ∑ j, w j * (p j).toOuterMeasure (S j))
    (hcap : ∀ j (Q : Pin Axis I N), 1 ≤ (P j).relativeRank Q →
      (p j).toOuterMeasure (Q.event A) ≤
        ((2 : ℝ≥0∞) ^ (-((1 - ζ) * n))) ^ (P j).relativeRank Q)
    (hdensity : ∀ j o, p j o ≤ (2 : ℝ≥0∞) ^ (C * n) * μ o) :
    discardedMass w (fun j => (p j).toOuterMeasure (S j)) ((2 : ℝ≥0∞) ^ (-(ζ * n))) /
        (∑ j, w j * (p j).toOuterMeasure (S j)) ≤ (2 : ℝ≥0∞) ^ (-((ζ - η) * n)) ∧
    ∀ j, (2 : ℝ≥0∞) ^ (-(ζ * n)) ≤ (p j).toOuterMeasure (S j) →
      LawBound (p j) μ A (P j) (S j)
        ((2 : ℝ≥0∞) ^ (-((1 - 2 * ζ) * n))) ((2 : ℝ≥0∞) ^ ((C + ζ) * n))

axiom weighted_residual {J : Type} [Fintype J] (w r : J → ℝ≥0∞) (δ : ℝ≥0∞)
    (hw : ∑ j, w j ≤ 1) (hr : ∀ j, r j ≤ δ) : ∑ j, w j * r j ≤ δ

end Lax342547.RestrictedLeaves
