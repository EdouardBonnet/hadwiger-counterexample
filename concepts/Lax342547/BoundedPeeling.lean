import Lax342547.LeafPartition
import Lax342547.PeelingBudget
import Lax342547.Conditioning

/-!
---
title: Peeling with bounded new rank and normalized leaf laws
type: definition and theorem
---
The finite partition construction is quantitative under an absolute
reference image cap. It preserves initial pins, bounds only the added
rank, and records both conditional image probabilities and density costs.
-/

namespace Lax342547.BoundedPeeling

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.LeafPartition
open scoped ENNReal

def LawBound {Ω Axis I N : Type} [Fintype Axis] (p μ : PMF Ω)
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (S : Set Ω) (α c : ℝ≥0∞) : Prop :=
  ∃ hS : ∃ o ∈ S, o ∈ p.support,
    (∀ Q : Pin Axis I N, 1 ≤ P.relativeRank Q →
      (p.filter S hS).toOuterMeasure (Q.event A) ≤ α ^ (P.relativeRank Q)) ∧
    (∀ o, (p.filter S hS) o ≤ c * μ o) ∧
    ∀ o, p.toOuterMeasure S * (p.filter S hS) o = S.indicator p o

axiom bounded_partition {Ω Axis I N : Type}
    [Fintype Ω] [DecidableEq Ω] [Fintype Axis] [Fintype I] [Fintype N]
    (p μ : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (R : Finset Ω) (hR : (R : Set Ω) ⊆ P₀.event A)
    (D ζ ε : ℝ) (n K : ℕ) (hn : 0 < n)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hε : ε ≤ ζ / 4) (hK : 4 * (D + 1) / ζ ≤ K)
    (hdensity : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ (D * n) * μ o)
    (hreference : ∀ P : Pin Axis I N,
      μ.toOuterMeasure (P.event A) ≤ (2 : ℝ≥0∞) ^ (-((1 - ε) * P.rank * n))) :
    ∃ L : Finset (Finset Ω × Pin Axis I N),
      Partition p A P₀ R ((2 : ℝ≥0∞) ^ (-(ζ * n))) ((2 : ℝ≥0∞) ^ (-((1 - ζ) * n))) L ∧
      ∀ z ∈ L, z.2.rank - P₀.rank ≤ K ∧
        LawBound p μ A z.2 z.1 ((2 : ℝ≥0∞) ^ (-((1 - ζ) * n)))
          ((2 : ℝ≥0∞) ^ ((D + K + 1) * n))

end Lax342547.BoundedPeeling
