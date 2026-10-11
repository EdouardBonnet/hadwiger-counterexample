import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Finset.Union

/-!
---
title: Exact conditioning costs and recovery of finite probability masses
type: lemma
---
Conditioning divides event probabilities and point densities by the
retained mass. Multiplying a conditional law by that actual mass recovers
the original unnormalized restriction pointwise.
-/

namespace Lax342547.Conditioning

open scoped ENNReal

axiom filter_event {Ω : Type} [Fintype Ω] (p : PMF Ω) (S T : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) :
    (p.filter S hS).toOuterMeasure T = p.toOuterMeasure (S ∩ T) / p.toOuterMeasure S

axiom filter_event_bound {Ω : Type} [Fintype Ω] (p : PMF Ω) (S T : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) (c : ℝ≥0∞)
    (hc : p.toOuterMeasure (S ∩ T) ≤ c * p.toOuterMeasure S) :
    (p.filter S hS).toOuterMeasure T ≤ c

axiom filter_density {Ω : Type} (p μ : PMF Ω) (S : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) (c : ℝ≥0∞) (hc : ∀ o, p o ≤ c * μ o) :
    ∀ o, (p.filter S hS) o ≤ (c / p.toOuterMeasure S) * μ o

axiom weighted_filter {Ω : Type} (p : PMF Ω) (S : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) (o : Ω) :
    p.toOuterMeasure S * (p.filter S hS) o = S.indicator p o

axiom disjoint_mixture {Ω J : Type} [DecidableEq Ω] (p : PMF Ω)
    (L : Finset J) (S : J → Finset Ω)
    (hdisjoint : ∀ i ∈ L, ∀ j ∈ L, i ≠ j → Disjoint (S i) (S j))
    (hS : ∀ j ∈ L, ∃ o ∈ (S j : Set Ω), o ∈ p.support) (o : Ω) :
    (∑ j : {j // j ∈ L}, p.toOuterMeasure (S j.val) * (p.filter (S j.val) (hS j.val j.property)) o) =
      (L.biUnion S : Set Ω).indicator p o

end Lax342547.Conditioning
