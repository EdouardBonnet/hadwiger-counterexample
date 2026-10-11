import Lax342547.Conditioning

/-!
---
title: Actual-mass recovery and residual bounds through finite splits
type: lemma
---
Finite mixture event masses retain their original weights. Successive
conditional parts recover the combined restriction exactly. Relative
residual budgets on split fibers sum to the same global budget.
-/

namespace Lax342547.MixtureRecovery

open scoped ENNReal

axiom mixture_event {Ω J : Type} [Fintype Ω] [Fintype J]
    (p : J → PMF Ω) (q : PMF Ω) (w : J → ℝ≥0∞)
    (hq : ∀ o, q o = ∑ j, w j * p j o) (S : Set Ω) :
    q.toOuterMeasure S = ∑ j, w j * (p j).toOuterMeasure S

axiom nested_weighted_filter {Ω : Type} (p : PMF Ω) (S T : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support)
    (hT : ∃ o ∈ T, o ∈ (p.filter S hS).support) (o : Ω) :
    p.toOuterMeasure S * (p.filter S hS).toOuterMeasure T * ((p.filter S hS).filter T hT) o =
      (S ∩ T).indicator p o

axiom conditional_event_mass {Ω : Type} [Fintype Ω] (p : PMF Ω)
    (S T : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support) (hT : T ⊆ S)
    (δ : ℝ≥0∞) (hb : (p.filter S hS).toOuterMeasure T ≤ δ) :
    p.toOuterMeasure T ≤ δ * p.toOuterMeasure S

axiom fiber_residual {Ω K : Type} [Fintype K] (p : PMF Ω) (f : Ω → K)
    (R : K → Set Ω) (τ δ : ℝ≥0∞)
    (hr : ∀ k, τ ≤ p.toOuterMeasure {o | f o = k} →
      p.toOuterMeasure (R k) ≤ δ * p.toOuterMeasure {o | f o = k}) :
    p.toOuterMeasure ({o | p.toOuterMeasure {x | f x = f o} < τ} ∪
        {o | τ ≤ p.toOuterMeasure {x | f x = f o} ∧ o ∈ R (f o)}) ≤
      p.toOuterMeasure {o | p.toOuterMeasure {x | f x = f o} < τ} + δ

end Lax342547.MixtureRecovery
