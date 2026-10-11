import Lax342547.EntropyProjection
import Lax342547.PairRecovery

/-!
---
title: Admissible pair laws
type: lemma
---
Compactness, convexity and entropy minimization for the actual marginal and pair capacity constraints.
-/

namespace Lax342547.UnitLaws

open Lax342547.RelativeEntropy
open scoped BigOperators

def Feasible {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (R : Ω → Ω → Prop)
    (M κ : ℝ) (ρ : Ω × Ω → ℝ) : Prop :=
  Probability ρ ∧ (∀ x, (∑ y, ρ (x,y)) ≤ M*μ x) ∧
    (∀ y, (∑ x, ρ (x,y)) ≤ M*μ y) ∧
    (∀ xy, ρ xy ≤ κ*(μ xy.1*μ xy.2)) ∧ (∀ xy, ¬ R xy.1 xy.2 → ρ xy = 0)

axiom feasible_closed {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ) : IsClosed {ρ | Feasible μ R M κ ρ}

axiom feasible_compact {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ) : IsCompact {ρ | Feasible μ R M κ ρ}

axiom feasible_convex {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ) : Convex ℝ {ρ | Feasible μ R M κ ρ}

axiom entropy_minimizer {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ)
    (hne : ∃ ρ, Feasible μ R M κ ρ) :
    ∃ ρ, Feasible μ R M κ ρ ∧
      (∀ ρ', Feasible μ R M κ ρ' → entropy ρ (fun xy => μ xy.1*μ xy.2) ≤ entropy ρ' (fun xy => μ xy.1*μ xy.2)) ∧
      (∀ ρ', Feasible μ R M κ ρ' → ∀ xy, 0 < ρ' xy → 0 < ρ xy) ∧
      (∀ ρ', Feasible μ R M κ ρ' → entropy ρ' ρ ≤
        entropy ρ' (fun xy => μ xy.1*μ xy.2)-entropy ρ (fun xy => μ xy.1*μ xy.2))

axiom feasible_entropy_budget {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ) (ρ : Ω × Ω → ℝ)
    (hμ : Probability μ) (hμpos : ∀ x, 0 < μ x) (hκ : 0 < κ) (hρ : Feasible μ R M κ ρ) :
    0 ≤ entropy ρ (fun xy => μ xy.1*μ xy.2) ∧ entropy ρ (fun xy => μ xy.1*μ xy.2) ≤ Real.log κ

end Lax342547.UnitLaws
