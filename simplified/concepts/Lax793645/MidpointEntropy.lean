import Lax793645.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
---
title: Entropy progress from a deleted neighborhood
type: lemma
---
For $F(\rho)=\sum_x\rho(x)\log\rho(x)$, if $\sigma$ vanishes on a
deleted set $D$, the midpoint convexity gap is at least $\rho(D)\log2$.
If $\rho$ minimizes $F$ over a convex feasible set containing $\sigma$,
minimality at the midpoint gives $F(\sigma)-F(\rho)\ge\rho(D)\log2$.
This is the container progress estimate; no support or information-projection
theorem is required.
-/

namespace Lax793645.MidpointEntropy
noncomputable section
open FiniteProbability
open scoped BigOperators

def potential {A : Type*} [Fintype A] (ρ : Weight A) : ℝ := ∑ x, ρ x * Real.log (ρ x)
def midpoint {A : Type*} (ρ σ : Weight A) : Weight A := fun x => (ρ x + σ x) * 2⁻¹

axiom midpoint_gap {A : Type*} [Fintype A] (ρ σ : Weight A)
    (hρ : ∀ x, 0 ≤ ρ x) (hσ : ∀ x, 0 ≤ σ x)
    (D : A → Prop) (hD : ∀ x, D x → σ x = 0) :
    mass ρ D * Real.log 2 ≤ potential ρ + potential σ - 2 * potential (midpoint ρ σ)

axiom progress {A : Type*} [Fintype A] (ρ σ : Weight A)
    (hρ : ∀ x, 0 ≤ ρ x) (hσ : ∀ x, 0 ≤ σ x)
    (D : A → Prop) (hD : ∀ x, D x → σ x = 0)
    (hmin : potential ρ ≤ potential (midpoint ρ σ)) :
    mass ρ D * Real.log 2 ≤ potential σ - potential ρ

end
end Lax793645.MidpointEntropy
