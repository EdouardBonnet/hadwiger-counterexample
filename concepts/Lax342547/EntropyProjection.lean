import Lax342547.EntropyLines

/-!
---
title: Full feasible support and finite information projection
type: lemma
---
A compact convex feasible family has an entropy minimizer positive on the union of all feasible supports. The exact one-sided variational inequality gives the information-projection bound and the negative log support cost, closing the finite content of Lemma 3.2.
-/

namespace Lax342547.EntropyProjection

open Lax342547.RelativeEntropy Lax342547.EntropyLines
open scoped Topology BigOperators
open Filter

axiom minimizer_full_support {Ω : Type} [Fintype Ω]
    (P : Set (Ω → ℝ)) (q ρ : Ω → ℝ)
    (hprob : ∀ p ∈ P, Probability p) (hconv : Convex ℝ P) (hρ : ρ ∈ P)
    (hmin : ∀ p ∈ P, entropy ρ q ≤ entropy p q) :
    ∀ ρ' ∈ P, ∀ x, 0 < ρ' x → 0 < ρ x

axiom minimizer_variational {Ω : Type} [Fintype Ω]
    (P : Set (Ω → ℝ)) (q ρ : Ω → ℝ)
    (hprob : ∀ p ∈ P, Probability p) (hconv : Convex ℝ P) (hρ : ρ ∈ P)
    (hmin : ∀ p ∈ P, entropy ρ q ≤ entropy p q) (ρ' : Ω → ℝ) (hρ' : ρ' ∈ P) :
    0 ≤ ∑ x, (ρ' x-ρ x)*(Real.log (ρ x)-Real.log (q x))

axiom projection_inequality {Ω : Type} [Fintype Ω]
    (P : Set (Ω → ℝ)) (q ρ : Ω → ℝ)
    (hprob : ∀ p ∈ P, Probability p) (hconv : Convex ℝ P) (hρ : ρ ∈ P)
    (hmin : ∀ p ∈ P, entropy ρ q ≤ entropy p q) (ρ' : Ω → ℝ) (hρ' : ρ' ∈ P) :
    entropy ρ' ρ ≤ entropy ρ' q-entropy ρ q

axiom projection_support_cost {Ω : Type} [Fintype Ω]
    (P : Set (Ω → ℝ)) (q ρ : Ω → ℝ)
    (hprob : ∀ p ∈ P, Probability p) (hconv : Convex ℝ P) (hρ : ρ ∈ P)
    (hmin : ∀ p ∈ P, entropy ρ q ≤ entropy p q) (ρ' : Ω → ℝ) (hρ' : ρ' ∈ P)
    (S : Ω → Prop) (hS : ∀ x, ¬ S x → ρ' x = 0)
    (hmass : 0 < Lax342547.RetainedImages.cellMass ρ S) :
    -Real.log (Lax342547.RetainedImages.cellMass ρ S) ≤ entropy ρ' q-entropy ρ q

axiom entropy_projection {Ω : Type} [Fintype Ω]
    (P : Set (Ω → ℝ)) (q : Ω → ℝ) (hcompact : IsCompact P) (hne : P.Nonempty)
    (hconv : Convex ℝ P) (hprob : ∀ p ∈ P, Probability p) :
    ∃ ρ ∈ P, (∀ ρ' ∈ P, entropy ρ q ≤ entropy ρ' q) ∧
      (∀ ρ' ∈ P, ∀ x, 0 < ρ' x → 0 < ρ x) ∧
      (∀ ρ' ∈ P, entropy ρ' ρ ≤ entropy ρ' q-entropy ρ q)

end Lax342547.EntropyProjection
