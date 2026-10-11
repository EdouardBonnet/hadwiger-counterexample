import Lax342547.FiniteSampling
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
---
title: Finite even moment expansion
type: definition and theorem
---
An actual finite even moment expands over independent samples. Bounded unit-side signs may be removed whenever the channel character expectation is nonnegative.
-/

namespace Lax342547.FiniteMoments

open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

axiom finite_even_moment {Ω C : Type} [Fintype Ω] [Fintype C]
    (μ : Ω → ℝ) (ν : C → ℝ) (ψ : Ω → ℝ) (χ : Ω → C → ℝ) (t : ℕ) :
    (∑ c, ν c*|∑ x, μ x*ψ x*χ x c|^(2*t)) =
      ∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample*
        (∏ i, ψ (sample i))*(∑ c, ν c*∏ i, χ (sample i) c)

axiom weighted_character_moment_bound {Ω C : Type} [Fintype Ω] [Fintype C]
    (μ : Ω → ℝ) (ν : C → ℝ) (ψ : Ω → ℝ) (χ : Ω → C → ℝ) (t : ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hψ : ∀ x, |ψ x| ≤ 1)
    (hχ : ∀ sample : Fin (2*t) → Ω, 0 ≤ ∑ c, ν c*∏ i, χ (sample i) c) :
    (∑ c, ν c*|∑ x, μ x*ψ x*χ x c|^(2*t)) ≤
      ∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample*
        (∑ c, ν c*∏ i, χ (sample i) c)

end Lax342547.FiniteMoments
