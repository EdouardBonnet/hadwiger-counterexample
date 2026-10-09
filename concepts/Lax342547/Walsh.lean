import Lax342547.MomentSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
---
title: Orthogonality and finite Walsh correlation bounds
type: definition and theorem
---
The real binary character is 1 on zero and -1 on one. Its dot-product
matrix has orthogonal rows. The resulting exact squared operator bound
controls correlations of bounded weights and subprobability masses.
-/

namespace Lax342547.Walsh

open Lax342547.MomentSpace

noncomputable def sign (z : Binary) : ℝ := if z = 0 then 1 else -1

noncomputable def phase {I : Type} [Fintype I] (x y : I → Binary) : ℝ :=
  sign (dotProduct x y)

noncomputable def transform {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Binary) → ℝ) (x : I → Binary) : ℝ := ∑ y, phase x y * f y

axiom linear_orthogonality {V : Type} [AddCommGroup V] [Module Binary V] [Fintype V]
    (f : V →ₗ[Binary] Binary) (hf : f ≠ 0) : ∑ x, sign (f x) = 0

axiom orthogonality {I : Type} [Fintype I] [DecidableEq I]
    (x z : I → Binary) :
    ∑ y, phase x y * phase z y = if x = z then (2 : ℝ) ^ Fintype.card I else 0

axiom transform_energy {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Binary) → ℝ) :
    ∑ x, (transform f x) ^ 2 = (2 : ℝ) ^ Fintype.card I * ∑ y, (f y) ^ 2

axiom dot_correlation_sq {I : Type} [Fintype I] [DecidableEq I]
    (f g : (I → Binary) → ℝ) :
    (∑ x, ∑ y, f x * g y * phase x y) ^ 2 ≤
      (2 : ℝ) ^ Fintype.card I * (∑ x, (f x) ^ 2) * ∑ y, (g y) ^ 2

axiom subprobability_dot_bound {I : Type} [Fintype I] [DecidableEq I]
    (α β f g : (I → Binary) → ℝ) (p₁ p₂ : ℝ)
    (hα : ∀ x, 0 ≤ α x ∧ α x ≤ p₁) (hβ : ∀ y, 0 ≤ β y ∧ β y ≤ p₂)
    (hαsum : ∑ x, α x ≤ 1) (hβsum : ∑ y, β y ≤ 1)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    |∑ x, ∑ y, α x * β y * f x * g y * phase x y| ≤
      Real.sqrt ((2 : ℝ) ^ Fintype.card I * p₁ * p₂)

end Lax342547.Walsh
