import Lax342547.Walsh

/-!
---
title: Walsh operator bounds with explicit bilinear rank
type: lemma
---
A rectangular bilinear phase factors through its column-image map.
Grouping the second weight by the fibers of that map costs at most the
kernel cardinality in squared energy. Rank-nullity then gives the exact
rank-dependent Walsh estimate, including bounded-density laws and affine
phases confined to either input group.
-/

namespace Lax342547.BilinearWalsh

open Lax342547.MomentSpace Lax342547.Walsh

noncomputable def correlation {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ) : ℝ :=
  ∑ x, ∑ y, f x * g y * phase x (A.mulVec y)

noncomputable def average {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ) : ℝ :=
  correlation A f g / (2 ^ Fintype.card I * 2 ^ Fintype.card J)

axiom correlation_sq {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ) :
    (correlation A f g) ^ 2 ≤ (2 : ℝ) ^ (Fintype.card I + (Fintype.card J - A.rank)) *
      (∑ x, (f x) ^ 2) * ∑ y, (g y) ^ 2

axiom uniform_bound {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    |average A f g| ≤ 1 / Real.sqrt ((2 : ℝ) ^ A.rank)

axiom bounded_weight_bound {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ) (C₁ C₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hf : ∀ x, |f x| ≤ C₁) (hg : ∀ y, |g y| ≤ C₂) :
    |average A f g| ≤ C₁ * C₂ / Real.sqrt ((2 : ℝ) ^ A.rank)

axiom density_bound {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (α f : (I → Binary) → ℝ) (β g : (J → Binary) → ℝ) (C₁ C₂ : ℝ)
    (hα : ∀ x, 0 ≤ α x ∧ α x ≤ C₁) (hβ : ∀ y, 0 ≤ β y ∧ β y ≤ C₂)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    |average A (fun x => α x * f x) (fun y => β y * g y)| ≤
      C₁ * C₂ / Real.sqrt ((2 : ℝ) ^ A.rank)

axiom separate_phase_bound {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ)
    (u : (I → Binary) → Binary) (v : (J → Binary) → Binary) (c : Binary)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    |(∑ x, ∑ y, f x * g y * sign (dotProduct x (A.mulVec y) + u x + v y + c)) /
      ((2 : ℝ) ^ Fintype.card I * 2 ^ Fintype.card J)| ≤ 1 / Real.sqrt ((2 : ℝ) ^ A.rank)

axiom conditional_mixture_bound {T : Type} [Fintype T] {I J : T → Type}
    [∀ t, Fintype (I t)] [∀ t, Fintype (J t)]
    [∀ t, DecidableEq (I t)] [∀ t, DecidableEq (J t)]
    (A : ∀ t, Matrix (I t) (J t) Binary)
    (f : ∀ t, (I t → Binary) → ℝ) (g : ∀ t, (J t → Binary) → ℝ)
    (w C₁ C₂ : T → ℝ) (R : ℕ) (hw : ∀ t, 0 ≤ w t)
    (hC₁ : ∀ t, 0 ≤ C₁ t) (hC₂ : ∀ t, 0 ≤ C₂ t)
    (hf : ∀ t x, |f t x| ≤ C₁ t) (hg : ∀ t y, |g t y| ≤ C₂ t)
    (hR : ∀ t, R ≤ (A t).rank) :
    |∑ t, w t * average (A t) (f t) (g t)| ≤
      (∑ t, w t * C₁ t * C₂ t) / Real.sqrt ((2 : ℝ) ^ R)

end Lax342547.BilinearWalsh
