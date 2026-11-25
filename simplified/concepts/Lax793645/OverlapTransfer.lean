import Lax793645.FiniteProbability

/-!
---
title: Finite transfer of successful-query overlaps
type: lemma
---
Let $f,g\in[0,1]$ be bounded surrogate densities and let $x,y$ be actual
successful-query subprobabilities, supported on the reference law $\mu$.
The squared surrogate overlap is at most the actual overlap, plus the
truncated projection error, two cell-distribution errors, and two tail masses.
The cell tests concern the whole key tuple. Weak product comparison supplies
these errors from unary status tables and binary mixing.
-/

namespace Lax793645.OverlapTransfer
open FiniteProbability

axiom finite_transfer {A B : Type} [Fintype A] [Fintype B]
    (μ : Weight A) (hμ : Probability μ) (p : A → B) (R : ℝ) (hR : 0 ≤ R)
    (f g x y : Weight A) (hf : bounded f) (hg : bounded g)
    (hx : Subprobability x) (hy : Subprobability y)
    (hxs : dominatedSupport x μ) (hys : dominatedSupport y μ) :
    inner μ f g ^ 2 ≤ inner μ (density μ x) (density μ y) +
      |projectionError μ (clip R μ x) (clip R μ y) p| +
      ((cellError μ p f x + tail R μ x) + (cellError μ p g y + tail R μ y))

/-- The stronger form retains the clipped actual overlap. This is the form
used when a uniformly small raw-input rejection is imposed afterward. -/
axiom clipped_transfer {A B : Type} [Fintype A] [Fintype B]
    (μ : Weight A) (hμ : Probability μ) (p : A → B) (R : ℝ) (hR : 0 ≤ R)
    (f g x y : Weight A) (hf : bounded f) (hg : bounded g)
    (hx : Subprobability x) (hy : Subprobability y)
    (hxs : dominatedSupport x μ) (hys : dominatedSupport y μ) :
    inner μ f g ^ 2 ≤ inner μ (clip R μ x) (clip R μ y) +
      |projectionError μ (clip R μ x) (clip R μ y) p| +
      ((cellError μ p f x + tail R μ x) + (cellError μ p g y + tail R μ y))

end Lax793645.OverlapTransfer
