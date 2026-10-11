import Lax342547.DyadicDeficits
import Mathlib.Algebra.BigOperators.Field

/-!
---
title: Actual dyadic deficit recurrence
type: lemma
---
For nonnegative decreasing span increments, tail deficits are nonnegative and satisfy the dyadic averaging recurrence.
-/

namespace Lax342547.DyadicTails

open scoped BigOperators

noncomputable def tailSum (a : ℕ → ℝ) (s b : ℕ) : ℝ := ∑ t ∈ Finset.range b, a (s-b+t)
noncomputable def tailDeficit (a : ℕ → ℝ) (s b : ℕ) : ℝ := a (s-b)-tailSum a s b/b

axiom tail_deficit_nonneg (a : ℕ → ℝ) (ha : Antitone a) (s b : ℕ) (hb : 0 < b) :
    0 ≤ tailDeficit a s b

axiom tail_deficit_le (a : ℕ → ℝ) (ha : ∀ t, 0 ≤ a t) (s b : ℕ) :
    tailDeficit a s b ≤ a (s-b)

axiom dyadic_recurrence (a : ℕ → ℝ) (ha : Antitone a) (s b : ℕ)
    (hb : 0 < b) (hbs : 2*b ≤ s) :
    2*tailDeficit a s (2*b) ≤ 2*(a (s-2*b)-a (s-b))+tailDeficit a s b

end Lax342547.DyadicTails
