import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
---
title: Dyadic span deficit estimates
type: lemma
---
The finite telescoping deficit recurrence yields a common scale with small combined row and column deficit.
-/

namespace Lax342547.DyadicDeficits

open scoped BigOperators

axiom sum_shift (v : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, v (j+1)) = (∑ j ∈ Finset.range n, v j)-v 0+v n

axiom sum_differences (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (f j-f (j+1))) = f 0-f n

axiom deficit_ratio_sum (f v : ℕ → ℝ) (n : ℕ) (r : ℝ)
    (hrec : ∀ j < n, 2*v j ≤ 2*(f j-f (j+1))+v (j+1))
    (hf0 : f 0 ≤ r) (hfn : 0 ≤ f n) (hv0 : 0 ≤ v 0) (hvn : v n ≤ f n) :
    (∑ j ∈ Finset.range n, v j) ≤ 2*r

axiom two_mode_scale (fC fR vC vR : ℕ → ℝ) (n : ℕ) (r : ℝ)
    (hC : ∀ j < n, 2*vC j ≤ 2*(fC j-fC (j+1))+vC (j+1))
    (hR : ∀ j < n, 2*vR j ≤ 2*(fR j-fR (j+1))+vR (j+1))
    (hfC0 : fC 0 ≤ r) (hfR0 : fR 0 ≤ r)
    (hfCn : 0 ≤ fC n) (hfRn : 0 ≤ fR n)
    (hvC0 : 0 ≤ vC 0) (hvR0 : 0 ≤ vR 0)
    (hvCn : vC n ≤ fC n) (hvRn : vR n ≤ fR n) (hn : 16*r < n) :
    ∃ j < n, vC j+vR j < 1/4

end Lax342547.DyadicDeficits
