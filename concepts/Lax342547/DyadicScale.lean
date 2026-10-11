import Lax342547.DyadicTails

/-!
---
title: A small dyadic tail scale
type: definition and theorem
---
The actual dyadic recurrence and the total rank budget give a scale with tail deficit ratio less than one quarter.
-/

namespace Lax342547.DyadicScale

open Lax342547.DyadicTails
open scoped BigOperators

axiom single_scale (f v : ℕ → ℝ) (n : ℕ) (r : ℝ)
    (hrec : ∀ j < n, 2*v j ≤ 2*(f j-f (j+1))+v (j+1))
    (hf0 : f 0 ≤ r) (hfn : 0 ≤ f n) (hv0 : 0 ≤ v 0) (hvn : v n ≤ f n)
    (hn : 8*r < n) : ∃ j < n, v j < 1/4

axiom dyadic_small_tail (a : ℕ → ℝ) (ha : Antitone a) (ha0 : ∀ t, 0 ≤ a t)
    (k n : ℕ) (r : ℝ) (hnk : n ≤ k) (har : a 0 ≤ r) (hn : 8*r < n) :
    ∃ j < n, tailDeficit a (2^k) (2^(k-j)) < 1/4

end Lax342547.DyadicScale
