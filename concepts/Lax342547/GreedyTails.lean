import Lax342547.GreedySpans
import Lax342547.ListTails
import Lax342547.DyadicScale
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
---
title: Small actual greedy exposure tails
type: definition and theorem
---
Greedy exposure bounds the actual sum of projected mode dimensions minus their span increase by a dyadic tail deficit, yielding a small tail at an explicit scale.
-/

namespace Lax342547.GreedyTails

open Lax342547.GreedySpans Lax342547.ListTails Lax342547.DyadicTails
open scoped BigOperators

noncomputable def deficit {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) : ℝ :=
    (l.map (fun i => gain W (S i))).sum-(increments S W l).sum

axiom greedy_deficit_bound {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι)
    (hg : Greedy S W l) (hl : l ≠ []) :
    deficit S W l ≤ (l.length : ℝ)*value (increments S W l) 0-(increments S W l).sum

axiom greedy_tail_bound {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι)
    (hg : Greedy S W l) (b : ℕ) (hb : 0 < b) (hbl : b ≤ l.length) :
    deficit S (spanAfter S W (l.take (l.length-b))) (l.drop (l.length-b)) ≤
      (b : ℝ)*tailDeficit (value (increments S W l)) l.length b

axiom small_greedy_tail {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι)
    (hg : Greedy S W l) (r : ℝ) (hr : ∀ i ∈ l, (Module.finrank K (S i) : ℝ) ≤ r)
    (k n : ℕ) (hlen : l.length = 2^k) (hnk : n ≤ k) (hn : 8*r < n) :
    ∃ j < n, deficit S (spanAfter S W (l.take (l.length-2^(k-j))))
      (l.drop (l.length-2^(k-j))) < (2^(k-j) : ℝ)/4

end Lax342547.GreedyTails
