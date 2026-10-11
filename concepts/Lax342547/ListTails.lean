import Lax342547.GreedySpans
import Lax342547.DyadicTails
import Mathlib.Data.List.Sort

/-!
---
title: Finite list tail statistics
type: definition and theorem
---
Nonnegative decreasing finite lists extend by zero to decreasing sequences; their finite sums and dyadic tail sums agree with the actual list tails.
-/

namespace Lax342547.ListTails

open scoped BigOperators

noncomputable def value (l : List ℝ) (t : ℕ) : ℝ := l[t]?.getD 0

axiom value_in_range (l : List ℝ) (t : ℕ) (ht : t < l.length) : value l t = l[t]

axiom value_out_of_range (l : List ℝ) (t : ℕ) (ht : l.length ≤ t) : value l t = 0

axiom value_nonneg (l : List ℝ) (h : ∀ x ∈ l, 0 ≤ x) (t : ℕ) : 0 ≤ value l t

axiom value_antitone (l : List ℝ) (h : l.Pairwise (fun a b => b ≤ a))
    (h0 : ∀ x ∈ l, 0 ≤ x) : Antitone (value l)

axiom value_drop (l : List ℝ) (n t : ℕ) : value (l.drop n) t = value l (n+t)

axiom sum_values (l : List ℝ) : (∑ t ∈ Finset.range l.length, value l t) = l.sum

axiom tail_sum_list (l : List ℝ) (b : ℕ) (hb : b ≤ l.length) :
    Lax342547.DyadicTails.tailSum (value l) l.length b = (l.drop (l.length-b)).sum

end Lax342547.ListTails
