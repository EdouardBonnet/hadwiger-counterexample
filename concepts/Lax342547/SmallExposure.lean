import Lax342547.CombinedSpans

/-!
---
title: One exposure controls both modes
type: lemma
---
Finite greedy ordering of the product of column and row spaces supplies one dyadic exposed set with combined actual deficit less than one quarter of its remaining size.
-/

namespace Lax342547.SmallExposure

open Lax342547.GreedySpans Lax342547.GreedyTails
open scoped BigOperators

axiom simultaneous_small_exposure {K V W ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (C : ι → Submodule K V) (R : ι → Submodule K W) (r : ℝ) (k n : ℕ)
    (hC : ∀ i, (Module.finrank K (C i) : ℝ) ≤ r)
    (hR : ∀ i, (Module.finrank K (R i) : ℝ) ≤ r)
    (hcard : Fintype.card ι = 2^k) (hnk : n ≤ k) (hn : 16*r < n) :
    ∃ l : List ι, l.Nodup ∧ l.toFinset = Finset.univ ∧ ∃ j < n,
      deficit C (spanAfter C ⊥ (l.take (l.length-2^(k-j)))) (l.drop (l.length-2^(k-j)))+
      deficit R (spanAfter R ⊥ (l.take (l.length-2^(k-j)))) (l.drop (l.length-2^(k-j))) <
        (2^(k-j) : ℝ)/4

end Lax342547.SmallExposure
