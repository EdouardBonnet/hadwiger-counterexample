import Lax342547.ProjectedSpans
import Lax342547.GreedyTails

/-!
---
title: Actual projected span deficit
type: lemma
---
The projected-space dimension deficit equals the greedy tail statistic, so the small-tail conclusion concerns actual quotient spaces.
-/

namespace Lax342547.ActualDeficits

open Lax342547.GreedySpans Lax342547.GreedyTails
open scoped BigOperators

noncomputable def projectedDeficit {K V ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) : ℝ :=
    (l.map (fun i => (Module.finrank K ((S i).map W.mkQ) : ℝ))).sum-
      Module.finrank K (l.toFinset.sup (fun i => (S i).map W.mkQ) : Submodule K (V ⧸ W))

axiom map_finset_sup {K V U ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    (S : ι → Submodule K V) (f : V →ₗ[K] U) (I : Finset ι) :
    (I.sup S).map f = I.sup (fun i => (S i).map f)

axiom projected_deficit_eq {K V ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) :
    projectedDeficit S W l = deficit S W l

axiom small_projected_tail {K V ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : ι → Submodule K V) (W : Submodule K V) (l : List ι)
    (hg : Greedy S W l) (r : ℝ) (hr : ∀ i ∈ l, (Module.finrank K (S i) : ℝ) ≤ r)
    (k n : ℕ) (hlen : l.length = 2^k) (hnk : n ≤ k) (hn : 8*r < n) :
    ∃ j < n, projectedDeficit S (spanAfter S W (l.take (l.length-2^(k-j))))
      (l.drop (l.length-2^(k-j))) < (2^(k-j) : ℝ)/4

end Lax342547.ActualDeficits
