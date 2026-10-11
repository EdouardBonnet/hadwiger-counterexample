import Lax342547.ActualDeficits
import Lax342547Proofs.ProjectedSpans
import Lax342547Proofs.GreedyTails

namespace Lax342547Proofs.ActualDeficits
open Lax342547.ActualDeficits

set_option backward.isDefEq.respectTransparency false
open Lax342547.GreedySpans Lax342547.GreedyTails
open scoped BigOperators

/--
---
conclusion: Lax342547.ActualDeficits.map_finset_sup
---
-/
theorem map_finset_sup {K V U ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    (S : ι → Submodule K V) (f : V →ₗ[K] U) (I : Finset ι) :
    (I.sup S).map f = I.sup (fun i => (S i).map f) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih => simp [Finset.sup_insert,Submodule.map_sup,ih]

/--
---
conclusion: Lax342547.ActualDeficits.projected_deficit_eq
---
-/
theorem projected_deficit_eq {K V ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) :
    projectedDeficit S W l = deficit S W l := by
  unfold projectedDeficit deficit
  simp_rw [Lax342547Proofs.ProjectedSpans.projected_dimension_gain]
  rw [← map_finset_sup,Lax342547Proofs.ProjectedSpans.projected_dimension_gain,
    Lax342547Proofs.GreedySpans.increments_sum,Lax342547Proofs.GreedySpans.span_after_eq]
  rfl

/--
---
conclusion: Lax342547.ActualDeficits.small_projected_tail
---
-/
theorem small_projected_tail {K V ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : ι → Submodule K V) (W : Submodule K V) (l : List ι)
    (hg : Greedy S W l) (r : ℝ) (hr : ∀ i ∈ l, (Module.finrank K (S i) : ℝ) ≤ r)
    (k n : ℕ) (hlen : l.length = 2^k) (hnk : n ≤ k) (hn : 8*r < n) :
    ∃ j < n, projectedDeficit S (spanAfter S W (l.take (l.length-2^(k-j))))
      (l.drop (l.length-2^(k-j))) < (2^(k-j) : ℝ)/4 := by
  simp_rw [projected_deficit_eq]
  exact Lax342547Proofs.GreedyTails.small_greedy_tail S W l hg r hr k n hlen hnk hn

end Lax342547Proofs.ActualDeficits
