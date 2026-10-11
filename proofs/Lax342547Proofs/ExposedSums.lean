import Lax342547.ExposedSums
import Lax342547.CoverProjection
import Lax342547.GreedySpans
import Lax342547.PartitionLists

namespace Lax342547Proofs.ExposedSums
open Lax342547.ExposedSums

set_option backward.isDefEq.respectTransparency false
open Lax342547.GreedySpans Lax342547.CoverProjection
open scoped BigOperators

/--
---
conclusion: Lax342547.ExposedSums.remaining_projection_sum
---
-/
theorem remaining_projection_sum {K V W ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : ι → V →ₗ[K] W) (l : List ι) (hl : l.Nodup) (hI : l.toFinset = Finset.univ) (t : ℕ) :
    let S := spanAfter (fun i => LinearMap.range (M i)) ⊥ (l.take t)
    let T := spanAfter (fun i => LinearMap.range (M i).dualMap) ⊥ (l.take t)
    projection (∑ i : (l.drop t).toFinset, M i.val) S T = projection (∑ i, M i) S T := by
  classical
  dsimp only
  let E := (l.take t).toFinset
  let J := (l.drop t).toFinset
  let S := spanAfter (fun i => LinearMap.range (M i)) ⊥ (l.take t)
  let T := spanAfter (fun i => LinearMap.range (M i).dualMap) ⊥ (l.take t)
  have hu : E ∪ J = Finset.univ := by
    rw [Lax342547.PartitionLists.take_drop_union,hI]
  have hd : Disjoint E J := Lax342547.PartitionLists.take_drop_disjoint l hl t
  have hz : ∀ i ∈ E, projection (M i) S T = 0 := by
    intro i hi
    apply Lax342547.CoverProjection.projection_zero_of_columns (M i) S T
    dsimp [S]
    rw [Lax342547.GreedySpans.span_after_eq,bot_sup_eq]
    exact Finset.le_sup (f := fun i => LinearMap.range (M i)) hi
  rw [Finset.sum_coe_sort (l.drop t).toFinset M]
  change projection (∑ i ∈ J, M i) S T = projection (∑ i, M i) S T
  rw [Lax342547.CoverProjection.projection_sum]
  have hsplit : (∑ i, projection (M i) S T) =
      (∑ i ∈ E, projection (M i) S T)+(∑ i ∈ J, projection (M i) S T) := by
    rw [← Finset.sum_union hd,hu]
  rw [hsplit,Finset.sum_eq_zero (fun i hi => hz i hi),zero_add]
  have he : projection (∑ i ∈ J, M i) S T = ∑ i ∈ J, projection (M i) S T := by
    ext v
    simp [projection]
  exact he

end Lax342547Proofs.ExposedSums
