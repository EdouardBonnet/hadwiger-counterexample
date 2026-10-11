import Lax342547.NoCoverCertificate
import Lax342547.CoverCounts
import Lax342547.CoverProjection
import Lax342547.ExposedSums
import Lax342547.GreedySpans
import Lax342547.PartitionLists
import Lax342547.ProjectedCounts
import Lax342547.SmallExposure

namespace Lax342547Proofs.NoCoverCertificate
open Lax342547.NoCoverCertificate

set_option backward.isDefEq.respectTransparency false
open Lax342547.GreedySpans Lax342547.GreedyTails Lax342547.CoverProjection
open scoped BigOperators

/--
---
conclusion: Lax342547.NoCoverCertificate.low_rank_cover_certificate
---
-/
theorem low_rank_cover_certificate {K V W ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : ι → V →ₗ[K] W) (r : ℝ) (k n : ℕ)
    (hM : ∀ i, (Module.finrank K (LinearMap.range (M i)) : ℝ) ≤ r)
    (hcard : Fintype.card ι = 2^k) (hnk : n ≤ k) (hn : 16*r < n)
    (hlow : (Module.finrank K (LinearMap.range (∑ i, M i)) : ℝ) < (2^(k-n) : ℝ)/4) :
    ∃ E J : Finset ι, Disjoint E J ∧ 2^(k-n) ≤ J.card ∧
      ∀ j ∈ J, projection (M j) (E.sup (fun i => LinearMap.range (M i)))
        (E.sup (fun i => LinearMap.range (M i).dualMap)) = 0 := by
  classical
  let C := fun i => LinearMap.range (M i)
  let R := fun i => LinearMap.range (M i).dualMap
  have hR : ∀ i, (Module.finrank K (R i) : ℝ) ≤ r := by
    intro i
    simpa only [R,LinearMap.finrank_range_dualMap_eq_finrank_range] using hM i
  obtain ⟨l,hl,hI,j,hj,hd⟩ := Lax342547.SmallExposure.simultaneous_small_exposure C R r k n hM hR hcard hnk hn
  let b := (2 : ℕ)^(k-j)
  let t := l.length-b
  let E := (l.take t).toFinset
  let F := (l.drop t).toFinset
  let S := spanAfter C ⊥ (l.take t)
  let T := spanAfter R ⊥ (l.take t)
  have hlen : l.length = 2^k := by rw [← List.toFinset_card_of_nodup hl,hI,Finset.card_univ,hcard]
  have hbl : b ≤ l.length := by rw [hlen]; exact Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have hbt : 2*2^(k-n) ≤ b := by
    have hpow : 2*2^(k-n) = (2 : ℕ)^(k-n+1) := by rw [pow_succ]; omega
    rw [hpow]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hF : F.card = b := Lax342547.PartitionLists.take_drop_card l hl b hbl
  have hST : deficit C S (l.drop t)+deficit R T (l.drop t) < (b : ℝ)/4 := by
    simpa only [S,T,t,b,Nat.cast_pow,Nat.cast_ofNat] using hd
  have hc := Lax342547.ProjectedCounts.projected_nonzero_count M S T (l.drop t) (hl.drop)
  have hc' : ((F.filter (fun i => projection (M i) S T ≠ 0)).card : ℝ) ≤
      Module.finrank K (LinearMap.range (projection (∑ i : F, M i.val) S T))+
      deficit C S (l.drop t)+deficit R T (l.drop t) := by
    convert hc using 1
    congr 1
    simp only [Finset.card_filter]
    rw [Finset.sum_coe_sort (l.drop t).toFinset (fun i => if projection (M i) S T ≠ 0 then (1 : ℕ) else 0)]
  have hs : projection (∑ i : F, M i.val) S T = projection (∑ i, M i) S T :=
    Lax342547.ExposedSums.remaining_projection_sum M l hl hI t
  rw [hs] at hc'
  have hr := Lax342547.CoverProjection.projection_rank_le (∑ i, M i) S T
  have hr' : (Module.finrank K (LinearMap.range (projection (∑ i, M i) S T)) : ℝ) < (2^(k-n) : ℝ)/4 := by
    have hr'' : (Module.finrank K (LinearMap.range (projection (∑ i, M i) S T)) : ℝ) ≤
        Module.finrank K (LinearMap.range (∑ i, M i)) := by exact_mod_cast hr
    exact hr''.trans_lt hlow
  have hz := Lax342547.CoverCounts.covered_count_lower_bound F
    (fun i => projection (M i) S T ≠ 0) b (2^(k-n))
    (Module.finrank K (LinearMap.range (projection (∑ i, M i) S T)))
    (deficit C S (l.drop t)+deficit R T (l.drop t)) hF hbt (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hr') hST (by
      convert hc' using 1
      · congr 2
        ext i
        simp
      · ring)
  let J := F.filter (fun i => projection (M i) S T = 0)
  have hJ : 2^(k-n) ≤ J.card := by simpa only [not_not] using hz
  refine ⟨E,J,?_,hJ,?_⟩
  · exact (Lax342547.PartitionLists.take_drop_disjoint l hl t).mono_right (Finset.filter_subset _ _)
  · intro i hi
    have heq := (Finset.mem_filter.mp hi).2
    have hS : S = E.sup C := by simp only [S,E,Lax342547.GreedySpans.span_after_eq,bot_sup_eq]
    have hT : T = E.sup R := by simp only [T,E,Lax342547.GreedySpans.span_after_eq,bot_sup_eq]
    rw [hS,hT] at heq
    exact heq

end Lax342547Proofs.NoCoverCertificate
