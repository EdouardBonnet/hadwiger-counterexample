import Lax342547.SparseRepresentatives
import Lax342547Proofs.CutSparsity
import Lax342547Proofs.TagGeometry
import Lax342547Proofs.SlotWalsh
import Lax342547.ConcreteGeometry
import Lax342547.CutSparsity
import Lax342547.TagGeometry
import Lax342547.TensorIntersections
import Lax342547Proofs.CutProfiles
import Lax342547Proofs.MomentSpace

namespace Lax342547Proofs.SparseRepresentatives

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles Lax342547.CutSparsity Lax342547.ConcreteCut
open Lax342547.RawFrames Lax342547.TensorIntersections Lax342547.SparseRepresentatives

/--
---
conclusion: Lax342547.SparseRepresentatives.cutSize_le_rank
---
Each nonzero cut matrix has rank at least one. Sum this inequality
over the unordered components, counting the zero matrices as zero.
-/
theorem cutSize_le_rank {Tag I : Type} [Fintype Tag] [Fintype I]
    [Fintype (Component Tag)] (w : Tag → Matrix I I Binary) :
    cutSize w ≤ ∑ e : Component Tag, (cutMap w e).rank := by
  classical
  have hc : cutSize w = ∑ e : Component Tag, if cutMap w e = 0 then 0 else 1 := by
    unfold cutSize NonzeroCuts
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp_all
  rw [hc]
  apply Finset.sum_le_sum
  intro e _
  split_ifs with he
  · exact Nat.zero_le _
  · exact SlotWalsh.rank_pos_of_ne_zero _ he

theorem tag_majority_intersection {k n b degree : ℕ} (S : Finset (Tag k))
    (hS : Fintype.card (Tag k) < 2 * S.card) :
    (⨅ t : {t // t ∈ S}, tagSpace k n b degree t.val) ≤ ⨅ t, tagSpace k n b degree t := by
  have hS' : k < S.card := by
    have hn : 2 * k + 1 < 2 * S.card := by simpa only [Tag, ZMod.card] using hS
    omega
  change (⨅ t : {t // t ∈ S}, momentSpace selectorEval (allowedBase k n t.val)) ≤
    ⨅ t : Tag k, momentSpace selectorEval (allowedBase k n t)
  rw [Lax342547.TagGeometry.majority_intersection k n selectorEval S hS',
    TagGeometry.all_tag_intersection k n selectorEval]

/--
---
conclusion: Lax342547.SparseRepresentatives.normalized_representation
---
Apply majority normalization to an actual restricted cut representative.
The cyclic majority-intersection theorem supplies exactly the subspace
condition required to translate its majority value to zero.
-/
theorem normalized_representation {k n b degree : ℕ} (R : ℕ)
    (hsmall : 4 * R < (2 * k + 1) * (2 * k + 1)) (x : Profile k n b degree)
    (hrank : (∑ e, (x.val e).rank) ≤ R) :
    ∃! w : Representation k n b degree, Normalized x w ∧
      (2 * k + 1) * supportSize w.val ≤ 2 * R := by
  obtain ⟨w, hwx⟩ := x.property
  have hw : ∀ t, w.val t ∈ tagSpace k n b degree t := by
    simpa only [representatives, Submodule.mem_pi, Set.mem_univ, forall_const] using w.property
  have hcut : cutMap w.val = x.val := hwx
  have hcount : cutSize w.val ≤ R := by
    have hc := Lax342547.SparseRepresentatives.cutSize_le_rank w.val
    rw [hcut] at hc
    exact hc.trans hrank
  have hs : 4 * cutSize w.val < Fintype.card (Tag k) * Fintype.card (Tag k) := by
    simpa only [Tag, ZMod.card] using lt_of_le_of_lt (Nat.mul_le_mul_left 4 hcount) hsmall
  obtain ⟨v, hv, _⟩ := Lax342547.CutSparsity.exists_unique_normalized (tagSpace k n b degree)
    tag_majority_intersection w.val hw hs
  let v' : Representation k n b degree := ⟨v, by
    simpa only [representatives, Submodule.mem_pi, Set.mem_univ, forall_const] using hv.1⟩
  have hvmajor : 2 * k + 1 < 2 * valueCount v 0 := by simpa only [Tag, ZMod.card] using hv.2.2.1
  refine ⟨v', ⟨⟨hv.2.1.trans hcut, hvmajor⟩, ?_⟩, ?_⟩
  · have hb := hv.2.2.2.trans (Nat.mul_le_mul_left 2 hcount)
    simpa only [Tag, ZMod.card] using hb
  · intro u hu
    apply Subtype.ext
    apply Lax342547.CutSparsity.majority_unique u.val v
    · exact hu.1.1.trans (hv.2.1.trans hcut).symm
    · simpa only [Tag, ZMod.card] using hu.1.2
    · exact hv.2.2.1

theorem representative_full_moment {k n b degree : ℕ}
    (w : Representation k n b degree) (t : Tag k) :
    w.val t ∈ momentSpace selectorEval Set.univ := by
  have hw : ∀ t, w.val t ∈ tagSpace k n b degree t := by
    simpa only [representatives, Submodule.mem_pi, Set.mem_univ, forall_const] using w.property
  exact MomentSpace.momentSpace_mono selectorEval (Set.subset_univ _) (hw t)

theorem cut_full_moment {k n b degree : ℕ}
    (w : Representation k n b degree) (e : Component (Tag k)) :
    representationCut k n b degree w e ∈ momentSpace selectorEval Set.univ := by
  change (∑ t ∈ e.val, w.val t) ∈ _
  exact Submodule.sum_mem _ (fun t _ => representative_full_moment w t)

/--
---
conclusion: Lax342547.SparseRepresentatives.shared_chiStar
---
The trace identity and concrete self-Gram identity equate eta on every
component of the two shared tensors. The eta-valued representatives
therefore differ by a constant. Their majority zero sets intersect,
forcing that constant to vanish before summing the values over tags.
-/
theorem shared_chiStar {k n b degree r h N : ℕ}
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (F G : Component (Tag k) → Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M))
    (w v : Representation k n b degree)
    (hw : 2 * k + 1 < 2 * valueCount w.val 0)
    (hv : 2 * k + 1 < 2 * valueCount v.val 0)
    (heq : profileMap F (representationCut k n b degree w) =
      profileMap G (representationCut k n b degree v)) :
    chiStar hr w = chiStar hr v := by
  have he (e : Component (Tag k)) : eta hr (cutMap w.val e) = eta hr (cutMap v.val e) := by
    have ht := congrArg Matrix.trace (congrFun heq e)
    change Matrix.trace (sandwich (F e).P (F e).Q (representationCut k n b degree w e)) =
      Matrix.trace (sandwich (G e).P (G e).Q (representationCut k n b degree v e)) at ht
    rw [Lax342547.TensorIntersections.trace_sandwich, Lax342547.TensorIntersections.trace_sandwich,
      Lax342547.ConcreteGeometry.selfGram_moments hr hd M _ (cut_full_moment w e),
      Lax342547.ConcreteGeometry.selfGram_moments hr hd M _ (cut_full_moment v e)] at ht
    exact ht
  have hc : cutMap (fun t => eta hr (w.val t)) = cutMap (fun t => eta hr (v.val t)) := by
    funext e
    simpa only [cutMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum] using he e
  obtain ⟨c, hconst⟩ := (CutProfiles.cutMap_eq_iff _ _).mp hc
  obtain ⟨t, ht, ht'⟩ := CutSparsity.exists_common_zero w.val v.val
    (by simpa only [Tag, ZMod.card] using hw) (by simpa only [Tag, ZMod.card] using hv)
  have hzero : c = 0 := by simpa only [ht, ht', map_zero, zero_add] using (hconst t).symm
  have heta (i : Tag k) : eta hr (w.val i) = eta hr (v.val i) :=
    sub_eq_zero.mp (by simpa only [ZModModule.sub_eq_add, hzero] using hconst i)
  simp only [chiStar, LinearMap.sum_apply, LinearMap.comp_apply, representativeAt,
    LinearMap.proj_apply, Submodule.subtype_apply, heta]

/--
---
conclusion: Lax342547.SparseRepresentatives.shared_sparse_profiles
---
The intersection bound controls both total profile ranks. Normalize each
profile, retain its support bound, and apply the shared-trace conclusion.
-/
theorem shared_sparse_profiles {k n b degree r h N : ℕ}
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (F G : Component (Tag k) → Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M))
    (R : ℕ) (hsmall : 4 * R < (2 * k + 1) * (2 * k + 1))
    (hinter : (∑ e, Module.finrank Binary (intersectionSpace (F e).P (G e).P)) ≤ R)
    (x y : Profile k n b degree) (heq : profileMap F x.val = profileMap G y.val) :
    ∃ w v : Representation k n b degree, Normalized x w ∧ Normalized y v ∧
      (2 * k + 1) * supportSize w.val ≤ 2 * R ∧
      (2 * k + 1) * supportSize v.val ≤ 2 * R ∧ chiStar hr w = chiStar hr v := by
  have hrank := Lax342547.TensorIntersections.shared_total_rank F G x.val y.val heq
  obtain ⟨w, hw, _⟩ := Lax342547.SparseRepresentatives.normalized_representation R hsmall x (hrank.2.trans hinter)
  obtain ⟨v, hv, _⟩ := Lax342547.SparseRepresentatives.normalized_representation R hsmall y
    (by rw [← hrank.1]; exact hrank.2.trans hinter)
  refine ⟨w, v, hw.1, hv.1, hw.2, hv.2, Lax342547.SparseRepresentatives.shared_chiStar hr hd M F G w v hw.1.2 hv.1.2 ?_⟩
  rw [hw.1.1, hv.1.1]
  exact heq

end Lax342547Proofs.SparseRepresentatives
