import Lax342547.CutSparsity
import Lax342547.ConcreteCut
import Lax342547.TensorIntersections

/-!
---
title: Sparse normalized representatives of shared concrete tensors
type: lemma
---
Low total component rank yields a unique representative vanishing at a
strict majority of tags, with the quantitative support bound. Shared
ambient tensors have equal chiStar values on these representatives.
-/

namespace Lax342547.SparseRepresentatives

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles Lax342547.CutSparsity Lax342547.ConcreteCut
open Lax342547.RawFrames Lax342547.TensorIntersections

def Normalized {k n b degree : ℕ} (x : Profile k n b degree)
    (w : Representation k n b degree) : Prop :=
  representationCut k n b degree w = x.val ∧
    2 * k + 1 < 2 * valueCount w.val 0

axiom cutSize_le_rank {Tag I : Type} [Fintype Tag] [Fintype I]
    [Fintype (Component Tag)] (w : Tag → Matrix I I Binary) :
    cutSize w ≤ ∑ e : Component Tag, (cutMap w e).rank

axiom normalized_representation {k n b degree : ℕ} (R : ℕ)
    (hsmall : 4 * R < (2 * k + 1) * (2 * k + 1)) (x : Profile k n b degree)
    (hrank : (∑ e, (x.val e).rank) ≤ R) :
    ∃! w : Representation k n b degree, Normalized x w ∧
      (2 * k + 1) * supportSize w.val ≤ 2 * R

axiom shared_chiStar {k n b degree r h N : ℕ}
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (F G : Component (Tag k) → Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M))
    (w v : Representation k n b degree)
    (hw : 2 * k + 1 < 2 * valueCount w.val 0)
    (hv : 2 * k + 1 < 2 * valueCount v.val 0)
    (heq : profileMap F (representationCut k n b degree w) =
      profileMap G (representationCut k n b degree v)) :
    chiStar hr w = chiStar hr v

axiom shared_sparse_profiles {k n b degree r h N : ℕ}
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree) (M : Fin b → Matrix (Fin n) (Fin n) Binary)
    (F G : Component (Tag k) → Frame (Coordinate k n b degree) (Fin h) (Fin N) (selfGram hr hd M))
    (R : ℕ) (hsmall : 4 * R < (2 * k + 1) * (2 * k + 1))
    (hinter : (∑ e, Module.finrank Binary (intersectionSpace (F e).P (G e).P)) ≤ R)
    (x y : Profile k n b degree) (heq : profileMap F x.val = profileMap G y.val) :
    ∃ w v : Representation k n b degree, Normalized x w ∧ Normalized y v ∧
      (2 * k + 1) * supportSize w.val ≤ 2 * R ∧
      (2 * k + 1) * supportSize v.val ≤ 2 * R ∧ chiStar hr w = chiStar hr v

end Lax342547.SparseRepresentatives
