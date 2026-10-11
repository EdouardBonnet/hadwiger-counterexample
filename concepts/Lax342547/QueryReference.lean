import Lax342547.QuerySlots
import Lax342547.ReferenceKeys
import Lax342547.PairedWitnesses

/-!
---
title: Reference keys and matched keys for actual paired lists
type: lemma
---
Global key tuples contain both nominal signs of every actual incident witness direction. Their equality gives matched keys; the constrained reference space has the exact slot cardinality bound and a dimension-independent positive density.
-/

namespace Lax342547.QueryReference

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.CutProfiles
open Lax342547.PairedWitnesses Lax342547.QuerySlots Lax342547.ReferenceKeys
open Lax342547.ConcreteGeometry
open scoped ENNReal

abbrev ComponentPosition {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) (e : Component (Tag k)) :=
  {p : Lax342547.QuerySlots.Position W // (W.left p.1 p.2.1 p.2.2).tag ∈ e.val}

noncomputable def groupedSlots {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) :
    Slot W ≃ (Σ e : Component (Tag k), ComponentPosition W e × Bool) where
  toFun x := ⟨x.2.1.val, ⟨⟨x.1, x.2.1.property⟩, x.2.2⟩⟩
  invFun x := ⟨x.2.1.val, ⟨⟨x.1, x.2.1.property⟩, x.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def gram {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) (e : Component (Tag k)) :
    Matrix (ComponentPosition W e) (ComponentPosition W e) Binary := by
  classical
  exact fun p q => if p.val = q.val then diagonalBit hr (W.left p.val.1 p.val.2.1 p.val.2.2) else 0

noncomputable def leftTuple {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (o : Unit (H := H) (N := N) (E := E)) :
    Tuples (Component (Tag k)) (ComponentPosition W) N := fun e =>
  ⟨fun n p => (o p.val.1 e).P.mulVec (W.left p.val.1 p.val.2.1 p.val.2.2).vector n,
    fun n p => (o p.val.1 e).Q.mulVec (W.left p.val.1 p.val.2.1 p.val.2.2).vector n⟩

noncomputable def rightTuple {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (o : Unit (H := H) (N := N) (E := E)) :
    Tuples (Component (Tag k)) (ComponentPosition W) N := fun e =>
  ⟨fun n p => (o p.val.2.1 e).P.mulVec (W.right p.val.1 p.val.2.1 p.val.2.2).vector n,
    fun n p => (o p.val.2.1 e).Q.mulVec (W.right p.val.1 p.val.2.1 p.val.2.2).vector n⟩

axiom tuple_equality_matched_keys {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (oA oB : Unit (H := H) (N := N) (E := E))
    (h : leftTuple W oA = rightTuple W oB) : MatchedKeys W oA oB

axiom component_position_budget {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) (e : Component (Tag k)) : by
      classical
      exact Fintype.card (ComponentPosition W e) ≤ 28

axiom grouped_slot_count {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) : by
      classical
      exact Fintype.card (Slot W) = 2 * ∑ e, Fintype.card (ComponentPosition W e)

axiom key_space_size {k n b degree r : ℕ} {hr : 2 * r ≤ n} {N : Type} [Fintype N]
    (W : Lists k n b degree r hr) : by
      classical
      exact Fintype.card (space (ComponentPosition W) N (gram W)) ≤
        2 ^ (Fintype.card (Slot W) * Fintype.card N)

axiom key_space_density {k n b degree r : ℕ} {hr : 2 * r ≤ n} {N : Type} [Fintype N]
    (W : Lists k n b degree r hr) (hN : 57 ≤ Fintype.card N) : by
      classical
      exact (∏ e, 1 / (2 : ℝ≥0∞)^
        (Fintype.card (ComponentPosition W e) * Fintype.card (ComponentPosition W e) + 2)) ≤
        (PMF.uniformOfFintype (Tuples (Component (Tag k)) (ComponentPosition W) N)).toOuterMeasure
          (space (ComponentPosition W) N (gram W))

end Lax342547.QueryReference
