import Lax342547.RawQueryImages
import Lax342547.PairedRecipes

/-!
---
title: Right endpoint query-key caps via paired-list reindexing
type: lemma
---
The flipped paired lists reindex the same incident positions and slots. Their actual left-key cap therefore gives the right-key cap with exactly the original exponent.
-/

namespace Lax342547.RightQueryImages

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.PairedWitnesses Lax342547.PairedRecipes Lax342547.QueryReference
open Lax342547.ReferenceKeys Lax342547.ReferencePins Lax342547.KeySpans
open scoped ENNReal

noncomputable def flippedPosition {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) (e : Lax342547.CutProfiles.Component (Tag k)) :
    ComponentPosition (flip W) e ≃ ComponentPosition W e where
  toFun p := ⟨⟨p.val.2.1,p.val.1,p.val.2.2⟩, by
    have h := p.property
    change (W.right p.val.2.1 p.val.1 p.val.2.2).tag ∈ e.val at h
    rwa [W.same_tag]⟩
  invFun p := ⟨⟨p.val.2.1,p.val.1,p.val.2.2⟩, by
    change (W.right p.val.1 p.val.2.1 p.val.2.2).tag ∈ e.val
    rw [← W.same_tag]
    exact p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def reindexTuple {k n b degree r : ℕ} {hr : 2 * r ≤ n} {N : Type}
    (W : Lists k n b degree r hr)
    (q : Tuples (Lax342547.CutProfiles.Component (Tag k)) (ComponentPosition W) N) :
    Tuples (Lax342547.CutProfiles.Component (Tag k)) (ComponentPosition (flip W)) N :=
  fun e => ⟨fun n p => (q e).1 n (flippedPosition W e p),
    fun n p => (q e).2 n (flippedPosition W e p)⟩

axiom reindex_injective {k n b degree r : ℕ} {hr : 2 * r ≤ n} {N : Type}
    (W : Lists k n b degree r hr) : Function.Injective (reindexTuple (N := N) W)

axiom left_flip_right_tuple {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (o : Unit (H := H) (N := N) (E := E)) :
    leftTuple (flip W) o = reindexTuple W (rightTuple W o)

axiom right_tuple_event {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (o : Unit (H := H) (N := N) (E := E))
    (q : Tuples (Lax342547.CutProfiles.Component (Tag k)) (ComponentPosition W) N) :
    rightTuple W o = q ↔ leftTuple (flip W) o = reindexTuple W q

axiom flipped_slot_count {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) : by
      classical
      exact Fintype.card (Lax342547.QuerySlots.Slot (flip W)) =
        Fintype.card (Lax342547.QuerySlots.Slot W)

axiom actual_right_key_cap {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr)
    (p : PMF (Unit (H := H) (N := N) (E := E)))
    (P : Lax342547.ExactPins.Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (B : Fin 2 → Finset (Fin b → Binary)) (hB : Excludes P B)
    (hfresh : ∀ i z t, (W.right i z t).label ∉ B z)
    (q : Tuples (Lax342547.CutProfiles.Component (Tag k)) (ComponentPosition W) N)
    (α : ℝ≥0∞)
    (hcap : ∀ Q : Lax342547.ExactPins.Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N,
      1 ≤ P.relativeRank Q → p.toOuterMeasure (Q.event observation) ≤ α ^ (P.relativeRank Q))
    (hrank : 1 ≤ Fintype.card (Lax342547.QuerySlots.Slot W)) :
    p.toOuterMeasure {o | rightTuple W o = q} ≤ α ^ Fintype.card (Lax342547.QuerySlots.Slot W)

end Lax342547.RightQueryImages
