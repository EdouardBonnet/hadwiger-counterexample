import Lax342547.RightQueryImages
import Lax342547Proofs.RawQueryImages
import Lax342547Proofs.PairedRecipes

namespace Lax342547Proofs.RightQueryImages
open Lax342547.RightQueryImages

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.PairedWitnesses Lax342547.PairedRecipes Lax342547.QueryReference
open Lax342547.ReferenceKeys Lax342547.ReferencePins Lax342547.KeySpans
open scoped ENNReal

/--
---
conclusion: Lax342547.RightQueryImages.reindex_injective
---
-/
theorem reindex_injective {k n b degree r : ℕ} {hr : 2 * r ≤ n} {N : Type}
    (W : Lists k n b degree r hr) : Function.Injective (reindexTuple (N := N) W) := by
  intro q q' h
  funext e
  apply Prod.ext
  · funext n p
    exact congrFun (congrFun (congrArg Prod.fst (congrFun h e)) n) ((flippedPosition W e).symm p)
  · funext n p
    exact congrFun (congrFun (congrArg Prod.snd (congrFun h e)) n) ((flippedPosition W e).symm p)

/--
---
conclusion: Lax342547.RightQueryImages.left_flip_right_tuple
---
-/
theorem left_flip_right_tuple {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (o : Unit (H := H) (N := N) (E := E)) :
    leftTuple (flip W) o = reindexTuple W (rightTuple W o) := by
  rfl

/--
---
conclusion: Lax342547.RightQueryImages.right_tuple_event
---
-/
theorem right_tuple_event {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (o : Unit (H := H) (N := N) (E := E))
    (q : Tuples (Lax342547.CutProfiles.Component (Tag k)) (ComponentPosition W) N) :
    rightTuple W o = q ↔ leftTuple (flip W) o = reindexTuple W q := by
  rw [left_flip_right_tuple]
  exact (reindex_injective W).eq_iff.symm

/--
---
conclusion: Lax342547.RightQueryImages.flipped_slot_count
---
-/
theorem flipped_slot_count {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) : by
      classical
      exact Fintype.card (Lax342547.QuerySlots.Slot (flip W)) =
        Fintype.card (Lax342547.QuerySlots.Slot W) := by
  classical
  rw [Lax342547Proofs.QueryReference.grouped_slot_count,
    Lax342547Proofs.QueryReference.grouped_slot_count]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact Fintype.card_congr (flippedPosition W e)

/--
---
conclusion: Lax342547.RightQueryImages.actual_right_key_cap
---
-/
theorem actual_right_key_cap {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
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
    p.toOuterMeasure {o | rightTuple W o = q} ≤ α ^ Fintype.card (Lax342547.QuerySlots.Slot W) := by
  classical
  have he : {o : Unit (H := H) (N := N) (E := E) | rightTuple W o = q} =
      {o : Unit (H := H) (N := N) (E := E) | leftTuple (flip W) o = reindexTuple W q} := by
    ext o
    exact right_tuple_event W o q
  rw [he]
  have h := Lax342547Proofs.RawQueryImages.actual_left_key_cap (flip W) p P B hB
    (fun i z t => hfresh z i t) (reindexTuple W q) α hcap
    (by rw [flipped_slot_count]; exact hrank)
  simpa only [flipped_slot_count] using h

end Lax342547Proofs.RightQueryImages
