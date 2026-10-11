import Lax342547.RawQueryImages
import Lax342547.LeafImages
import Lax342547.QueryIndependence
import Lax342547.QueryReference
import Lax342547Proofs.PairedFrames

namespace Lax342547Proofs.RawQueryImages
open Lax342547.RawQueryImages

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ReferencePins
open Lax342547.TableSpaces Lax342547.ProductImages Lax342547.TagGeometry
open Lax342547.ConcreteGeometry Lax342547.PairedWitnesses Lax342547.QueryReference
open Lax342547.QueryIndependence Lax342547.PairedKeys Lax342547.KeySpans

/--
---
conclusion: Lax342547.RawQueryImages.observation_primal_plus
---
-/
theorem observation_primal_plus {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (e : Comp) (i : Fin 2) (v : B → Binary) :
    observation o (e,true) (primalEmbedding i v) = (o i e).P.mulVec v := by
  classical
  ext n
  simp [observation, observationMatrix, jointMatrix, primalEmbedding, Lax342547.FrameSymmetry.plus,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type, mul_ite]

/--
---
conclusion: Lax342547.RawQueryImages.observation_primal_minus
---
-/
theorem observation_primal_minus {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (e : Comp) (i : Fin 2) (v : B → Binary) :
    observation o (e,false) (primalEmbedding i v) = (o i e).Q.mulVec v := by
  classical
  ext n
  simp [observation, observationMatrix, jointMatrix, primalEmbedding, Lax342547.FrameSymmetry.minus,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type, mul_ite]

/--
---
conclusion: Lax342547.RawQueryImages.key_map_coordinate
---
-/
theorem key_map_coordinate {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H : Type}
    (W : Lists k n b degree r hr) (e : Lax342547.CutProfiles.Component (Tag k))
    (p : ComponentPosition W e) : by
      classical
      exact keyMap (H := H) W e (Pi.single p 1) =
        primalEmbedding p.val.1 (W.left p.val.1 p.val.2.1 p.val.2.2).vector := by
  classical
  unfold keyMap
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp [ray, labels, bases, Lax342547.WitnessAtoms.PointAtom.vector, Pi.single_apply]

/--
---
conclusion: Lax342547.RawQueryImages.key_observations_left
---
-/
theorem key_observations_left {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (o : Unit (H := H) (N := N) (E := E))
    (e : Lax342547.CutProfiles.Component (Tag k)) (mode : Bool) : by
      classical
      exact LinearMap.toMatrix' ((observation o (e,mode)).comp (keyMap (H := H) W e)) =
        if mode then (leftTuple W o e).1 else (leftTuple W o e).2 := by
  classical
  ext n p
  simp only [LinearMap.toMatrix'_apply, LinearMap.comp_apply, Lax342547.RawQueryImages.key_map_coordinate]
  cases mode
  · rw [Lax342547.RawQueryImages.observation_primal_minus]
    rfl
  · rw [Lax342547.RawQueryImages.observation_primal_plus]
    rfl

/--
---
conclusion: Lax342547.RawQueryImages.left_tuple_event
---
-/
theorem left_tuple_event {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (q : Lax342547.ReferenceKeys.Tuples
      (Lax342547.CutProfiles.Component (Tag k)) (ComponentPosition W) N)
    (o : Unit (H := H) (N := N) (E := E)) :
    leftTuple W o = q ↔ ∀ a, (observation o a).comp (keyMap (H := H) W a.1) = tupleMaps W q a := by
  classical
  constructor
  · intro h a
    apply LinearMap.toMatrix'.injective
    rw [Lax342547.RawQueryImages.key_observations_left, h]
    unfold tupleMaps
    exact (Lax342547Proofs.PairedFrames.toMatrix_mulVecLin _).symm
  · intro h
    funext e
    apply Prod.ext
    · have ht := congrArg LinearMap.toMatrix' (h (e,true))
      rw [Lax342547.RawQueryImages.key_observations_left] at ht
      simpa [tupleMaps, Lax342547Proofs.PairedFrames.toMatrix_mulVecLin] using ht
    · have ht := congrArg LinearMap.toMatrix' (h (e,false))
      rw [Lax342547.RawQueryImages.key_observations_left] at ht
      simpa [tupleMaps, Lax342547Proofs.PairedFrames.toMatrix_mulVecLin] using ht

/--
---
conclusion: Lax342547.RawQueryImages.key_dimension
---
-/
theorem key_dimension {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) : by
      classical
      exact (∑ a : Lax342547.CutProfiles.Component (Tag k) × Bool,
        Module.finrank Binary (ComponentPosition W a.1 → Binary)) =
        Fintype.card (Lax342547.QuerySlots.Slot W) := by
  classical
  rw [Lax342547.QueryReference.grouped_slot_count]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Module.finrank_pi_fintype,
    Module.finrank_self, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Finset.sum_add_distrib]
  simp only [Nat.cast_id]
  ring

open scoped ENNReal

/--
---
conclusion: Lax342547.RawQueryImages.actual_left_key_cap
---
-/
theorem actual_left_key_cap {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr)
    (p : PMF (Unit (H := H) (N := N) (E := E)))
    (P : Lax342547.ExactPins.Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (q : Lax342547.ReferenceKeys.Tuples (Lax342547.CutProfiles.Component (Tag k)) (ComponentPosition W) N)
    (α : ℝ≥0∞)
    (hcap : ∀ Q : Lax342547.ExactPins.Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N,
      1 ≤ P.relativeRank Q → p.toOuterMeasure (Q.event observation) ≤ α ^ (P.relativeRank Q))
    (hr : 1 ≤ Fintype.card (Lax342547.QuerySlots.Slot W)) :
    p.toOuterMeasure {o | leftTuple W o = q} ≤ α ^ Fintype.card (Lax342547.QuerySlots.Slot W) := by
  classical
  have he : {o : Unit (H := H) (N := N) (E := E) | leftTuple W o = q} =
      {o : Unit (H := H) (N := N) (E := E) | ∀ a,
        (observation o a).comp (keyMap (H := H) W a.1) = tupleMaps W q a} := by
    ext o
    exact Lax342547.RawQueryImages.left_tuple_event W q o
  rw [he]
  have h := Lax342547.LeafImages.leaf_tuple_image_cap p observation P
    (fun a => keyMap (H := H) W a.1)
    (Lax342547.QueryIndependence.actual_key_independence W P A hA hfresh)
    (tupleMaps W q) α hcap (by rw [Lax342547.RawQueryImages.key_dimension]; exact hr)
  simpa only [Lax342547.RawQueryImages.key_dimension] using h

end Lax342547Proofs.RawQueryImages
