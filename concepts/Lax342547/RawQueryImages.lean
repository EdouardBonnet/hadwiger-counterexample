import Lax342547.QueryIndependence
import Lax342547.ReferencePins
import Lax342547.LeafImages

/-!
---
title: Actual query-key image caps on raw leaves
type: definition and theorem
---
The raw paired-frame observation maps realize the selected query tuples. Their independence modulo old pins transfers exact leaf caps to actual key events.
-/

namespace Lax342547.RawQueryImages

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ReferencePins
open Lax342547.TableSpaces Lax342547.ProductImages Lax342547.TagGeometry
open Lax342547.ConcreteGeometry Lax342547.PairedWitnesses Lax342547.QueryReference
open Lax342547.QueryIndependence Lax342547.PairedKeys Lax342547.KeySpans
open scoped ENNReal

axiom observation_primal_plus {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (e : Comp) (i : Fin 2) (v : B → Binary) :
    observation o (e,true) (primalEmbedding i v) = (o i e).P.mulVec v

axiom observation_primal_minus {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (o : Fin 2 → Comp → Frame B H N E)
    (e : Comp) (i : Fin 2) (v : B → Binary) :
    observation o (e,false) (primalEmbedding i v) = (o i e).Q.mulVec v

axiom key_map_coordinate {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H : Type}
    (W : Lists k n b degree r hr) (e : Lax342547.CutProfiles.Component (Tag k))
    (p : ComponentPosition W e) : by
      classical
      exact keyMap (H := H) W e (Pi.single p 1) =
        primalEmbedding p.val.1 (W.left p.val.1 p.val.2.1 p.val.2.2).vector

axiom key_observations_left {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (o : Unit (H := H) (N := N) (E := E))
    (e : Lax342547.CutProfiles.Component (Tag k)) (mode : Bool) : by
      classical
      exact LinearMap.toMatrix' ((observation o (e,mode)).comp (keyMap (H := H) W e)) =
        if mode then (leftTuple W o e).1 else (leftTuple W o e).2

noncomputable def tupleMaps {k n b degree r : ℕ} {hr : 2 * r ≤ n} {N : Type}
    (W : Lists k n b degree r hr) (q : Lax342547.ReferenceKeys.Tuples
      (Lax342547.CutProfiles.Component (Tag k)) (ComponentPosition W) N)
    (a : Lax342547.CutProfiles.Component (Tag k) × Bool) :
    (ComponentPosition W a.1 → Binary) →ₗ[Binary] (N → Binary) := by
  classical
  exact (if a.2 then (q a.1).1 else (q a.1).2).mulVecLin

axiom left_tuple_event {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr) (q : Lax342547.ReferenceKeys.Tuples
      (Lax342547.CutProfiles.Component (Tag k)) (ComponentPosition W) N)
    (o : Unit (H := H) (N := N) (E := E)) :
    leftTuple W o = q ↔ ∀ a, (observation o a).comp (keyMap (H := H) W a.1) = tupleMaps W q a

axiom key_dimension {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) : by
      classical
      exact (∑ a : Lax342547.CutProfiles.Component (Tag k) × Bool,
        Module.finrank Binary (ComponentPosition W a.1 → Binary)) =
        Fintype.card (Lax342547.QuerySlots.Slot W)

axiom actual_left_key_cap {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
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
    p.toOuterMeasure {o | leftTuple W o = q} ≤ α ^ Fintype.card (Lax342547.QuerySlots.Slot W)

end Lax342547.RawQueryImages
