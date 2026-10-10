import Lax342547.RawQueryImages
import Lax342547.JointKeyCap

/-!
---
title: Actual joint key and fresh image caps
type: definition and theorem
---
The actual selected query tuples and arbitrary fresh directions have one leaf cap, with all component and sign ranks summed. Their dependence within a sampled unit is retained.
-/

namespace Lax342547.RawJointImages

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.PairedWitnesses Lax342547.QueryReference Lax342547.QueryIndependence
open Lax342547.RawQueryImages Lax342547.ReferencePins Lax342547.KeySpans
open scoped ENNReal

axiom actual_left_key_fresh_cap {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {E : Moment k n b degree}
    {V : (Lax342547.CutProfiles.Component (Tag k) × Bool) → Type}
    [∀ a, AddCommGroup (V a)] [∀ a, Module Binary (V a)]
    [∀ a, FiniteDimensional Binary (V a)]
    (W : Lists k n b degree r hr)
    (p : PMF (Unit (H := H) (N := N) (E := E)))
    (P : Lax342547.ExactPins.Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (q : Lax342547.ReferenceKeys.Tuples (Lax342547.CutProfiles.Component (Tag k)) (ComponentPosition W) N)
    (fresh : ∀ a, V a →ₗ[Binary] (Fin 2 × (Coordinate k n b degree ⊕ H) → Binary))
    (hf : ∀ a, Function.Injective
      (((P.space a) ⊔ LinearMap.range (keyMap (H := H) W a.1)).mkQ.comp (fresh a)))
    (yf : ∀ a, V a →ₗ[Binary] (N → Binary)) (α : ℝ≥0∞)
    (hcap : ∀ Q : Lax342547.ExactPins.Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N,
      1 ≤ P.relativeRank Q → p.toOuterMeasure (Q.event observation) ≤ α ^ (P.relativeRank Q))
    (hrank : 1 ≤ Fintype.card (Lax342547.QuerySlots.Slot W) + ∑ a, Module.finrank Binary (V a)) :
    p.toOuterMeasure {o | leftTuple W o = q ∧ ∀ a, (observation o a).comp (fresh a) = yf a} ≤
      α ^ (Fintype.card (Lax342547.QuerySlots.Slot W) + ∑ a, Module.finrank Binary (V a))

end Lax342547.RawJointImages
