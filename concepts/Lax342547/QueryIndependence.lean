import Lax342547.QueryReference
import Lax342547.PairedKeys
import Lax342547.KeySpans
import Lax342547.TableSpaces

/-!
---
title: Actual query keys independent modulo old pins
type: lemma
---
The incident selected rays in the actual four witness lists are independent modulo the combined nominal pins. The proof uses the existing indexed fresh-label exclusion, with fourteen distinct rays per endpoint.
-/

namespace Lax342547.QueryIndependence

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.CutProfiles
open Lax342547.PairedWitnesses Lax342547.QueryReference Lax342547.QuerySlots
open Lax342547.PairedKeys Lax342547.KeySpans Lax342547.TableSpaces Lax342547.ExactPins
open Lax342547.ConcreteGeometry

noncomputable def keyMap {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H : Type}
    (W : Lists k n b degree r hr) (e : Component (Tag k)) :
    (ComponentPosition W e → Binary) →ₗ[Binary] ((Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary) := by
  classical
  exact
    { toFun := fun c => ∑ p, c p • ray (H := H) (degree := degree) (labels W) (bases W) p.val
      map_add' := by intro c d; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro s c; simp [Finset.smul_sum, smul_smul] }

axiom actual_key_independence {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i) (a : Component (Tag k) × Bool) :
    Function.Injective ((P.space a).mkQ.comp (keyMap (H := H) W a.1))

end Lax342547.QueryIndependence
