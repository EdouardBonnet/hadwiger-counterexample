import Lax342547.FrozenCharacters
import Lax342547.RawFrames

/-!
---
title: Unary records determine every frozen cross entry
type: lemma
---
Pairings of nominal columns with already fixed frozen image vectors require only nominal dimension times frozen-vector count bits. Separate unary records determine all cross entries with a frozen factor.
-/

namespace Lax342547.FrozenRecords

open Lax342547.MomentSpace Lax342547.ConcreteGeometry

noncomputable def record {I X N : Type} [Fintype N]
    (A : (I → Binary) →ₗ[Binary] (N → Binary)) (frozen : X → N → Binary) : Matrix I X Binary := by
  classical
  exact fun i x => dotProduct (A (Pi.single i 1)) (frozen x)

axiom record_count {I X : Type} [Fintype I] [Fintype X] : by
    classical
    exact Fintype.card (Matrix I X Binary) = 2 ^ (Fintype.card I * Fintype.card X)

axiom record_evaluation {I X N : Type} [Fintype I] [Fintype N]
    (A : (I → Binary) →ₗ[Binary] (N → Binary)) (frozen : X → N → Binary)
    (v : I → Binary) (x : X) :
    dotProduct (A v) (frozen x) = ∑ i, v i * record A frozen i x

axiom records_determine_frozen {I X N : Type} [Fintype I] [Fintype N]
    (A A' : (I → Binary) →ₗ[Binary] (N → Binary)) (frozen : X → N → Binary)
    (hrec : record A frozen = record A' frozen) (v : I → Binary)
    (w : Submodule.span Binary (Set.range frozen)) :
    dotProduct (A v) w.val = dotProduct (A' v) w.val

axiom two_records_cross_agreement {I J X Y N : Type}
    [Fintype I] [Fintype J] [Fintype N]
    (A A' : (I → Binary) →ₗ[Binary] (N → Binary))
    (B B' : (J → Binary) →ₗ[Binary] (N → Binary))
    (left : X → I → Binary) (right : Y → J → Binary)
    (leftImages : X → N → Binary) (rightImages : Y → N → Binary)
    (hleft : ∀ x, A (left x) = leftImages x ∧ A' (left x) = leftImages x)
    (hright : ∀ y, B (right y) = rightImages y ∧ B' (right y) = rightImages y)
    (hrecA : record A rightImages = record A' rightImages)
    (hrecB : record B leftImages = record B' leftImages) :
    (∀ v ∈ Submodule.span Binary (Set.range left), ∀ w,
      dotProduct (A v) (B w) = dotProduct (A' v) (B' w)) ∧
    (∀ v w, w ∈ Submodule.span Binary (Set.range right) →
      dotProduct (A v) (B w) = dotProduct (A' v) (B' w))

end Lax342547.FrozenRecords
