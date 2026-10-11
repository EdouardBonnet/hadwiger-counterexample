import Lax342547.QueryRecordBounds
import Lax342547.RightQueryImages
import Lax342547.PrimalGramTests
import Lax342547.RawBaselines

/-!
---
title: Original record cells determine the common frozen gradient target
type: lemma
---
Exact pin events and equal query keys fix every joined frozen direction image. The two separate actual unary records transfer frozen target agreement from chosen representatives to every pair in their original cells, for both cross orientations.
-/

namespace Lax342547.FrozenCellDirections

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TagGeometry
open Lax342547.PairedWitnesses Lax342547.PairedRecipes Lax342547.QueryReference
open Lax342547.QueryIndependence Lax342547.RawQueryImages Lax342547.RightQueryImages
open Lax342547.ReferencePins Lax342547.JoinedRecords Lax342547.ExactPins
open Lax342547.RawBaselines Lax342547.PrimalGramTests Lax342547.RetainedCharacters
open Lax342547.TableContractions Lax342547.PairedKeys

axiom pin_key_frozen_images {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {M : Moment k n b degree}
    (W : Lists k n b degree r hr)
    (P : Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (o o' : Unit (H := H) (N := N) (E := M))
    (ho : o ∈ P.event observation) (ho' : o' ∈ P.event observation)
    (hkey : leftTuple W o = leftTuple W o') (a : Lax342547.CutProfiles.Component (Tag k) × Bool)
    (v : (Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary)
    (hv : v ∈ joined P (fun a => keyMap (H := H) W a.1) a) : observation o a v = observation o' a v

axiom right_pin_key_frozen_images {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {M : Moment k n b degree}
    (W : Lists k n b degree r hr)
    (P : Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (o o' : Unit (H := H) (N := N) (E := M))
    (ho : o ∈ P.event observation) (ho' : o' ∈ P.event observation)
    (hkey : rightTuple W o = rightTuple W o') (a : Lax342547.CutProfiles.Component (Tag k) × Bool)
    (v : (Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary)
    (hv : v ∈ joined P (fun a => keyMap (H := H) (flip W) a.1) a) : observation o a v = observation o' a v

axiom frozen_target_oriented {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {M : Moment k n b degree}
    (W : Lists k n b degree r hr)
    (P Q : Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (oA oB : Unit (H := H) (N := N) (E := M))
    (G : CrossForms (Lax342547.CutProfiles.Component (Tag k)) (Coordinate k n b degree) H)
    (hf : Frozen G W P Q oA oB) (a : Lax342547.CutProfiles.Component (Tag k) × Bool)
    (v w : (Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary)
    (hvw : v ∈ joined P (fun a => keyMap (H := H) W a.1) a ∨
      w ∈ joined Q (fun a => keyMap (H := H) (flip W) a.1) (a.1,!a.2)) :
    actualForm (leftMatrices oA a) (rightMatrices oB a) v w = orientedForms G a v w

noncomputable def leftRecord {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {M : Moment k n b degree}
    (W : Lists k n b degree r hr)
    (Q : Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (frozen o : Unit (H := H) (N := N) (E := M)) :
    ∀ a : Lax342547.CutProfiles.Component (Tag k) × Bool,
      Matrix (Fin 2 × (Coordinate k n b degree ⊕ H))
        (Fin (Module.finrank Binary (joined Q (fun a => keyMap (H := H) (flip W) a.1) (a.1,!a.2)))) Binary :=
  fun a => Lax342547.FrozenRecords.record (observation o a)
    (fun j => observation frozen (a.1,!a.2)
      (basisVectors (joined Q (fun a => keyMap (H := H) (flip W) a.1) (a.1,!a.2)) j))

noncomputable def rightRecord {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {M : Moment k n b degree}
    (W : Lists k n b degree r hr)
    (P : Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (frozen o : Unit (H := H) (N := N) (E := M)) :
    ∀ a : Lax342547.CutProfiles.Component (Tag k) × Bool,
      Matrix (Fin 2 × (Coordinate k n b degree ⊕ H))
        (Fin (Module.finrank Binary (joined P (fun a => keyMap (H := H) W a.1) a))) Binary :=
  fun a => Lax342547.FrozenRecords.record (observation o (a.1,!a.2))
    (fun j => observation frozen a (basisVectors (joined P (fun a => keyMap (H := H) W a.1) a) j))

axiom record_target_oriented {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {M : Moment k n b degree}
    (W : Lists k n b degree r hr)
    (P Q : Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (oA oB refA refB : Unit (H := H) (N := N) (E := M))
    (hA : oA ∈ P.event observation) (hAr : refA ∈ P.event observation)
    (hB : oB ∈ Q.event observation) (hBr : refB ∈ Q.event observation)
    (hkeyA : leftTuple W oA = leftTuple W refA) (hkeyB : rightTuple W oB = rightTuple W refB)
    (hrecA : leftRecord W Q refB oA = leftRecord W Q refB refA)
    (hrecB : rightRecord W P refA oB = rightRecord W P refA refB)
    (G : CrossForms (Lax342547.CutProfiles.Component (Tag k)) (Coordinate k n b degree) H)
    (hf : Frozen G W P Q refA refB) (a : Lax342547.CutProfiles.Component (Tag k) × Bool)
    (v w : (Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary)
    (hvw : v ∈ joined P (fun a => keyMap (H := H) W a.1) a ∨
      w ∈ joined Q (fun a => keyMap (H := H) (flip W) a.1) (a.1,!a.2)) :
    actualForm (leftMatrices oA a) (rightMatrices oB a) v w = orientedForms G a v w

end Lax342547.FrozenCellDirections
