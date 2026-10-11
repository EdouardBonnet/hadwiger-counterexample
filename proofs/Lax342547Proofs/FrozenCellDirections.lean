import Lax342547.FrozenCellDirections
import Lax342547.JoinedRecords
import Lax342547.PrimalGramTests
import Lax342547.QueryRecordBounds
import Lax342547.RawQueryImages
import Lax342547.RightQueryImages

namespace Lax342547Proofs.FrozenCellDirections
open Lax342547.FrozenCellDirections

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TagGeometry
open Lax342547.PairedWitnesses Lax342547.PairedRecipes Lax342547.QueryReference
open Lax342547.QueryIndependence Lax342547.RawQueryImages Lax342547.RightQueryImages
open Lax342547.ReferencePins Lax342547.JoinedRecords Lax342547.ExactPins
open Lax342547.RawBaselines Lax342547.PrimalGramTests Lax342547.RetainedCharacters
open Lax342547.TableContractions Lax342547.PairedKeys

/--
---
conclusion: Lax342547.FrozenCellDirections.pin_key_frozen_images
---
-/
theorem pin_key_frozen_images {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {M : Moment k n b degree}
    (W : Lists k n b degree r hr)
    (P : Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (o o' : Unit (H := H) (N := N) (E := M))
    (ho : o ∈ P.event observation) (ho' : o' ∈ P.event observation)
    (hkey : leftTuple W o = leftTuple W o') (a : Lax342547.CutProfiles.Component (Tag k) × Bool)
    (v : (Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary)
    (hv : v ∈ joined P (fun a => keyMap (H := H) W a.1) a) : observation o a v = observation o' a v := by
  classical
  obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, map_add]
  have hxv : observation o a x = observation o' a x := (ho a ⟨x,hx⟩).trans (ho' a ⟨x,hx⟩).symm
  rcases hy with ⟨c,rfl⟩
  have hk := (Lax342547.RawQueryImages.left_tuple_event W (leftTuple W o') o).mp hkey a
  have hk' := (Lax342547.RawQueryImages.left_tuple_event W (leftTuple W o') o').mp rfl a
  have hyv : observation o a (keyMap W a.1 c) = observation o' a (keyMap W a.1 c) :=
    LinearMap.congr_fun (hk.trans hk'.symm) c
  rw [hxv, hyv]

/--
---
conclusion: Lax342547.FrozenCellDirections.right_pin_key_frozen_images
---
-/
theorem right_pin_key_frozen_images {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    [Fintype H] [Fintype N] {M : Moment k n b degree}
    (W : Lists k n b degree r hr)
    (P : Pin (Lax342547.CutProfiles.Component (Tag k) × Bool)
      (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (o o' : Unit (H := H) (N := N) (E := M))
    (ho : o ∈ P.event observation) (ho' : o' ∈ P.event observation)
    (hkey : rightTuple W o = rightTuple W o') (a : Lax342547.CutProfiles.Component (Tag k) × Bool)
    (v : (Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary)
    (hv : v ∈ joined P (fun a => keyMap (H := H) (flip W) a.1) a) : observation o a v = observation o' a v := by
  apply Lax342547.FrozenCellDirections.pin_key_frozen_images (flip W) P o o' ho ho' _ a v hv
  rw [Lax342547.RightQueryImages.left_flip_right_tuple,
    Lax342547.RightQueryImages.left_flip_right_tuple, hkey]

/--
---
conclusion: Lax342547.FrozenCellDirections.frozen_target_oriented
---
-/
theorem frozen_target_oriented {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
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
    actualForm (leftMatrices oA a) (rightMatrices oB a) v w = orientedForms G a v w := by
  classical
  rw [Lax342547.PrimalGramTests.raw_oriented_forms]
  simp only [joined, Lax342547.QueryRecordBounds.key_map_range] at hvw
  rcases a with ⟨e,s⟩
  cases s
  · have h := (hf e).2 w v (by simpa only [Bool.not_false] using hvw.symm)
    exact h.symm
  · have h := (hf e).1 v w (by simpa only [Bool.not_true] using hvw)
    exact h.symm

/--
---
conclusion: Lax342547.FrozenCellDirections.record_target_oriented
---
-/
theorem record_target_oriented {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
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
    actualForm (leftMatrices oA a) (rightMatrices oB a) v w = orientedForms G a v w := by
  classical
  let DA := joined P (fun a => keyMap (H := H) W a.1) a
  let EB := joined Q (fun a => keyMap (H := H) (flip W) a.1) (a.1,!a.2)
  have h := Lax342547.JoinedRecords.basis_records_cross_agreement DA EB
    (observation oA a) (observation refA a) (observation oB (a.1,!a.2)) (observation refB (a.1,!a.2))
    (fun j => observation refA a (basisVectors DA j))
    (fun j => observation refB (a.1,!a.2) (basisVectors EB j))
    (fun j => ⟨Lax342547.FrozenCellDirections.pin_key_frozen_images W P oA refA hA hAr hkeyA a (basisVectors DA j)
      (Module.finBasis Binary DA j).property, rfl⟩)
    (fun j => ⟨Lax342547.FrozenCellDirections.right_pin_key_frozen_images W Q oB refB hB hBr hkeyB (a.1,!a.2) (basisVectors EB j)
      (Module.finBasis Binary EB j).property, rfl⟩)
    (congrFun hrecA a) (congrFun hrecB a)
  have he : dotProduct (observation oA a v) (observation oB (a.1,!a.2) w) =
      dotProduct (observation refA a v) (observation refB (a.1,!a.2) w) := by
    rcases hvw with hv | hw
    · exact h.1 v hv w
    · exact h.2 v w hw
  rw [Lax342547.PrimalGramTests.gram_form_evaluation]
  change dotProduct (observation oA a v) (observation oB (a.1,!a.2) w) = _
  rw [he]
  change dotProduct ((leftMatrices refA a).mulVec v) ((rightMatrices refB a).mulVec w) = _
  rw [← Lax342547.PrimalGramTests.gram_form_evaluation]
  exact Lax342547.FrozenCellDirections.frozen_target_oriented W P Q refA refB G hf a v w hvw

end Lax342547Proofs.FrozenCellDirections
