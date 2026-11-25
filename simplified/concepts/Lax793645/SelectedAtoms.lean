import Lax793645.ConstructionData

/-!
---
title: Isolating selected point matrices
type: lemma
---
Choose point directions whose selector and base factors are each independent modulo
the corresponding protected space. Under the support condition of the lemma, a moment
matrix splits into the selected point squares and a matrix supported on the protected
rows and columns.
-/

namespace Lax793645.SelectedAtoms

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule Module LinearMap
open scoped BigOperators Kronecker
variable {S T I S' T' : Type} [Fintype S] [Fintype T] [Fintype I]
  [Fintype S'] [Fintype T']

axiom tensor_atom_isolation (U : Space (Vec S)) (V : Space (Vec T))
    (s : I → Vec S) (t : I → Vec T)
    (hs : LinearIndependent F (U.mkQ ∘ s)) (ht : LinearIndependent F (V.mkQ ∘ t))
    (εS : Vec S) (εT : Vec T) (hs1 : ∀ i, dotProduct εS (s i)=1)
    (ht1 : ∀ i, dotProduct εT (t i)=1)
    (w : Mat (S × T) (S × T)) (hw : w ∈ affineTensorSpace εS εT)
    (hvan : vanish (tensorRectangle U V ⊔ selectedTensorSpace s t)
      (tensorRectangle U V ⊔ selectedTensorSpace s t) w) :
    ∃ (c : I → F) (w₀ : Mat (S × T) (S × T)),
      w=(∑ i, c i • vecMulVec (tensorRay (s i) (t i)) (tensorRay (s i) (t i)))+w₀ ∧
      w₀ ∈ box (tensorCross U V) (tensorCross U V)

end

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule Module LinearMap
open scoped BigOperators Kronecker
axiom selected_tensor_independent_mod_cross
    {S T I : Type} [Fintype S] [Fintype T] [Fintype I]
    (U : Space (Vec S)) (V : Space (Vec T)) (s : I → Vec S) (t : I → Vec T)
    (hs : LinearIndependent F (U.mkQ ∘ s)) (ht : LinearIndependent F (V.mkQ ∘ t)) :
    LinearIndependent F ((tensorCross U V).mkQ ∘ (fun i => tensorRay (s i) (t i)))

end

end Lax793645.SelectedAtoms
