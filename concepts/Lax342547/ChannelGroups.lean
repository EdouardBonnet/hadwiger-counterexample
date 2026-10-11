import Lax342547.TensorCharacters
import Lax342547.ChannelColumns
import Lax342547.Walsh

/-!
---
title: Actual endpoint character products
type: definition and theorem
---
Reindexing the actual channels identifies endpoint group products and their binary channel value.
-/

namespace Lax342547.ChannelGroups

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.TensorCharacters
open Lax342547.ChannelCharacters Lax342547.ChannelColumns
open scoped BigOperators

axiom sign_sum {ι : Type} [Fintype ι] (z : ι → Binary) : sign (∑ i, z i) = ∏ i,sign (z i)

axiom tensor_character_groups {e d I J : Type} [Fintype e] [Fintype d] [Fintype I] [Fintype J]
    (A : e → Matrix I J Binary) (h : ℕ)
    (c : (e × d) × Fin h → (I → Binary) × (J → Binary)) :
    tensorCharacter h (fun i : e × d => A i.1) c =
      ∏ j : d,tensorCharacter h A (fun i => c ((i.1,j),i.2))

noncomputable def channelValue {I J : Type} [Fintype I] [Fintype J] (h : ℕ)
    (A : Matrix I J Binary) (X : Matrix I (Fin h) Binary) (Y : Matrix J (Fin h) Binary) : Binary :=
  ∑ k,dotProduct (fun i => X i k) (A.mulVec (fun j => Y j k))

axiom tensor_character_value {e N : Type} [Fintype e] [Fintype N] (h : ℕ)
    (A : e → Matrix N N Binary)
    (z : e → Matrix N (Fin h) Binary × Matrix N (Fin h) Binary) :
    tensorCharacter h A (columnsEquiv h z) = sign (∑ i,channelValue h (A i) (z i).1 (z i).2)

end Lax342547.ChannelGroups
