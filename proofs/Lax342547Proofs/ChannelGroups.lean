import Lax342547.ChannelGroups
import Lax342547Proofs.Walsh

namespace Lax342547Proofs.ChannelGroups
open Lax342547.ChannelGroups

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Walsh Lax342547.TensorCharacters
open Lax342547.ChannelCharacters Lax342547.ChannelColumns
open scoped BigOperators

/--
---
conclusion: Lax342547.ChannelGroups.sign_sum
---
-/
theorem sign_sum {ι : Type} [Fintype ι] (z : ι → Binary) : sign (∑ i, z i) = ∏ i,sign (z i) := by
  classical
  have hs (S : Finset ι) : sign (∑ i ∈ S,z i) = ∏ i ∈ S,sign (z i) := by
    induction S using Finset.induction_on with
    | empty => simp [Lax342547Proofs.Walsh.sign_zero]
    | @insert i S hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,Lax342547Proofs.Walsh.sign_add,ih]
  exact hs Finset.univ

/--
---
conclusion: Lax342547.ChannelGroups.tensor_character_groups
---
-/
theorem tensor_character_groups {e d I J : Type} [Fintype e] [Fintype d] [Fintype I] [Fintype J]
    (A : e → Matrix I J Binary) (h : ℕ)
    (c : (e × d) × Fin h → (I → Binary) × (J → Binary)) :
    tensorCharacter h (fun i : e × d => A i.1) c =
      ∏ j : d,tensorCharacter h A (fun i => c ((i.1,j),i.2)) := by
  unfold tensorCharacter
  simp only [Fintype.prod_prod_type]
  exact Finset.prod_comm

/--
---
conclusion: Lax342547.ChannelGroups.tensor_character_value
---
-/
theorem tensor_character_value {e N : Type} [Fintype e] [Fintype N] (h : ℕ)
    (A : e → Matrix N N Binary)
    (z : e → Matrix N (Fin h) Binary × Matrix N (Fin h) Binary) :
    tensorCharacter h A (columnsEquiv h z) = sign (∑ i,channelValue h (A i) (z i).1 (z i).2) := by
  unfold tensorCharacter channelValue
  simp only [Fintype.prod_prod_type,Lax342547.ChannelGroups.sign_sum,character,phase,columnsEquiv,Equiv.coe_fn_mk]

end Lax342547Proofs.ChannelGroups
