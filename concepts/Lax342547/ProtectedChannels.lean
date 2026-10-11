import Lax342547.InjectiveFrames
import Lax342547.ChannelColumns
import Lax342547.FiniteLinearLaw

/-!
---
title: Exact probabilities for independent protected channel images
type: lemma
---
An actual independent witness tuple has uniform transpose images, giving the exact probability that every image lies in a prescribed protected coefficient space.
-/

namespace Lax342547.ProtectedChannels

open Lax342547.MomentSpace Lax342547.RetainedImages Lax342547.RealCellLaws
open scoped BigOperators ENNReal

noncomputable def columnSpaceEquiv {I H : Type} [Fintype I] [Fintype H]
    (S : Submodule Binary (H → Binary)) :
    {Z : Matrix H I Binary // ∀ i,(fun h => Z h i) ∈ S} ≃ (I → S) where
  toFun Z := fun i => ⟨fun h => Z.val h i,Z.property i⟩
  invFun v := ⟨fun h i => (v i).val h,fun i => (v i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

axiom protected_columns_card {I H : Type} [Fintype I] [Fintype H]
    (S : Submodule Binary (H → Binary)) :
    Nat.card {Z : Matrix H I Binary // ∀ i,(fun h => Z h i) ∈ S} =
      2^(Module.finrank Binary S*Fintype.card I)

axiom independent_protected_probability {I H N : Type}
    [Fintype I] [Fintype H] [Fintype N] [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (D : Matrix N I Binary) (hD : Function.Injective D.mulVec)
    (S : Submodule Binary (H → Binary)) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N H Binary)))
      (fun Y => ∀ i,(fun h => (Y.transpose*D) h i) ∈ S) =
      (2 : ℝ)^(Module.finrank Binary S*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I)

axiom protected_probability_rank_bound {I H N : Type}
    [Fintype I] [Fintype H] [Fintype N] [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (D : Matrix N I Binary) (hD : Function.Injective D.mulVec)
    (S : Submodule Binary (H → Binary)) (K : ℕ) (hS : Module.finrank Binary S ≤ K) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N H Binary)))
      (fun Y => ∀ i,(fun h => (Y.transpose*D) h i) ∈ S) ≤
      (2 : ℝ)^(K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I)

end Lax342547.ProtectedChannels
