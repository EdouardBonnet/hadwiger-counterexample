import Lax342547.ProtectedChannels
import Lax342547.SmallSubspaceCount
import Lax342547.ChannelColumns
import Lax342547.InjectiveFrames

/-!
---
title: Channel bounds with adaptive protected coefficient spaces
type: lemma
---
Uniform counting of every bounded-dimensional protected space controls the actual channel event even when that space depends on the random matrix.
-/

namespace Lax342547.AdaptiveProtection

open Lax342547.MomentSpace Lax342547.RetainedImages Lax342547.RealCellLaws
open scoped BigOperators

axiom adaptive_protected_probability {I H N : Type}
    [Fintype I] [Fintype H] [Fintype N] [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (D : Matrix N I Binary) (hD : Function.Injective D.mulVec)
    (S : Matrix N H Binary → Submodule Binary (H → Binary)) (K : ℕ)
    (hS : ∀ Y,Module.finrank Binary (S Y) ≤ K) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N H Binary)))
      (fun Y => ∀ i,(fun h => (Y.transpose*D) h i) ∈ S Y) ≤
      (2 : ℝ)^(Fintype.card H*K+K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I)

end Lax342547.AdaptiveProtection
