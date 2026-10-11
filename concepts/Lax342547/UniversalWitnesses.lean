import Lax342547.IndependentWitnesses
import Lax342547.PhaseAverages

/-!
---
title: Universal protected pin witnesses
type: definition and theorem
---
Independent pin witnesses have an amplified probability bound even when the small protected space depends on the whole unit.
-/

namespace Lax342547.UniversalWitnesses

open Lax342547.MomentSpace Lax342547.RetainedImages Lax342547.RealCellLaws Lax342547.PushforwardWalsh
open scoped BigOperators

axiom some_protected_witness_probability {I H N : Type}
    [Fintype I] [Fintype H] [Fintype N] [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (V : I → Submodule Binary (N → Binary)) (hV : iSupIndep V)
    (K : ℕ) (hK : ∀ i,Module.finrank Binary (V i) ≤ K) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N H Binary)))
      (fun Y => ∃ S : Submodule Binary (H → Binary),Module.finrank Binary S ≤ K ∧
        ∀ i,∃ v : V i,v.val ≠ 0 ∧ Y.transpose.mulVec v.val ∈ S) ≤
      (2 : ℝ)^(Fintype.card H*K+2*K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I)

axiom marked_unit_witness_probability {I H N B : Type}
    [Fintype I] [Fintype H] [Fintype N] [Fintype B] [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (V : I → Submodule Binary (N → Binary)) (hV : iSupIndep V)
    (β : B → ℝ) (Y : B → Matrix N H Binary) (S : B → Submodule Binary (H → Binary))
    (K : ℕ) (L : ℝ) (hβ : ∀ b,0 ≤ β b) (hL : 0 ≤ L) (hK : ∀ i,Module.finrank Binary (V i) ≤ K)
    (hS : ∀ b,Module.finrank Binary (S b) ≤ K)
    (hcap : ∀ y,push β Y y ≤ L*weights (PMF.uniformOfFintype (Matrix N H Binary)) y) :
    cellMass β (fun b => ∀ i,∃ v : V i,v.val ≠ 0 ∧ (Y b).transpose.mulVec v.val ∈ S b) ≤
      L*((2 : ℝ)^(Fintype.card H*K+2*K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I))

end Lax342547.UniversalWitnesses
