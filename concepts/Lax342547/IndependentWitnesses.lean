import Lax342547.AdaptiveProtection
import Mathlib.LinearAlgebra.DFinsupp

/-!
---
title: Amplified channel failures on independent pinned spaces
type: lemma
---
Nonzero choices from actual independent pinned spaces form independent witnesses; counting all choices and adaptive protected spaces gives the amplified failure exponent.
-/

namespace Lax342547.IndependentWitnesses

open Lax342547.MomentSpace Lax342547.RetainedImages Lax342547.RealCellLaws
open scoped BigOperators

axiom independent_witness_matrix {I N : Type} [Fintype I]
    (V : I → Submodule Binary (N → Binary)) (hV : iSupIndep V)
    (v : ∀ i,V i) (hv : ∀ i,(v i).val ≠ 0) :
    Function.Injective (Matrix.of (fun n i => (v i).val n)).mulVec

axiom nonzero_witness_card {I N : Type} [Fintype I] [Fintype N]
    (V : I → Submodule Binary (N → Binary)) (K : ℕ) (hK : ∀ i,Module.finrank Binary (V i) ≤ K) :
    Nat.card (∀ i,{v : V i // v.val ≠ 0}) ≤ 2^(K*Fintype.card I)

axiom adaptive_independent_witness_probability {I H N : Type}
    [Fintype I] [Fintype H] [Fintype N] [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (V : I → Submodule Binary (N → Binary)) (hV : iSupIndep V)
    (S : Matrix N H Binary → Submodule Binary (H → Binary)) (K : ℕ)
    (hK : ∀ i,Module.finrank Binary (V i) ≤ K) (hS : ∀ Y,Module.finrank Binary (S Y) ≤ K) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N H Binary)))
      (fun Y => ∀ i,∃ v : V i,v.val ≠ 0 ∧ Y.transpose.mulVec v.val ∈ S Y) ≤
      (2 : ℝ)^(Fintype.card H*K+2*K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I)

end Lax342547.IndependentWitnesses
