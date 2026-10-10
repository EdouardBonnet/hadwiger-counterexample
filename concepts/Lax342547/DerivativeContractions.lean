import Lax342547.TensorContractions
import Lax342547.PrimalContractions

/-!
---
title: Rank-one derivative tests are scalar pairings of residual contractions
type: theorem
---
A rank-one change in either channel map contracts to the baseline
evaluation of the corresponding matrix contraction. Transposition
exchanges the two orientations without a symmetry assumption.
-/

namespace Lax342547.DerivativeContractions

open Lax342547.MomentSpace Lax342547.PrimalContractions Lax342547.ConcreteGeometry
open Lax342547.TensorContractions

axiom right_rank_one {B H : Type} [Fintype B] [Fintype H]
    (M : Matrix B B Binary) (f : (B → Binary) →ₗ[Binary] (H → Binary))
    (ψ : Module.Dual Binary (B → Binary)) (c : H → Binary) :
    ambient f (ψ.smulRight c) M = dotProduct (f (M.mulVecLin (coordinates ψ))) c

axiom transpose_contraction {B H : Type} [Fintype B] [Fintype H]
    (M : Matrix B B Binary) (f g : (B → Binary) →ₗ[Binary] (H → Binary)) :
    ambient f g M = ambient g f M.transpose

axiom left_rank_one {B H : Type} [Fintype B] [Fintype H]
    (M : Matrix B B Binary) (g : (B → Binary) →ₗ[Binary] (H → Binary))
    (φ : Module.Dual Binary (B → Binary)) (c : H → Binary) :
    ambient (φ.smulRight c) g M = dotProduct c (g (M.transpose.mulVecLin (coordinates φ)))

open Lax342547.PairedAnnihilators

axiom paired_transpose {B H : Type} [Fintype B]
    (M : Fin 2 → Matrix B B Binary) (D E : Submodule Binary (Nominal B H))
    (h : PairedAnnihilates M D E) : PairedAnnihilates (fun i => (M i).transpose) E D

end Lax342547.DerivativeContractions
