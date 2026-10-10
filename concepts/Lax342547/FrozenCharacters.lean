import Lax342547.TensorAnnihilators
import Lax342547.ResidualRealization
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
---
title: Exact agreement of zero quotient characters
type: definition and theorem
---
A bilinear difference killing both frozen factors descends to the two quotients. Coefficient tensors annihilating every quotient form therefore have identical actual and target pairings.
-/

namespace Lax342547.FrozenCharacters

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TensorAnnihilators

axiom quotient_bilinear {V W : Type} [AddCommGroup V] [Module Binary V]
    [AddCommGroup W] [Module Binary W]
    (D : Submodule Binary V) (E : Submodule Binary W)
    (F : V →ₗ[Binary] W →ₗ[Binary] Binary)
    (hD : ∀ v ∈ D, ∀ w, F v w = 0) (hE : ∀ v w, w ∈ E → F v w = 0) :
    ∃ Q : (V ⧸ D) →ₗ[Binary] (W ⧸ E) →ₗ[Binary] Binary,
      Q.compl₁₂ D.mkQ E.mkQ = F

axiom zero_quotient_frozen_agreement {I : Type} [Fintype I]
    (C : Matrix I I Binary) (D E : Submodule Binary (I → Binary))
    (F G : (I → Binary) →ₗ[Binary] (I → Binary) →ₗ[Binary] Binary)
    (hC : PureAnnihilates C D E)
    (hD : ∀ v ∈ D, ∀ w, F v w = G v w)
    (hE : ∀ v w, w ∈ E → F v w = G v w) :
    by
      classical
      exact matrixPair (LinearMap.BilinForm.toMatrix' F) C =
        matrixPair (LinearMap.BilinForm.toMatrix' G) C

end Lax342547.FrozenCharacters
