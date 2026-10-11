import Lax342547.TensorAnnihilators
import Lax342547.TableSpaces

/-!
---
title: Endpoint projections of paired pure-response annihilators
type: lemma
---
A shared bilinear response on the two nominal quotient spaces still
tests each endpoint separately: project onto its primal block before
choosing the bilinear form. This is the first step of the §6 obstruction
argument, with channel and mixed pin coordinates retained.
-/

namespace Lax342547.PairedAnnihilators

open Lax342547.MomentSpace Lax342547.ConcreteGeometry
open Lax342547.ProjectedPins Lax342547.TableSpaces Lax342547.TensorAnnihilators

abbrev Nominal (B H : Type) := (Fin 2 × (B ⊕ H)) → Binary

noncomputable def pureResponse {B H : Type} [Fintype B]
    (D E : Submodule Binary (Nominal B H))
    (β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary) :
    (Fin 2 → Matrix B B Binary) →ₗ[Binary] Binary := by
  classical
  exact ∑ i, (matrixPair (LinearMap.BilinForm.toMatrix'
    (β.compl₁₂ (D.mkQ.comp (primalEmbedding i))
      (E.mkQ.comp (primalEmbedding i))))).comp (LinearMap.proj i)

def PairedAnnihilates {B H : Type} [Fintype B]
    (M : Fin 2 → Matrix B B Binary) (D E : Submodule Binary (Nominal B H)) : Prop :=
  ∀ β, pureResponse D E β M = 0

axiom endpoint_projection {B H : Type} [Fintype B]
    (M : Fin 2 → Matrix B B Binary) (D E : Submodule Binary (Nominal B H))
    (h : PairedAnnihilates M D E) (i : Fin 2)
    (S T : Submodule Binary (B → Binary))
    (hD : D.map (primalProjection i) ≤ S) (hE : E.map (primalProjection i) ≤ T) :
    PureAnnihilates (M i) S T

axiom endpoint_rank {B H : Type} [Fintype B] [DecidableEq B]
    (M : Fin 2 → Matrix B B Binary) (D E : Submodule Binary (Nominal B H))
    (h : PairedAnnihilates M D E) (i : Fin 2)
    (S T : Submodule Binary (B → Binary))
    (hD : D.map (primalProjection i) ≤ S) (hE : E.map (primalProjection i) ≤ T) :
    (M i).rank ≤ Module.finrank Binary S + Module.finrank Binary T

end Lax342547.PairedAnnihilators
