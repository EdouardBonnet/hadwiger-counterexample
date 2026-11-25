import Lax793645.ConstructionData

/-!
---
title: Obstructions from frozen directions
type: lemma
---
For a protected witness list, agreement on the selected point squares and the
effective profiles implies agreement on all quadratic obstructions from the frozen
primal and channel directions.
-/

namespace Lax793645.FrozenConstraints

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
axiom one_selected_obstructions
    {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I] (v : Volley p n I) (t : Tagging p I) (hv : v.legal t)
    (P : Bool→ Comp p.g→ Space (Ray p n)) (R : ℕ) (hprot : OneProtectedVolley v t P R)
    (C : Bool→ Comp p.g→ Space (Hyperbolic p.h))
    (G : Bool→ Comp p.g→ JointRay p n→ₗ[F]Hyperbolic p.h)
    (hsafe : ∀ e i j,∀ u∈P i e,G j e (jointInjection i u)∈C j e→ u=0)
    (M : Bool→ JointProfile p n)
    (ha : ∀ j a,jointMatrixFunctional (M j) (jointEndpointMap (v.obj a) (v.atomAt t a))=
      jointMatrixFunctional (fun e=> channelQuadraticMatrix p.h (G j e))
        (jointEndpointMap (v.obj a) (v.atomAt t a)))
    (hp : ∀ j z,z∈jointXspace→(∀ e,z e∈quadraticSquares (jointSpace (fun i=> P i e)))→
      jointMatrixFunctional (M j) z=
        jointMatrixFunctional (fun e=> channelQuadraticMatrix p.h (G j e)) z) :
    ∀ j z,z∈jointXspace→ z∈jointQuadraticConstraints (oneSelectedPrimal v t P)
      (fun e=> frozenChannelKernel p.h (oneSelectedPrimal v t P e) (C j e)
        ((G j e).domRestrict (oneSelectedPrimal v t P e)))→
      jointMatrixFunctional (M j) z=
        jointMatrixFunctional (fun e=> channelQuadraticMatrix p.h (G j e)) z

end

end Lax793645.FrozenConstraints
