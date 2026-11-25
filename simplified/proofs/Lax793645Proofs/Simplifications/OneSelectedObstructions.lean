import Lax793645Proofs.Simplifications.OnePinInjection
import Lax793645Proofs.Simplifications.AffineKeyDirections

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def oneSelectedPrimal (v : Volley p n I) (t : Tagging p I)
    (P : Bool→Comp p.g→Space (Ray p n)) (e : Comp p.g) : Space (JointRay p n) :=
  jointSpace (fun i=>P i e⊔selectedAtComponent
    (fun a : CallsAt v i=>t a.val) (fun a=>v.sel a.val) (fun a=>v.par a.val) e)

/-- The protected-subspace conditions needed by the joint quadratic
annihilator, stated directly on the query's actual selected points. -/
structure OneProtectedVolley (v : Volley p n I) (t : Tagging p I)
    (P : Bool→Comp p.g→Space (Ray p n)) (R : ℕ) where
  selector : Bool→Space (Vec (SelIdx p.b p.j))
  base : Bool→Space (Vec (AIdx p.g n))
  pinCross : ∀ i e,P i e≤tensorCross (selector i) (base i)
  selectorIndependent : ∀ i,LinearIndependent F ((selector i).mkQ∘
    fun a : CallsAt v i=>selV p.j (v.sel a.val))
  baseIndependent : ∀ i,LinearIndependent F ((base i).mkQ∘
    fun a : CallsAt v i=>baseV (v.par a.val))
  rankBound : ∀ e,2*dim (oneSelectedPrimal v t P e)≤R
  lowPin : ∀ i e,∀ u∈P i e,Matrix.rank (flattenMatrix.symm u)≤R^2+Fintype.card (CallsAt v i)→
    u∈tensorRectangle (selector i) (base i)

/-- This discharges the entire obstruction condition from selected-atom
values and effective pin-profile values. The endpoint kernel condition is
exactly the one supplied by the new relative injection estimate. -/
theorem one_selected_obstructions (v : Volley p n I) (t : Tagging p I) (hv : v.legal t)
    (P : Bool→Comp p.g→Space (Ray p n)) (R : ℕ) (hprot : OneProtectedVolley v t P R)
    (C : Bool→Comp p.g→Space (Hyperbolic p.h))
    (G : Bool→Comp p.g→JointRay p n→ₗ[F]Hyperbolic p.h)
    (hsafe : ∀ e i j,∀ u∈P i e,G j e (jointInjection i u)∈C j e→u=0)
    (M : Bool→JointProfile p n)
    (ha : ∀ j a,jointMatrixFunctional (M j) (jointEndpointMap (v.obj a) (v.atomAt t a))=
      jointMatrixFunctional (fun e=>channelQuadraticMatrix p.h (G j e))
        (jointEndpointMap (v.obj a) (v.atomAt t a)))
    (hp : ∀ j z,z∈jointXspace→(∀ e,z e∈quadraticSquares (jointSpace (fun i=>P i e)))→
      jointMatrixFunctional (M j) z=
        jointMatrixFunctional (fun e=>channelQuadraticMatrix p.h (G j e)) z) :
    ∀ j z,z∈jointXspace→z∈jointQuadraticConstraints (oneSelectedPrimal v t P)
      (fun e=>frozenChannelKernel p.h (oneSelectedPrimal v t P e) (C j e)
        ((G j e).domRestrict (oneSelectedPrimal v t P e)))→
      jointMatrixFunctional (M j) z=
        jointMatrixFunctional (fun e=>channelQuadraticMatrix p.h (G j e)) z := by
  intro j z hz hquad
  let K:=fun e=>frozenChannelKernel p.h (oneSelectedPrimal v t P e) (C j e)
    ((G j e).domRestrict (oneSelectedPrimal v t P e))
  have hk (e) (i) : Disjoint (K e) ((P i e).map (jointInjection i)):=
    frozen_endpoint_kernel_disjoint _ _ _ _ _ (hsafe e i j)
  have hh:=joint_quadratic_obstruction_test
    (fun i (a : CallsAt v i)=>t a.val) (fun i a=>v.sel a.val) (fun i a=>v.par a.val)
    (fun i a=>hv a.val) hprot.selector hprot.base hprot.selectorIndependent hprot.baseIndependent
    P K hprot.pinCross (fun e=>frozen_channel_kernel_le ..) hk R hprot.rankBound hprot.lowPin
    (jointMatrixFunctional (M j)-jointMatrixFunctional (fun e=>channelQuadraticMatrix p.h (G j e)))
    (fun i a=>?_) (fun y hy hpy=>sub_eq_zero.mpr (hp j y hy hpy)) z hz hquad
  · exact sub_eq_zero.mp hh
  · have hi : v.obj a.val=i:=(Finset.mem_filter.mp a.property).2
    have he:=ha j a.val
    rw [hi] at he
    exact sub_eq_zero.mpr he

variable {N : ℕ}

theorem one_right_channels_reciprocal (x y : OneUnit p n N) (e : Comp p.g) (i : Bool) :
    unitRightChannels p.h (oneUnitActual x y e) i=
      unitLeftChannels p.h (oneUnitActual y x e) i := by
  have he : (oneUnitActual x y e).flip=oneUnitActual y x e := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    exact one_unit_actual_reciprocal x y e b a
  rw [unitRightChannels,he]

end
end Lax793645Proofs.Simplifications
