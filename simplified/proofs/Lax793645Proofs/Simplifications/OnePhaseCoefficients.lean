import Lax793645Proofs.Simplifications.OneDualImages
import Lax793645Proofs.Simplifications.OnePhaseLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ} {J : Type} [Fintype J] [DecidableEq J]

def onePrimalCoefficient (i : Bool) (Z : Mat (Row p n) J) : Mat (OneColumn p n) J:=
  LinearMap.toMatrix' ((oneEndpointInjection i).comp (quadraticPrimalIn.comp Z.mulVecLin))

def oneChannelCoefficient (C : Bool→Mat (HyperbolicIdx p.h) J) : Mat (OneColumn p n) J:=
  LinearMap.toMatrix' (∑ i,(oneEndpointInjection i).comp
    ((LinearMap.inr F _ _).comp ((hyperbolicCoordinates p.h).toLinearMap.comp (C i).mulVecLin)))

theorem one_primal_coefficient_apply (i : Bool) (Z : Mat (Row p n) J) (v : Vec J) :
    onePrimalCoefficient i Z*ᵥv=oneEndpointInjection i (Z*ᵥv,0) := by
  rw [onePrimalCoefficient,LinearMap.toMatrix'_mulVec]
  rfl

theorem one_channel_coefficient_apply (C : Bool→Mat (HyperbolicIdx p.h) J) (v : Vec J) :
    oneChannelCoefficient (n:=n) C*ᵥv=∑ i,oneEndpointInjection i (0,hyperbolicCoordinates p.h (C i*ᵥv)) := by
  rw [oneChannelCoefficient,LinearMap.toMatrix'_mulVec,LinearMap.sum_apply]
  rfl

theorem one_primal_coefficient_projection (i j : Bool) (Z : Mat (Row p n) J) (v : Vec J) :
    oneEndpointProjection j (onePrimalCoefficient i Z*ᵥv)=if i=j then (Z*ᵥv,0) else 0 := by
  rw [one_primal_coefficient_apply,one_endpoint_injection_projection]

theorem one_channel_coefficient_projection (j : Bool) (C : Bool→Mat (HyperbolicIdx p.h) J)
    (v : Vec J) :
    oneEndpointProjection j (oneChannelCoefficient (n:=n) C*ᵥv)=(0,hyperbolicCoordinates p.h (C j*ᵥv)) := by
  rw [one_channel_coefficient_apply,map_sum]
  simp only [one_endpoint_injection_projection]
  cases j <;> simp

theorem one_primal_coefficient_inj (i : Bool) (Z : Mat (Row p n) J)
    (hZ : Function.Injective Z.mulVec) : Function.Injective (onePrimalCoefficient i Z).mulVec := by
  intro u v h
  apply hZ
  have he:=congrArg (fun x=>Prod.fst (oneEndpointProjection i x)) h
  simpa [one_primal_coefficient_projection] using he

theorem one_channel_coefficient_inj (C : Bool→Mat (HyperbolicIdx p.h) J)
    (j : Bool) (hC : Function.Injective (C j).mulVec) :
    Function.Injective (oneChannelCoefficient (n:=n) C).mulVec := by
  intro u v h
  apply hC
  apply (hyperbolicCoordinates p.h).injective
  have he:=congrArg (fun x=>Prod.snd (oneEndpointProjection j x)) h
  simpa only [one_channel_coefficient_projection] using he

theorem one_coefficient_disjoint {K : Type} [Fintype K] [DecidableEq K]
    (i : Bool) (Z : Mat (Row p n) J) (C : Bool→Mat (HyperbolicIdx p.h) K) :
    Disjoint (colSp (onePrimalCoefficient i Z)) (colSp (oneChannelCoefficient (n:=n) C)) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨u,rfl⟩ ⟨v,hv⟩
  change oneChannelCoefficient (n:=n) C*ᵥv=onePrimalCoefficient i Z*ᵥu at hv
  have he:=congrArg (fun x=>Prod.fst (oneEndpointProjection i x)) hv
  simp only [one_channel_coefficient_projection,one_primal_coefficient_projection,ite_true] at he
  change onePrimalCoefficient i Z*ᵥu=0
  rw [one_primal_coefficient_apply,←he]
  exact map_zero _

theorem one_dual_channel_value (P : OneFrame p n N) (v : Vec (HyperbolicIdx p.h)) :
    oneDualCoordinates N (P (0,hyperbolicCoordinates p.h v))=
      Matrix.fromCols (oneChannelPairEquiv p N (oneChannels P)).2
        (oneChannelPairEquiv p N (oneChannels P)).1*ᵥv := by
  have he : Matrix.fromCols (oneChannelPairEquiv p N (oneChannels P)).2
      (oneChannelPairEquiv p N (oneChannels P)).1=
      LinearMap.toMatrix' ((oneDualCoordinates N).toLinearMap.comp (oneChannels P)) := by
    ext a j
    cases j <;> rfl
  rw [he,LinearMap.toMatrix'_mulVec]
  rfl

theorem one_fused_dual_images (x : OneUnit p n N) (e : Comp p.g)
    (C : Bool→Mat (HyperbolicIdx p.h) J) :
    oneDualImages x e*oneChannelCoefficient (n:=n) C=
      ∑ i,Matrix.fromCols (onePhaseCube (x i) e).2 (onePhaseCube (x i) e).1*C i := by
  apply coe_mv_inj
  apply LinearMap.ext
  intro v
  change (oneDualImages x e*oneChannelCoefficient (n:=n) C)*ᵥv=_
  rw [←mulVec_mulVec,one_channel_coefficient_apply,mulVec_sum]
  simp only [one_dual_endpoint_images,one_dual_channel_value,Matrix.mulVecLin_apply,
    Matrix.sum_mulVec,←mulVec_mulVec]
  rfl

end
end Lax793645Proofs.Simplifications
