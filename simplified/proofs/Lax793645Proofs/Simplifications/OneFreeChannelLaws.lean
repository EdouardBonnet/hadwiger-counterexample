import Lax793645Proofs.Simplifications.QuadraticFreeChannelLaws
import Lax793645Proofs.Simplifications.OnePhaseActionLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

def oneFreeChannelEquiv (p : Shape) (N : ℕ) :
    (Vec (Fin p.h)→ₗ[F]Vec (HyperbolicIdx N))≃ₗ[F]HMat p (2*N) :=
  (LinearEquiv.arrowCongr (LinearEquiv.refl F (Vec (Fin p.h)))
    (oneDualCoordinates N)).trans LinearMap.toMatrix'

theorem one_free_channel_value (P : OneFrame p n N) :
    oneFreeChannelEquiv p N (P.comp quadraticYIn)=
      (oneChannelPairEquiv p N (oneChannels P)).1 := by
  ext i j
  change oneDualCoordinates N (P (quadraticYIn (Pi.single j 1))) i=_
  have hh:=one_channel_pair_y (oneChannels P) j
  rw [one_channel_coordinate_y] at hh
  exact congrFun hh.symm i

theorem one_free_channel_cap (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤2*N) (Y : HMat p (2*N)) :
    mapW (quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
      (selfM p n m.mixM).toQuadraticForm')
      (fun P=>(oneChannelPairEquiv p N (oneChannels P)).1) Y≤2*unif Y := by
  classical
  letI : Fintype ((Ray p n×Vec (Fin p.h))→ₗ[F]Vec (HyperbolicIdx N)):=
    Fintype.ofInjective DFunLike.coe DFunLike.coe_injective
  letI : Fintype (Vec (Fin p.h)→ₗ[F]Vec (HyperbolicIdx N)):=
    Fintype.ofInjective DFunLike.coe DFunLike.coe_injective
  have hh:=mapW_cap (quadratic_free_channel_cap (hyperbolicMatrix N).toQuadraticForm'
    (selfM p n m.mixM).toQuadraticForm' (C:=Vec (Fin p.h)) (by
      simpa [dim,Upstream.OAI.HadwigerCounterexample.Ray,HyperbolicIdx,Module.finrank_pi_fintype,two_mul] using hroom))
      (oneFreeChannelEquiv p N) Y
  rw [mapW_nested] at hh
  have hu : mapW unif (oneFreeChannelEquiv p N)=unif:=unif_equiv (oneFreeChannelEquiv p N).toEquiv
  rw [hu] at hh
  have he : (oneFreeChannelEquiv p N)∘(fun P : OneFrame p n N=>P.comp quadraticYIn)=
      fun P=>(oneChannelPairEquiv p N (oneChannels P)).1 := funext one_free_channel_value
  rw [he] at hh
  exact hh

/-- Full-rank tests use only the freely sampled channel block, so their
loss has the original fixed-channel exponent and no quadratic price. -/
theorem one_free_channel_glimpse (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤2*N)
    {d : ℕ} (T : Mat (Fin (2*N)) (Fin d)) (hT : Function.Injective T.mulVec) :
    pr (quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
      (selfM p n m.mixM).toQuadraticForm')
      (fun P=>¬Function.Injective (((oneChannelPairEquiv p N (oneChannels P)).1)ᵀ*T).mulVec)≤
        2*bp ((d:ℝ)-p.h) := by
  have hh:=pr_cap (one_free_channel_cap m hroom)
    (fun Y : HMat p (2*N)=>¬Function.Injective (Yᵀ*T).mulVec)
  rw [mapW_pr] at hh
  apply hh.trans
  have he:=quadratic_phase_glimpse_failure (H:=Fin p.h) T hT
  simpa [num] using mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤2)

end
end Lax793645Proofs.Simplifications
