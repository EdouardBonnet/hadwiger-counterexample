import Lax793645Proofs.Simplifications.OneClosedPinLaws
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ChannelFrameLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev OneChannels (p : Shape) (N : ℕ) := Vec (HyperbolicIdx p.h)→ₗ[F]Vec (HyperbolicIdx N)

instance oneChannelsFintype (p : Shape) (N : ℕ) : Fintype (OneChannels p N):=
  Fintype.ofInjective (fun f : OneChannels p N=>⇑f) DFunLike.coe_injective

def oneChannelIn (p : Shape) (n : ℕ) : Vec (HyperbolicIdx p.h)→ₗ[F]OneFull p n:=
  (LinearMap.inr F _ _).comp (hyperbolicCoordinates p.h).toLinearMap

theorem one_channel_in_inj (p : Shape) (n : ℕ) : Function.Injective (oneChannelIn p n) := by
  intro v w h
  apply (hyperbolicCoordinates p.h).injective
  exact congrArg Prod.snd h

variable {p : Shape} {n N : ℕ}

def oneChannels (x : OneFrame p n N) : OneChannels p N:=x.comp (oneChannelIn p n)

def oneChannelPrice (p : Shape) := bp ((2*(p.h:ℝ))^2+2)

/-- The complete pair of channel blocks has bounded density relative to
independent uniform columns. Its price depends only on the fixed channel
budget, not on n or on the prescribed primal quadratic form. -/
theorem one_channels_cap (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N)
    (T : OneChannels p N) :
    mapW (quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
      (selfM p n m.mixM).toQuadraticForm') oneChannels T≤oneChannelPrice p*unif T := by
  have hc:=quadratic_channel_frames_exist (hyperbolicMatrix N).toQuadraticForm'
    (hyperbolic_matrix_nondegenerate N) (selfM p n m.mixM).toQuadraticForm'
    (C:=Vec (Fin p.h)) (one_frame_room hroom)
  have hn : 2*num (HyperbolicIdx p.h)+3≤N:=by
    simp only [num,HyperbolicIdx,Fintype.card_sum,Fintype.card_fin,Nat.cast_add]
    exact_mod_cast (show 2*(p.h+p.h)+3≤N by omega)
  have hh:=quadratic_image_cap N (quadraticChannelClass (C:=Vec (Fin p.h))
    (selfM p n m.mixM).toQuadraticForm') hc (oneChannelIn p n) (one_channel_in_inj p n) hn T
  apply hh.trans_eq
  unfold oneChannelPrice
  rw [unif_apply,card_space,←bp_neg,←bp_add]
  apply congrArg bp
  have hd : dim (OneChannels p N)=(2*p.h)*(2*N):=by
    simp [dim,OneChannels,Module.finrank_linearMap,HyperbolicIdx,Vec,
      Module.finrank_pi_fintype]
    ring
  rw [hd]
  simp only [num,HyperbolicIdx,Fintype.card_sum,Fintype.card_fin,Nat.cast_mul,
    Nat.cast_add,Nat.cast_ofNat]
  ring

def oneChannelCube (o : OneOrient p n N) : Comp p.g→OneChannels p N:=fun e=>oneChannels (o e)

def oneCubePrice (p : Shape) := (oneChannelPrice p)^(Fintype.card (Comp p.g))

theorem one_channel_cube_cap (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N)
    (x : Comp p.g→OneChannels p N) :
    mapW (oneRaw m N) oneChannelCube x≤oneCubePrice p*prodW (fun _ : Comp p.g=>unif) x := by
  classical
  unfold oneRaw oneChannelCube
  rw [mapW_repeat]
  apply (Finset.prod_le_prod (fun e _=>pr_nonneg (unifOn_sub _).nz)
    (fun e _=>one_channels_cap m hroom hN (x e))).trans_eq
  rw [Finset.prod_mul_distrib]
  simp [oneCubePrice,prodW]

end
end Lax793645Proofs.Simplifications
