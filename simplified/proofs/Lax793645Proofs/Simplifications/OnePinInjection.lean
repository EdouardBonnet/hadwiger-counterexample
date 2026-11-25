import Lax793645Proofs.Simplifications.OneChannelImageBounds
import Lax793645Proofs.Simplifications.OneFrozenTables

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

def oneChannelPullback (P : OneFrame p n N) : Vec (HyperbolicIdx N)→ₗ[F]Hyperbolic p.h :=
  (hyperbolicCoordinates p.h).toLinearMap.comp
    ((oneChannelRows P).mulVecLin.comp (oneAmbientCoordinates N).toLinearMap)

theorem one_channel_pullback_first (P : OneFrame p n N)
    (v : Vec (HyperbolicIdx N)) (j : Fin p.h) :
    (oneChannelPullback P v).1 j=
      (hyperbolicMatrix N).toQuadraticForm'.polarBilin (oneChannelY P j) v := by
  change dotProduct ((oneChannelPairEquiv p N (oneChannels P)).1.col j)
    (oneAmbientCoordinates N v)=_
  rw [one_channel_pair_y,one_channel_coordinate_y,one_dual_coordinates_dot]

theorem one_channel_pullback_second (P : OneFrame p n N)
    (v : Vec (HyperbolicIdx N)) (j : Fin p.h) :
    (oneChannelPullback P v).2 j=
      (hyperbolicMatrix N).toQuadraticForm'.polarBilin (oneChannelX P j) v := by
  change dotProduct ((oneChannelPairEquiv p N (oneChannels P)).2.col j)
    (oneAmbientCoordinates N v)=_
  rw [one_channel_pair_x,one_channel_coordinate_x,one_dual_coordinates_dot]

/-- The channel map used by quadratic realization is exactly the
ordinary matrix of polar evaluations on the ambient primal image. -/
theorem one_actual_left_pullback (x y : OneUnit p n N) (e : Comp p.g)
    (i j : Bool) (v : Ray p n) :
    unitLeftChannels p.h (oneUnitActual x y e) j (jointInjection i v)=
      oneChannelPullback (y j e) (onePrimal (x i e) v) := by
  apply Prod.ext <;> funext a
  · have he:=unit_left_channels_pairing p.h (oneUnitActual x y e) j (jointInjection i v)
      (0,Pi.single a 1)
    rw [hyperbolic_polar] at he
    simp only [dotProduct_single,mul_one,dotProduct_zero,zero_dotProduct,add_zero,zero_add] at he
    rw [he,one_channel_pullback_first]
    change (hyperbolicMatrix N).toQuadraticForm'.polarBilin
      (oneUnitMap x e (jointInjection i v,0)) (oneUnitMap y e (0,Pi.single j (0,Pi.single a 1)))=_
    rw [one_unit_map_primal,one_unit_map_channel,binary_polar_symm]
    rfl
  · have he:=unit_left_channels_pairing p.h (oneUnitActual x y e) j (jointInjection i v)
      (Pi.single a 1,0)
    rw [hyperbolic_polar] at he
    simp only [single_dotProduct,one_mul,dotProduct_zero,zero_dotProduct,add_zero,zero_add] at he
    rw [he,one_channel_pullback_second]
    change (hyperbolicMatrix N).toQuadraticForm'.polarBilin
      (oneUnitMap x e (jointInjection i v,0)) (oneUnitMap y e (0,Pi.single j (Pi.single a 1,0)))=_
    rw [one_unit_map_primal,one_unit_map_channel,binary_polar_symm]
    rfl

/-- Only a kernel vector supported at one endpoint needs to be excluded.
Shared pinned vectors across the two endpoints are permitted. -/
theorem frozen_endpoint_kernel_disjoint
    (S : Space (JointRay p n)) (P : Space (Ray p n))
    (C : Space (Hyperbolic p.h)) (G : JointRay p n→ₗ[F]Hyperbolic p.h) (i : Bool)
    (h : ∀ v∈P,G (jointInjection i v)∈C→v=0) :
    Disjoint (frozenChannelKernel p.h S C (G.domRestrict S)) (P.map (jointInjection i)) := by
  rw [Submodule.disjoint_def]
  rintro v ⟨s,hs,hsv⟩ ⟨u,hu,huv⟩
  have hg : G (jointInjection i u)∈C := by
    change G s.val∈C at hs
    simpa only [show s.val=jointInjection i u from hsv.trans huv.symm] using hs
  rw [←huv,h u hu hg,map_zero]

def onePinSafe (P : Bool→Comp p.g→Space (Ray p n))
    (C : Bool→Comp p.g→Space (Hyperbolic p.h)) (x y : OneUnit p n N) : Prop :=
  ∀ e i j,∀ v∈P i e,
    unitLeftChannels p.h (oneUnitActual x y e) j (jointInjection i v)∈C j e→v=0

theorem one_pin_safe_kernel (P : Bool→Comp p.g→Space (Ray p n))
    (C : Bool→Comp p.g→Space (Hyperbolic p.h)) (x y : OneUnit p n N)
    (h : onePinSafe P C x y) (S : Comp p.g→Space (JointRay p n)) :
    ∀ e i j,Disjoint (frozenChannelKernel p.h (S e) (C j e)
      ((unitLeftChannels p.h (oneUnitActual x y e) j).domRestrict (S e)))
      ((P i e).map (jointInjection i)) := by
  intro e i j
  exact frozen_endpoint_kernel_disjoint _ _ _ _ _ (h e i j)

theorem one_pin_failure_witness (P : Bool→Comp p.g→Space (Ray p n))
    (C : Bool→Comp p.g→Space (Hyperbolic p.h)) (x y : OneUnit p n N)
    (m : Mixer p n) (hx : ∀ i,oneFrameLaw m (x i)) (h : ¬onePinSafe P C x y) :
    ∃ e i j,∃ v∈(P i e).map (onePrimal (x i e)),
      v≠0 ∧ oneChannelPullback (y j e) v∈C j e := by
  unfold onePinSafe at h
  push_neg at h
  obtain ⟨e,i,j,v,hv,hc,hn⟩:=h
  refine ⟨e,i,j,onePrimal (x i e) v,⟨v,hv,rfl⟩,?_,?_⟩
  · intro he
    exact hn (one_primal_injective (hx i) e (he.trans (map_zero _).symm))
  · rwa [←one_actual_left_pullback]

/-- A sampled pin space may depend on all the unit data. Confining k
independent ambient directions to it still forces a low-rank channel table. -/
theorem one_pin_strikers {A : Type} [Fintype A] {w : Wgt A} (hw : SubLaw w)
    (read : A→Mat (HyperbolicIdx p.h) (Fin (2*N))) {H : ℝ}
    (hcap : ∀ T,mapW w read T≤H*unif T)
    (C : A→Space (Hyperbolic p.h)) (K : ℕ) (hK : ∀ x,dim (C x)≤K)
    {k : ℕ} (P : Mat (Fin (2*N)) (Fin k)) (hP : Function.Injective P.mulVec) :
    pr w (fun x=>∀ j,hyperbolicCoordinates p.h (read x*ᵥP.col j)∈C x)≤
      H*bp ((2*(p.h:ℝ)+k)*K-2*(p.h:ℝ)*k) := by
  classical
  apply (pr_mono hw.nz ?_).trans (one_channel_rank_cap hw read hcap P hP K)
  intro x hx
  have hc : colSp (read x*P)≤(C x).map (hyperbolicCoordinates p.h).symm.toLinearMap := by
    rw [colSp,range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    refine ⟨hyperbolicCoordinates p.h (read x*ᵥP.col j),hx j,?_⟩
    simp only [LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
    ext a
    rfl
  exact (show (read x*P).rank=dim (colSp (read x*P)) from (colSp_dim _).symm).trans_le
    ((Submodule.finrank_mono hc).trans ((Submodule.finrank_map_le ..).trans (hK x)))

end
end Lax793645Proofs.Simplifications
