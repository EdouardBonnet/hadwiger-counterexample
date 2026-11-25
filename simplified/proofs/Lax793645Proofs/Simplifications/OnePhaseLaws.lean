import Lax793645Proofs.Simplifications.OneChannelCoordinates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

def oneAmbientReadout (x : OneAmbient p N) : Ambient p (2*N) :=
  fun e=>quadraticMomentMap (oneAmbientCoordinates N).toLinearMap (x e)

theorem phase_pair_outer {A J : Type} [Fintype A] [Fintype J]
    (X Y : Mat A J) (v w : Vec A) :
    mpair (Y*Xᵀ) (vecMulVec v w)=
      ∑ j,dotProduct (Y.col j) v*dotProduct (X.col j) w := by
  rw [mpair_outer]
  rw [evmat,←Matrix.mulVec_mulVec,dotProduct_mulVec]
  unfold dotProduct Matrix.vecMul Matrix.mulVec
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem one_channel_coordinate_x (P : OneFrame p n N) (j : Fin p.h) :
    oneChannels P (Pi.single (Sum.inl j) 1)=oneChannelX P j := by
  change P (0,hyperbolicCoordinates p.h (Pi.single (Sum.inl j) 1))=P (0,(Pi.single j 1,0))
  apply congrArg (fun c=>P (0,c))
  apply Prod.ext <;> funext a
  · change (Pi.single (Sum.inl j) 1 : Vec (HyperbolicIdx p.h)) (Sum.inl a)=
      (Pi.single j 1 : Vec (Fin p.h)) a
    simp [Pi.single_apply]
  · change (Pi.single (Sum.inl j) 1 : Vec (HyperbolicIdx p.h)) (Sum.inr a)=0
    simp

theorem one_channel_coordinate_y (P : OneFrame p n N) (j : Fin p.h) :
    oneChannels P (Pi.single (Sum.inr j) 1)=oneChannelY P j := by
  change P (0,hyperbolicCoordinates p.h (Pi.single (Sum.inr j) 1))=P (0,(0,Pi.single j 1))
  apply congrArg (fun c=>P (0,c))
  apply Prod.ext <;> funext a
  · change (Pi.single (Sum.inr j) 1 : Vec (HyperbolicIdx p.h)) (Sum.inl a)=0
    simp
  · change (Pi.single (Sum.inr j) 1 : Vec (HyperbolicIdx p.h)) (Sum.inr a)=
      (Pi.single j 1 : Vec (Fin p.h)) a
    simp [Pi.single_apply]

theorem one_phase_component (P : OneFrame p n N) (W : Mat (HyperbolicIdx N) (HyperbolicIdx N)) :
    let C:=oneChannelPairEquiv p N (oneChannels P)
    mpair (C.2*C.1ᵀ) (quadraticMomentMap (oneAmbientCoordinates N).toLinearMap W)=
      quadraticChannelFunctional (hyperbolicMatrix N).toQuadraticForm'
        (oneChannelX P) (oneChannelY P) W := by
  classical
  letI : DecidableEq (HyperbolicIdx N):=Classical.decEq _
  let E:=LinearMap.toMatrix' (oneAmbientCoordinates N).toLinearMap
  let C:=oneChannelPairEquiv p N (oneChannels P)
  have hm : liftM Eᵀ Eᵀ (C.2*C.1ᵀ)=
      (quadraticChannelBilin (hyperbolicMatrix N).toQuadraticForm'
        (oneChannelX P) (oneChannelY P)).toMatrix' := by
    apply evmat_ext
    intro v w
    rw [←mpair_outer,←mpair_liftM,liftM_outer]
    rw [phase_pair_outer]
    simp only [C,E,LinearMap.toMatrix'_mulVec,LinearEquiv.coe_coe,
      one_channel_pair_x,one_channel_pair_y,one_channel_coordinate_x,
      one_channel_coordinate_y,one_dual_coordinates_dot]
    rw [evmat,←Matrix.toBilin'_apply',Matrix.toBilin'_toMatrix']
    simp only [quadraticChannelBilin,LinearMap.sum_apply,LinearMap.smulRight_apply,
      smul_eq_mul]
    congr!
  dsimp only
  rw [quadraticMomentMap,mpair_liftM]
  dsimp only [E,C] at hm
  convert congrArg (fun M=>mpair M W) hm using 1 <;> congr!

theorem one_phase_actual (o : OneOrient p n N) (x : OneAmbient p N) :
    uPhase p (onePhaseCube o) (oneAmbientReadout x)=oneFunctional o x := by
  simp only [uPhase,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]
  apply Finset.sum_congr rfl
  intro e _
  exact one_phase_component (o e) (x e)

def oneListens (x : OneUnit p n N) : PhasePair p (2*N):=
  (onePhaseCube (x true),onePhaseCube (x false))

theorem one_listens_raw (m : Mixer p n) :
    mapW (oneUnitRaw m N) oneListens=
      pairW (mapW (oneRaw m N) onePhaseCube) (mapW (oneRaw m N) onePhaseCube) := by
  classical
  funext y
  change pr (prodW (fun _ : Bool=>oneRaw m N)) (fun x=>oneListens x=y)=_
  have he (x : OneUnit p n N) : oneListens x=y ↔
      ∀ i,onePhaseCube (x i)=onSide y i := by
    simp [oneListens,Prod.ext_iff,Bool.forall_bool,onSide,and_comm]
  simp_rw [he]
  rw [prodW_pr (fun _ : Bool=>oneRaw m N) (fun i x=>onePhaseCube x=onSide y i)]
  simp [prodW,Fintype.prod_bool,onSide,pairW,mapW]

/-- The actual one-frame phase law is dominated by independent free
channel matrices with a price depending only on the fixed construction. -/
theorem one_phase_cap {w : Wgt (OneUnit p n N)} {c : ℝ} (hc : 0≤c)
    (m : Mixer p n) (h : ∀ x,w x≤c*oneUnitRaw m N x)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N)
    (y : PhasePair p (2*N)) :
    mapW w oneListens y≤c*oneCubePrice p^2*freeH p (2*N) y := by
  refine (mapW_cap h oneListens y).trans ?_
  rw [one_listens_raw]
  have hz (x) : 0≤mapW (oneRaw m N) onePhaseCube x:=
    pr_nonneg (prodW_law (fun _=>unifOn_law (quadratic_channel_frames_exist
      (hyperbolicMatrix N).toQuadraticForm' (hyperbolic_matrix_nondegenerate N)
      (selfM p n m.mixM).toQuadraticForm' (C:=Vec (Fin p.h)) (one_frame_room hroom)))).nz
  calc
    c*pairW _ _ y ≤ c*((oneCubePrice p*lawH p (2*N) y.1)*
      (oneCubePrice p*lawH p (2*N) y.2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (one_phase_cube_cap m hroom hN y.1)
        (one_phase_cube_cap m hroom hN y.2) (hz _)
        ((hz _).trans (one_phase_cube_cap m hroom hN y.1))) hc
    _ = _ := by unfold freeH pairW; ring

end
end Lax793645Proofs.Simplifications
