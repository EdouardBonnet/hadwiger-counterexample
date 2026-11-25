import Lax793645Proofs.Simplifications.OnePrimalImageBounds
import Lax793645Proofs.Simplifications.OnePinInjection
import Lax793645Proofs.Simplifications.IndependentInjectionWitnesses

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

theorem one_unit_component_event_cap {w : Wgt (OneUnit p n N)} {H : ℝ}
    (m : Mixer p n) (i : Bool)
    (hcap : ∀ o,mapW w (fun x=>x i) o≤H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N)
    (e : Comp p.g) (Q : OneFrame p n N→Prop) :
    pr w (fun x=>Q (x i e))≤H*
      pr (quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
        (selfM p n m.mixM).toQuadraticForm') Q := by
  have hp:=pr_cap hcap (fun o=>Q (o e))
  rw [mapW_pr] at hp
  have hc:=product_projection_law
    (fun _ : Comp p.g=>quadraticChannelRaw (C:=Vec (Fin p.h))
      (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm')
    (fun _=>unifOn_law (quadratic_channel_frames_exist
      (hyperbolicMatrix N).toQuadraticForm' (hyperbolic_matrix_nondegenerate N)
      (selfM p n m.mixM).toQuadraticForm' (C:=Vec (Fin p.h)) (one_frame_room hroom))) e
  have hc' : mapW (oneRaw m N) (fun o=>o e)=
      quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
        (selfM p n m.mixM).toQuadraticForm' := by
    convert hc using 1 <;> congr!
  have ht:=mapW_pr (oneRaw m N) (fun o=>o e) Q
  rw [hc'] at ht
  exact hp.trans_eq (congrArg (H*·) ht.symm)

def oneRoot (P : OneUnit p n N→Space (Ray p n)) (i : Bool) (e : Comp p.g)
    (x : OneUnit p n N) : Space (Vec (HyperbolicIdx N)) :=
  (P x).map (onePrimal (x i e))

def oneStrike (C : OneUnit p n N→Space (Hyperbolic p.h)) (j : Bool) (e : Comp p.g)
    (v : Vec (HyperbolicIdx N)) (y : OneUnit p n N) : Prop :=
  oneChannelPullback (y j e) v∈C y

def oneFireBill (p : Shape) (k K : ℕ) (H : ℝ) :=
  H*oneChannelPrice p*bp ((2*(p.h:ℝ)+k)*K-2*(p.h:ℝ)*k)

theorem one_strike_frame_bound
    (C : OneUnit p n N→Space (Hyperbolic p.h)) (K : ℕ) (hK : ∀ y,dim (C y)≤K)
    {v : Wgt (OneUnit p n N)} (hv : SubLaw v) {H : ℝ} (hH : 0≤H)
    (m : Mixer p n) (j : Bool) (e : Comp p.g)
    (hcap : ∀ o,mapW v (fun x=>x j) o≤H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N)
    {k : ℕ} (Y : Mat (HyperbolicIdx N) (Fin k)) (hY : Function.Injective Y.mulVec) :
    pr v (fun y=>∀ a,oneStrike C j e (Y.col a) y)≤oneFireBill p k K H := by
  let E:=LinearMap.toMatrix' (oneAmbientCoordinates N).toLinearMap
  have hE : Function.Injective E.mulVec := by
    intro x y h
    exact (oneAmbientCoordinates N).injective
      (by simpa only [E,LinearMap.toMatrix'_mulVec,LinearEquiv.coe_coe] using h)
  have hh:=one_pin_strikers hv (fun y=>oneChannelRows (y j e))
    (one_unit_channel_rows_cap hH m j hcap hroom hN e) C K hK
    (E*Y) (inj_comp_mat _ _ hE hY)
  have he (a : Fin k) : (E*Y).col a=oneAmbientCoordinates N (Y.col a) := by
    rw [show (E*Y).col a=E*ᵥY.col a from rfl,LinearMap.toMatrix'_mulVec]
    rfl
  simpa only [he,oneStrike,oneChannelPullback,LinearMap.comp_apply,LinearEquiv.coe_coe,
    Matrix.coe_mulVecLin,oneFireBill] using hh

/-- The actual one-frame laws supply both hypotheses of the finite
independent-witness extraction. No joint kernel-injectivity assumption
is introduced. -/
theorem one_injection_tail
    (P : OneUnit p n N→Space (Ray p n)) (C : OneUnit p n N→Space (Hyperbolic p.h))
    (K k : ℕ) (hP : ∀ x,dim (P x)≤K) (hC : ∀ y,dim (C y)≤K)
    (w v : Wgt (OneUnit p n N)) (hw : IsLaw w) (hv : IsLaw v)
    (m : Mixer p n) (i j : Bool) (e : Comp p.g)
    {A B l : ℝ} (hA : 0≤A) (hB : 0≤B) (hl : 0<l)
    (hwcap : ∀ o,mapW w (fun x=>x i) o≤A*oneRaw m N o)
    (hvcap : ∀ o,mapW v (fun x=>x j) o≤B*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N) (h5 : 5≤N)
    (hmiss : A*bp (num (Row p n)+k+3-2*(N:ℝ))≤l) :
    pr v (fun y=>3*l≤pr w (fun x=>rootFans (oneRoot P i e) (oneStrike C j e) x y))≤
      oneFireBill p k K B/(pushCost l K)^k := by
  apply root_cannon (oneRoot P i e) (fun x=>LinearMap.range (onePrimal (x i e)))
    (oneStrike C j e) K k (fun x=>(Submodule.finrank_map_le ..).trans (hP x))
    (fun x v hv=>by obtain ⟨u,_,rfl⟩:=hv; exact ⟨u,rfl⟩) w v hw hv hl ?_ ?_ ?_
  · exact mul_nonneg (mul_nonneg hB (bp_pos _).le) (bp_pos _).le
  · intro T hT
    have hh:=one_unit_component_event_cap m i hwcap hroom e
      (fun P=>¬Disjoint (LinearMap.range (onePrimal P)) T)
    apply (hh.trans (mul_le_mul_of_nonneg_left (one_primal_intersection_cap m hroom h5 T) hA)).trans
      (le_trans ?_ hmiss)
    apply mul_le_mul_of_nonneg_left (bp_le ?_) hA
    have ht : (dim T:ℝ)≤k:=by exact_mod_cast hT
    linarith
  · intro Y hY
    exact one_strike_frame_bound C K hC hv.sub hB m j e hvcap hroom hN Y hY

end
end Lax793645Proofs.Simplifications
