import Lax793645Proofs.Simplifications.QuadraticLaneGeometry
import Lax793645Proofs.Simplifications.QuadraticLaneCharacters
import Lax793645Proofs.Simplifications.QuadraticNetworkNormalization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
  [DecidableEq I] [DecidableEq J] [DecidableEq G] {N : ℕ}

def quadraticInjPart (g : Route I G) (x : Rack I N):=
  ∀ c,Injective (stackMatrixEquiv N (rackEquiv g N x c)).mulVec

def quadraticFramePart {g : Route I G} (Q : GeoM g) (x : Rack I N):=
  ∀ c,quadraticPairGood (Q c) (rackEquiv g N x c)

def quadraticStation {g : Route I G} (Q : GeoM g) (N : ℕ) : Wgt (Rack I N):=
  unifOn (quadraticFramePart Q)

def quadraticNetFact (g : Route I G) : ℝ:=
  (4:ℝ)^Fintype.card G*bp (dim (symmetricRail (crowded g)))

theorem quadratic_net_fact_pos (g : Route I G) : 0<quadraticNetFact g:=by
  unfold quadraticNetFact
  exact mul_pos (by positivity) (bp_pos _)

theorem quadratic_frame_exact (g : Route I G) (Q : GeoM g) :
    quadraticFramePart (N:=N) Q=
      quadraticExactNetwork g (fun i=>(1 : Mat (Port g i) (Port g i))) Q := by
  funext x
  apply propext
  apply forall_congr'
  intro i
  unfold quadraticPairGood quadraticPrescribedKernel
  simp only [transpose_one,one_mul,mul_one]
  have he : (1 : Mat (Port g i) (Port g i)).mulVecLin=LinearMap.id:=by
    ext x j
    simp
  rw [he,LinearMap.ker_id,LinearMap.ker_eq_bot]
  rfl

theorem quadratic_net_norm (g : Route I G) (Q : GeoM g)
    (hN : ∀ i,2*num (Port g i)+2≤N) :
    (quadraticNetFact g)⁻¹≤pr unif (quadraticFramePart (N:=N) Q) := by
  let L:=fun i=>(1 : Mat (Port g i) (Port g i))
  have hL i : Surjective (L i).mulVec:=by intro x; exact ⟨x,one_mulVec x⟩
  have hz:=quadratic_network_exact_pos (N:=N) g L Q hL hN
  have hc:=quadratic_network_expansion_cost (N:=N) g L Q hL hN
  simp only [sub_self,Finset.sum_const_zero,mul_zero,bp_zero,mul_one] at hc
  rw [←quadratic_frame_exact] at hz hc
  have hh:=(div_le_iff₀ hz).mp hc
  unfold quadraticNetFact
  rw [_root_.mul_inv_rev,←bp_neg]
  apply le_of_mul_le_mul_left _ (show 0<(4:ℝ)^Fintype.card G by positivity)
  calc
    _=bp (-(dim (symmetricRail (crowded g)):ℝ)):=by field_simp
    _≤_:=hh

theorem quadratic_frame_test (g : Route I G) (Q : GeoM g) (x : Rack I N) :
    quadraticFramePart Q x ↔
      quadraticTraced (crowded g) (geoMatrix g Q) ((rackCoordinates I N).symm x) ∧
        quadraticInjPart g x := by
  rw [quadratic_network_traced]
  unfold quadraticFramePart quadraticInjPart quadraticPairGood
  constructor
  · intro h
    exact ⟨fun c=>(h c).2,fun c=>(h c).1⟩
  · rintro ⟨hg,hi⟩ c
    exact ⟨hi c,hg c⟩

theorem quadratic_inj_failure (g : Route I G) (k : ℝ)
    (hk : ∀ i,num (Port g i)≤k) :
    pr unif (fun x : Rack I N=>¬quadraticInjPart g x)≤num G*(2*bp (k-N)) := by
  refine (pr_mono unif_law.nz ?_).trans (injPart_failure g N k hk)
  intro x hx hi
  apply hx
  intro c u v huv
  apply (hi c).1
  have hfirst:=congrArg (fun w : Vec (HyperbolicIdx N)=>fun j : Fin N=>w (Sum.inl j)) huv
  exact hfirst

theorem quadratic_lane_injective (g : Route (I×J) G) (x : Rack (I×J) N)
    (hx : quadraticInjPart g x) (i : I) : quadraticInjPart (street g i) (led i x) := by
  intro c
  let e:=condLane g i c
  have he : Injective e:=by
    intro u v h
    exact Subtype.ext (congrArg (fun z : Port g c=>z.val.2) h)
  have hh : stackMatrixEquiv N (rackEquiv (street g i) N (led i x) c)=
      (stackMatrixEquiv N (rackEquiv g N x c)).submatrix _root_.id e := by
    ext a b
    cases a <;> rfl
  rw [hh,←mul_embedMat]
  exact inj_comp_mat _ _ (hx c) (embedMat_inj he)

theorem quadratic_frame_road (g : Route (I×J) G) (Q : GeoM g) (x : Rack (I×J) N) :
    quadraticFramePart Q x ↔
      (quadraticTraced (crossroads g) (geoMatrix g Q) ((rackCoordinates (I×J) N).symm x) ∧
        ∀ i,quadraticFramePart (laneM Q i) (led i x)) ∧quadraticInjPart g x := by
  have hl i : (geoMatrix g Q).submatrix (Prod.mk i) (Prod.mk i)=
      geoMatrix (street g i) (laneM Q i) := by
    ext u v
    by_cases he : g (i,u)=g (i,v)
    · simp only [geoMatrix,submatrix_apply,street,dif_pos he,laneM,condLane]
    · simp only [geoMatrix,submatrix_apply,street,dif_neg he]
  simp_rw [quadratic_frame_test,quadratic_lane_road,hl]
  constructor
  · rintro ⟨⟨hc,hl⟩,hi⟩
    exact ⟨⟨hc,fun i=>⟨hl i,quadratic_lane_injective g x hi i⟩⟩,hi⟩
  · rintro ⟨⟨hc,hl⟩,hi⟩
    exact ⟨⟨hc,fun i=>(hl i).1⟩,hi⟩

end
end Lax793645Proofs.Simplifications
