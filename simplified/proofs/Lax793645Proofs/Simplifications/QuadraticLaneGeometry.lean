import Lax793645Proofs.Simplifications.QuadraticNetworkTrace
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionedBatchLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
  [DecidableEq I] [DecidableEq J] [DecidableEq G] {N : ℕ}

def laneLift (i : I) (M : Mat J J) : Mat (I×J) (I×J):=
  fun x y=>if x.1=i ∧ y.1=i then M x.2 y.2 else 0

theorem lane_lift_pairing (i : I) (M : Mat J J) (H : Mat (I×J) (I×J)) :
    mpair (laneLift i M) H=mpair M (H.submatrix (Prod.mk i) (Prod.mk i)) := by
  unfold mpair
  simp only [Fintype.sum_prod_type,laneLift,ite_mul,zero_mul]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,ite_and]
  simp

def laneInside (M : Mat (I×J) (I×J)) : Mat (I×J) (I×J):=
  fun x y=>if x.1=y.1 then M x y else 0

theorem lane_inside_pairing (M H : Mat (I×J) (I×J)) :
    mpair (laneInside M) H=∑ i,mpair (M.submatrix (Prod.mk i) (Prod.mk i))
      (H.submatrix (Prod.mk i) (Prod.mk i)) := by
  unfold mpair
  simp only [Fintype.sum_prod_type,laneInside,ite_mul,zero_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp [eq_comm]

theorem quadratic_lane_road (g : Route (I×J) G) (Z : Mat (I×J) (I×J))
    (x : Rack (I×J) N) :
    quadraticTraced (crowded g) Z ((rackCoordinates (I×J) N).symm x) ↔
      quadraticTraced (crossroads g) Z ((rackCoordinates (I×J) N).symm x) ∧
      ∀ i,quadraticTraced (crowded (street g i)) (Z.submatrix (Prod.mk i) (Prod.mk i))
        ((rackCoordinates J N).symm (led i x)) := by
  have hgram i : (x.1ᵀ*x.2).submatrix (Prod.mk i) (Prod.mk i)=
      (led i x).1ᵀ*(led i x).2 := by ext u v; rfl
  simp only [quadraticTraced,gramPrimitive,layer_form]
  constructor
  · intro h
    change ∀ M,Mᵀ=M → withinRail M (crowded g) → mpair M (x.1ᵀ*x.2)=mpair M Z at h
    constructor
    · intro M hs hm
      apply h M hs
      intro u v huv
      exact hm u v (fun he=>huv (mem_sdiff.mp he).1)
    · intro i M hs hm
      have hsym : (laneLift i M)ᵀ=laneLift i M := by
        ext u v
        have hv : M v.2 u.2=M u.2 v.2:=congrFun (congrFun hs u.2) v.2
        simp only [transpose_apply,laneLift,and_comm,hv]
      have hsup : withinRail (laneLift i M) (crowded g) := by
        intro u v huv
        by_cases he : u.1=i ∧ v.1=i
        · rw [laneLift,if_pos he]
          apply hm
          intro hz
          apply huv
          apply mem_filter.mpr
          refine ⟨mem_univ _,?_⟩
          have hv:=(mem_filter.mp hz).2
          have hu : (i,u.2)=u:=Prod.ext he.1.symm rfl
          have hvv : (i,v.2)=v:=Prod.ext he.2.symm rfl
          simpa only [street,hu,hvv] using hv
        · exact if_neg he
      have hh:=h _ hsym hsup
      rw [lane_lift_pairing,lane_lift_pairing,hgram] at hh
      exact hh
  · rintro ⟨hc,hl⟩ M hs hm
    let D:=laneInside M
    let R:=M+D
    have hD : Dᵀ=D := by
      ext u v
      change (if v.1=u.1 then M v u else 0)=(if u.1=v.1 then M u v else 0)
      have hv : M v u=M u v:=congrFun (congrFun hs u) v
      simp only [eq_comm,hv]
    have hR : Rᵀ=R := by rw [show R=M+D from rfl,transpose_add,hs,hD]
    have hsupport : withinRail R (crossroads g) := by
      intro u v huv
      change M u v+(if u.1=v.1 then M u v else 0)=0
      by_cases he : u.1=v.1
      · rw [if_pos he,char_two]
      · rw [if_neg he,add_zero]
        apply hm
        intro h
        apply huv
        exact mem_sdiff.mpr ⟨h,fun hi=>he (mem_filter.mp hi).2⟩
    have hcross:=hc R hR hsupport
    have hdiag : mpair D (x.1ᵀ*x.2)=mpair D Z := by
      rw [show D=laneInside M from rfl,lane_inside_pairing,lane_inside_pairing]
      apply Finset.sum_congr rfl
      intro i _
      rw [hgram]
      apply hl i
      · ext u v
        exact congrFun (congrFun hs (i,u)) (i,v)
      · intro u v huv
        apply hm
        intro h
        apply huv
        exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩
    change mpair R (x.1ᵀ*x.2)=mpair R Z at hcross
    simp only [R,mpair_add,hdiag] at hcross
    exact add_right_cancel hcross

end
end Lax793645Proofs.Simplifications
