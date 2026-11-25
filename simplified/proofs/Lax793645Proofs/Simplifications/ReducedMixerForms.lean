import Lax793645Proofs.Simplifications.ReducedMixers

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function Finset
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}

theorem sum_tag_star {V : Type*} [AddCommMonoid V] (l : Tag p.g) (f : Comp p.g→V) :
    (∑ e : TagStar l,f e.val)=∑ e,if inc e l then f e else 0 := by
  rw [←sum_filter]
  exact (sum_subtype _ (by simp) f).symm

theorem lift_smul_left (a : F) (L R X : Moment p n) :
    liftM (a •L) R X=a •liftM L R X := by
  simp only [liftM_def,Matrix.smul_mul]

def reducedProfile (x : Profile p n) (l : Tag p.g) (e : Comp p.g) (b : Bool) : Moment p n:=
  if b then if cycleOrigin e=l then 0 else x e
  else if inc e l then cycleAggregate e x else 0

theorem reduced_qmix (hg : Odd p.g) (d : ReducedDraw p n)
    (x : Profile p n) (l : Tag p.g) :
    qmix (reducedMixer d) x l=
      ∑ j : Fin p.J,∑ e : Comp p.g,
        (liftM (d.1 (j,e))ᵀ (d.2.1 (j,e))ᵀ (reducedProfile x l e true)+
          liftM (d.1 (j,e)) (d.2.1 (j,e)) (reducedProfile x l e false)) := by
  unfold qmix
  apply sum_congr rfl
  intro j _
  simp only [reducedMixer,Matrix.transpose_smul,lift_smul_left,sum_add_distrib]
  apply congrArg₂ (·+·)
  · rw [sum_comm]
    apply sum_congr rfl
    intro e _
    rw [←sum_smul,sum_tag_star,cycle_weight_star hg]
    by_cases h:cycleOrigin e=l <;> simp [reducedProfile,h]
  rw [sum_tag_star l (fun e=>∑ f,cycleWeight e f •liftM (d.1 (j,e)) (d.2.1 (j,e)) (x f))]
  apply sum_congr rfl
  intro e _
  by_cases h:inc e l
  · simp only [h,if_true,reducedProfile,Bool.false_eq_true,if_false]
    rw [cycle_aggregate_sum,map_sum]
    apply sum_congr rfl
    intro f _
    rw [map_smul]
  simp only [h,if_false,reducedProfile,Bool.false_eq_true,map_zero]

theorem reduced_profile_forward (x : Profile p n) (l : Tag p.g) (e : Comp p.g)
    (h : cycleOrigin e≠l) : reducedProfile x l e true=x e := by
  simp [reducedProfile,h]

theorem reduced_profile_reverse (x : Profile p n) (l : Tag p.g) (e : Comp p.g)
    (h : inc e l) : reducedProfile x l e false=cycleAggregate e x := by
  simp [reducedProfile,h]

end
end Lax793645Proofs.Simplifications
