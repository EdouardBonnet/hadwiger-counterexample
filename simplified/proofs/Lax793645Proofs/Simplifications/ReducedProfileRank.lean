import Lax793645Proofs.Simplifications.ReducedMixerForms
import Lax793645Proofs.Simplifications.CycleIntrinsic

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function Finset
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ}

theorem cycle_aggregate_rank (x : Profile p n) (e : Comp p.g) :
    (cycleAggregate e x).rank≤totalRank x := by
  rw [cycle_aggregate_sum]
  refine (mrk_sum_le univ _).trans (sum_le_sum fun f _=>?_)
  rcases bit_cases (cycleWeight e f) with h|h <;> simp [h]

def reducedMass (x : Profile p n) (l : Tag p.g) : ℕ:=
  ∑ e : Comp p.g,∑ b : Bool,(reducedProfile x l e b).rank
def reducedRankBudget (p : Shape) (K : ℕ):=2*Fintype.card (Comp p.g)*K

theorem reduced_profile_rank (x : Profile p n) (l : Tag p.g) (e : Comp p.g) (b : Bool) :
    (reducedProfile x l e b).rank≤totalRank x := by
  cases b
  · by_cases h:inc e l
    · rw [reduced_profile_reverse x l e h]
      exact cycle_aggregate_rank x e
    simp [reducedProfile,h]
  by_cases h:cycleOrigin e=l
  · simp [reducedProfile,h]
  rw [reduced_profile_forward x l e h]
  exact single_le_sum (f:=fun i : Comp p.g=>(x i).rank) (fun i _=>Nat.zero_le _) (mem_univ e)

theorem reduced_mass_bound (x : Profile p n) (l : Tag p.g) :
    reducedMass x l≤reducedRankBudget p (totalRank x) := by
  refine (sum_le_sum fun e _=>sum_le_sum fun b _=>reduced_profile_rank x l e b).trans_eq ?_
  simp only [sum_const,card_univ,Fintype.card_bool,smul_eq_mul,reducedRankBudget]
  ring

theorem reduced_profile_zero (hg : 3≤p.g) (x : Profile p n) (l : Tag p.g)
    (hz : ∀ e b,reducedProfile x l e b=0) : x=0 := by
  haveI : NeZero p.g:=⟨by omega⟩
  have hout (e : Comp p.g) (he : cycleOrigin e≠l) : x e=0 := by
    simpa only [reduced_profile_forward x l e he] using hz e true
  funext e
  by_cases he:cycleOrigin e=l
  · let t : Tag p.g:=l-1
    let f:=CycleGeometry.forward (by omega : 2≤p.g) t
    have ht:CycleGeometry.next t=l:=by rw [CycleGeometry.next_eq_add]; exact sub_add_cancel _ _
    have hi:inc f l:=(CycleGeometry.inc_forward _ _ _).mpr (Or.inr ht)
    have heq:CycleGeometry.forward (by omega : 2≤p.g) l=e:=by
      rw [←he,cycle_forward_origin hg]
    have hf:cycleWeight f e=1:=by
      simpa only [f,ht,heq] using cycle_weight_next hg t
    have hall (f' : Comp p.g) (hfe:f'≠e) : x f'=0 := by
      apply hout
      intro h
      apply hfe
      rw [←cycle_forward_origin hg f',h,heq]
    have hsum:cycleAggregate f x=x e := by
      rw [cycle_aggregate_sum,sum_eq_single e,hf,one_smul]
      · intro f' _ hfe
        rw [hall f' hfe,smul_zero]
      simp
    have hh:=hz f false
    rw [reduced_profile_reverse x l f hi,hsum] at hh
    exact hh
  exact hout e he

theorem reduced_mass_positive (hg : 3≤p.g) (x : Profile p n) (l : Tag p.g)
    (hx : 0<totalRank x) : 1≤reducedMass x l := by
  by_contra h
  have hr:reducedMass x l=0:=by omega
  have hz (e : Comp p.g) (b : Bool) : reducedProfile x l e b=0 := by
    by_contra hne
    have hh:1≤(reducedProfile x l e b).rank:=matrix_nonzero_rank hne
    have h₁:(reducedProfile x l e b).rank≤∑ c:Bool,(reducedProfile x l e c).rank:=
      single_le_sum (f:=fun c:Bool=>(reducedProfile x l e c).rank)
        (fun _ _=>Nat.zero_le _) (mem_univ b)
    have h₂:(∑ c:Bool,(reducedProfile x l e c).rank)≤reducedMass x l:=
      single_le_sum (f:=fun e : Comp p.g=>∑ c:Bool,(reducedProfile x l e c).rank)
        (fun _ _=>Nat.zero_le _) (mem_univ e)
    omega
  have he:=reduced_profile_zero hg x l hz
  simp only [he,totalRank,Pi.zero_apply,Matrix.rank_zero,sum_const_zero] at hx
  omega

end
end Lax793645Proofs.Simplifications
