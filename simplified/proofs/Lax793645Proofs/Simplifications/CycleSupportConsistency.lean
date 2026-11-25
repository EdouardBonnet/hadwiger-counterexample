import Lax793645Proofs.Simplifications.CycleMarkedProfiles

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset LinearMap
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {p : Shape} {n : ℕ}

def testerCoefficients (x : Profile p n) (α : F) (t : Tag p.g) :=
  role p n x+sharedT p n t x+α

theorem role_ordinary_bits (x : Profile p n) :
    role p n x=∑ t,ordinaryBit p n x t := by
  simp only [role,roleT,LinearMap.sum_apply,LinearMap.comp_apply,ordinaryBit]
  exact Finset.sum_comm

/-- Component tester equality determines the difference of the two
coefficient vectors directly. No normalized trace vector is involved. -/
theorem cycle_coefficient_difference (x y : Profile p n)
    (hx : x∈Xspace p n) (hy : y∈Xspace p n) (hg : Odd p.g)
    (hη : ∀ e,eta p n (x e)=eta p n (y e)) (α β : F) (t : Tag p.g) :
    testerCoefficients x α t+testerCoefficients y β t=
      α+β+ordinaryBit p n x t+ordinaryBit p n y t := by
  let o := fun t=>ordinaryBit p n x t+ordinaryBit p n y t
  have he : (fun e=>etab p n Block.S (x e)+etab p n Block.S (y e))=
      CycleGeometry.cut o := by
    funext e
    have hh:=hη e
    simp only [eta,LinearMap.add_apply,etaO_components x hx,
      etaO_components y hy] at hh
    change _=(ordinaryBit p n x e.val.1+ordinaryBit p n y e.val.1)+
      (ordinaryBit p n x e.val.2+ordinaryBit p n y e.val.2)
    linear_combination hh + char_two (etab p n Block.S (y e)) -
      char_two (ordinaryBit p n x e.val.1) - char_two (ordinaryBit p n x e.val.2)
  have hb : sharedT p n t x+sharedT p n t y=(∑ i,o i)+o t := by
    change etab p n Block.S (CycleGeometry.matchingMap t x)+
      etab p n Block.S (CycleGeometry.matchingMap t y)=_
    rw [map_matching,map_matching,←map_add]
    change CycleGeometry.matchingMap t (fun e=>etab p n Block.S (x e)+etab p n Block.S (y e))=_
    rw [he,CycleGeometry.matchingMap_cut hg]
  unfold testerCoefficients
  calc
    _=(role p n x+role p n y)+(sharedT p n t x+sharedT p n t y)+(α+β) := by abel
    _=_ := by
      rw [hb,role_ordinary_bits,role_ordinary_bits]
      simp only [o,Finset.sum_add_distrib]
      have hc : ∀ a : F,a+a=0 := char_two
      linear_combination hc (∑ i,ordinaryBit p n x i)+hc (∑ i,ordinaryBit p n y i)

theorem four_small_supports {g : ℕ} (a b c d : Fin g→F)
    (h : (bitSupport a).card+(bitSupport b).card+
      (bitSupport c).card+(bitSupport d).card<g) :
    ∃ t,a t=0 ∧ b t=0 ∧ c t=0 ∧ d t=0 := by
  classical
  let E:=((bitSupport a∪bitSupport b)∪bitSupport c)∪bitSupport d
  have hE : E.card<g := by
    exact ((card_union_le _ _).trans (Nat.add_le_add_right
      ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)) _)).trans_lt h
  obtain ⟨t,ht⟩ : ∃ t : Fin g,t∉E := by
    by_contra! hh
    have he : univ⊆E := fun t _=>hh t
    have hc := card_le_card he
    simp only [card_univ,Fintype.card_fin] at hc
    omega
  simp only [E,mem_union,not_or,bitSupport,mem_filter,mem_univ,true_and,not_not] at ht
  exact ⟨t,ht.1.1.1,ht.1.1.2,ht.1.2,ht.2⟩

/-- Small tester supports force the endpoint bits to agree. The ordinary
support bound may come either from true intersection or from the pin rank. -/
theorem cycle_support_consistency (x y : Profile p n)
    (hx : x∈Xspace p n) (hy : y∈Xspace p n) (hg : Odd p.g) (h3 : 3≤p.g)
    (hη : ∀ e,eta p n (x e)=eta p n (y e)) (α β : F)
    (hsmall : (bitSupport (testerCoefficients x α)).card+
      (bitSupport (testerCoefficients y β)).card+totalRank x+totalRank y<p.g) : α=β := by
  have hsum := Nat.add_le_add_right (Nat.add_le_add_left (ordinaryBit_support h3 x)
    ((bitSupport (testerCoefficients x α)).card+(bitSupport (testerCoefficients y β)).card))
    (bitSupport (ordinaryBit p n y)).card
  have hsum' := (hsum.trans (Nat.add_le_add_left (ordinaryBit_support h3 y) _)).trans_lt hsmall
  obtain ⟨t,ha,hb,hc,hd⟩:=four_small_supports (testerCoefficients x α)
    (testerCoefficients y β) (ordinaryBit p n x) (ordinaryBit p n y) hsum'
  have hh:=cycle_coefficient_difference x y hx hy hg hη α β t
  simp only [ha,hb,hc,hd,add_zero] at hh
  have hz : α+β+β=0+β := congrArg (·+β) hh.symm
  simpa only [add_assoc,char_two,add_zero,zero_add] using hz

end
end Lax793645Proofs.Simplifications
