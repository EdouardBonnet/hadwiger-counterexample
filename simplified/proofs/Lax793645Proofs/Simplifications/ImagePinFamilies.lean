import Lax793645Proofs.Simplifications.ClosedPinCompletion

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev ImagePlan (C I : Type) := C→Space (Vec I)

def imagePlanRank {C I : Type} [Fintype C] [Fintype I] (P : ImagePlan C I) :=∑ e,dim (P e)

structure ImagePin (C I : Type) (N : ℕ) where
  sp : ImagePlan C I
  target : C→Mat (Fin N) I

variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] {N : ℕ}

def imagePinAgree (X : A→C→Mat (Fin N) I) (P : ImagePin C I N) (x : A) :=
  ∀ e,∀ v∈P.sp e,X x e*ᵥv=P.target e*ᵥv

theorem image_plan_rank_mono {P Q : ImagePlan C I} (h : P≤Q) : imagePlanRank P≤ imagePlanRank Q :=
  Finset.sum_le_sum (fun e _=>Submodule.finrank_mono (h e))

theorem image_pin_make_agree (X : A→C→Mat (Fin N) I) (P : ImagePlan C I) (x : A) :
    imagePinAgree X ⟨P,X x⟩ x := fun _ _ _=>rfl

theorem image_pin_agree_sup (X : A→C→Mat (Fin N) I) (P Q : ImagePin C I N)
    {x y : A} (hx : imagePinAgree X P x) (hx' : imagePinAgree X Q x) :
    imagePinAgree X ⟨P.sp⊔Q.sp,X x⟩ y↔imagePinAgree X P y ∧ imagePinAgree X Q y := by
  constructor
  · intro h
    exact ⟨fun e v hv=>(h e v (Submodule.mem_sup_left hv)).trans (hx e v hv),
      fun e v hv=>(h e v (Submodule.mem_sup_right hv)).trans (hx' e v hv)⟩
  · rintro ⟨h,h'⟩ e v hv
    obtain ⟨s,hs,t,ht,rfl⟩:=Submodule.mem_sup.mp hv
    rw [Matrix.mulVec_add,Matrix.mulVec_add,h e s hs,h' e t ht,hx e s hs,hx' e t ht]

/-- The completion cost is N times the sum of the new ranks. It does not
multiply N by the number of components. -/
theorem closed_pin_family_completion
    (w : Wgt A) (hw : ∀ x,0≤w x) (E : A→Prop)
    (X : A→C→Mat (Fin N) I) (S T : ImagePlan C I) (hST : S≤T)
    (hE : ∀ x,E x→∀ y,E y→∀ e,∀ v∈S e,X x e*ᵥv=X y e*ᵥv)
    (a : ℕ) (ha : a≤ imagePlanRank S) (c ζ : ℝ) (hc : 0<c) (hz : 0≤ζ)
    (hstep : ((imagePlanRank T-a:ℕ):ℝ)≤c*(imagePlanRank S-a:ℕ))
    (he : fee N ζ (imagePlanRank S-a)<pr w E) :
    ∃ x₀,E x₀ ∧ fee N (ζ/c) (imagePlanRank T-a)<
      pr w (fun x=>E x ∧ imagePinAgree X ⟨T,X x₀⟩ x) := by
  classical
  let D : ImagePlan C I:=fun e=>chopSpace (S e) (T e)
  let V:=∀ e : C,Mat (Fin N) (Fin (dim (D e)))
  let f : A→V:=fun x e=>X x e*pack (D e)
  have hd : imagePlanRank S+imagePlanRank D=imagePlanRank T := by
    rw [imagePlanRank,imagePlanRank,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    exact (chopSpace_rank (S e) (T e)).trans (congrArg (fun P : Space (Vec I)=>dim P)
      (sup_eq_right.mpr (hST e)))
  have hdim : imagePlanRank S≤ imagePlanRank T:=image_plan_rank_mono hST
  have hu : imagePlanRank S-a≤ imagePlanRank T-a:=Nat.sub_le_sub_right hdim a
  letI : Fintype V:=inferInstanceAs (Fintype (∀ e : C,Mat (Fin N) (Fin (dim (D e)))))
  have hcount : num V≤bp ((((imagePlanRank T-a)-(imagePlanRank S-a):ℕ):ℝ)*N) := by
    have hu' : imagePlanRank T-a-(imagePlanRank S-a)=imagePlanRank D:=by omega
    rw [hu']
    change (Fintype.card V:ℝ)≤_
    rw [card_space]
    apply bp_le
    have hv : dim V=N*imagePlanRank D := by
      rw [show dim V=∑ e : C,dim (Mat (Fin N) (Fin (dim (D e)))) from Module.finrank_pi_fintype F]
      simp only [dim_mat,Fintype.card_fin,imagePlanRank,Finset.mul_sum]
    rw [hv]
    push_cast
    exact le_of_eq (mul_comm _ _)
  obtain ⟨v,hv⟩:=closed_pin_step w hw E f N (imagePlanRank S-a) (imagePlanRank T-a)
    c ζ hc hz hu hstep hcount he
  obtain ⟨x₀,hx₀,_⟩:=exists_of_pr_pos hw ((bp_pos _).trans hv)
  refine ⟨x₀,hx₀.1,hv.trans_le (pr_mono hw ?_)⟩
  intro x hx
  refine ⟨hx.1,?_⟩
  intro e v hv
  change v∈T e at hv
  have hjoin : S e⊔D e=T e:=(chopSpace_join (S e) (T e)).trans (sup_eq_right.mpr (hST e))
  rw [←hjoin] at hv
  obtain ⟨s,hs,d,hd',rfl⟩:=Submodule.mem_sup.mp hv
  change X x e*ᵥ(s+d)=X x₀ e*ᵥ(s+d)
  rw [Matrix.mulVec_add,Matrix.mulVec_add,hE x hx.1 x₀ hx₀.1 e s hs]
  congr 1
  obtain ⟨u,rfl⟩:=(pack_mem_iff d (D e)).mp hd'
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
  have hsame : X x e*pack (D e)=X x₀ e*pack (D e):=congrFun (hx.2.trans hx₀.2.symm) e
  rw [hsame]

end
end Lax793645Proofs.Simplifications
