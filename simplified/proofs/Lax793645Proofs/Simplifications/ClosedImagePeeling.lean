import Lax793645Proofs.Simplifications.ImagePinFamilies

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] {N : ℕ}

def imagePinClear (X : A→C→Mat (Fin N) I) (a : ImagePin C I N) (ζ : ℝ) (w : Wgt A) :=
  ∀ b : ImagePin C I N,pr w (imagePinAgree X b)≤
    fee N ζ (imagePlanRank (a.sp⊔b.sp)-imagePlanRank a.sp)

structure ImageClosure (C I : Type) [Fintype C] [Fintype I] (c : ℕ) where
  close : ImagePlan C I→ImagePlan C I
  extensive : ∀ P,P≤close P
  idempotent : ∀ P,close (close P)=close P
  growth : ∀ P Q,P≤Q→close P=P→
    imagePlanRank (close Q)-imagePlanRank P≤c*(imagePlanRank Q-imagePlanRank P)

/-- Closed-pin peeling with the original spreading exponent. The raw
image cap is required only for closed pins, and closure costs a factor c
in the rank budget. -/
theorem closed_image_heavy_leaf
    (X : A→C→Mat (Fin N) I) (c : ℕ) (hc : 1≤c) (cl : ImageClosure C I c)
    {r w : Wgt A} {D ζ : ℝ} (hz : 0<ζ) (hz' : ζ<1) (hn : 0<N)
    (hR : ∀ b : ImagePin C I N,cl.close b.sp=b.sp→
      pr r (imagePinAgree X b)≤fee N ((ζ/c)/4) (imagePlanRank b.sp))
    (hcap : ∀ x,w x≤bp (D*N)*r x) (hw : ∀ x,0≤w x)
    (R : Finset A) (a : ImagePin C I N) (ha : cl.close a.sp=a.sp)
    (hf : ∀ x∈R,imagePinAgree X a x)
    {K : ℕ} (hK : D+ζ≤((ζ/c)-(ζ/c)/4)*K)
    (hpos : bp (-ζ*N)<pr w (fun x=>x∈R)) :
    ∃ (S : Finset A) (b : ImagePin C I N),S⊆R ∧
      0<pr w (fun x=>x∈S) ∧ (∀ x∈S,imagePinAgree X b x) ∧
      a.sp≤b.sp ∧ cl.close b.sp=b.sp ∧
      imagePlanRank b.sp≤ imagePlanRank a.sp+K ∧
      imagePinClear X b ζ (onW w (fun x=>x∈S)) ∧
      ∀ x,onW w (fun x=>x∈S) x≤bp ((D+K+1)*N)*r x := by
  classical
  have hc' : (0:ℝ)<c:=by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hc)
  have hc1 : (1:ℝ)≤c:=by exact_mod_cast hc
  let η:=ζ/c
  have hη : 0<η:=div_pos hz hc'
  have hη' : η<1:=(div_lt_one hc').mpr (hz'.trans_le hc1)
  have hn' : (0:ℝ)<N:=by exact_mod_cast hn
  have hr : ∀ x,0≤r x := by
    intro x
    by_contra! h
    exact not_lt_of_ge ((hw x).trans (hcap x)) (mul_neg_of_pos_of_neg (bp_pos _) h)
  let cut:=bp (-ζ*N)
  let q (b : ImagePin C I N):=imagePlanRank b.sp-imagePlanRank a.sp
  let s (b : ImagePin C I N):=R.filter (imagePinAgree X b)
  let mass (b : ImagePin C I N):=pr w (fun x=>x∈s b)
  let heavy (b : ImagePin C I N):=a.sp≤b.sp ∧ cl.close b.sp=b.sp ∧
    cut*fee N η (q b)<mass b
  have hstart : heavy a := by
    have hs : s a=R:=by ext x; simp [s]; exact hf x
    refine ⟨le_rfl,ha,?_⟩
    simpa only [q,Nat.sub_self,cut,mass,hs,fee,Nat.cast_zero,mul_zero,zero_mul,bp_zero,mul_one] using hpos
  have bound (b : ImagePin C I N) (hb : heavy b) : q b≤K := by
    have hmo : (q b:ℝ)≤ imagePlanRank b.sp:=by exact_mod_cast Nat.sub_le _ _
    have he : cut*fee N η (q b)<bp (D*N)*fee N (η/4) (q b) := by
      refine hb.2.2.trans_le ?_
      calc
        mass b≤pr w (imagePinAgree X b):=pr_mono hw (fun x hx=>(Finset.mem_filter.mp hx).2)
        _≤bp (D*N)*pr r (imagePinAgree X b):=pr_cap hcap _
        _≤_:=mul_le_mul_of_nonneg_left ((hR b hb.2.1).trans (by
          unfold fee
          apply bp_le
          apply mul_le_mul_of_nonneg_right _ hn'.le
          exact mul_le_mul_of_nonpos_left hmo (by linarith))) (bp_pos _).le
    unfold cut fee at he
    rw [←bp_add,←bp_add] at he
    have hh : -ζ*N+(-(1-η)*(q b)*N)<D*N+(-(1-η/4)*(q b)*N) :=
      lt_of_not_ge (fun h=>not_lt_of_ge (bp_le h) he)
    have hi : (η-η/4)*(q b:ℝ)<D+ζ := by
      apply (mul_lt_mul_iff_left₀ hn').mp
      linarith only [hh]
    have hj:=(mul_lt_mul_iff_right₀ (show 0<η-η/4 by linarith)).mp (hi.trans_le hK)
    exact_mod_cast hj.le
  let T:={t : ℕ | ∃ b,heavy b ∧ q b=t}
  have hbounded : BddAbove T:=⟨K,fun t ⟨b,hb,he⟩=>he ▸ bound b hb⟩
  obtain ⟨b,hb,hmax⟩ : ∃ b,heavy b ∧ q b=sSup T:=
    Nat.sSup_mem (show T.Nonempty from ⟨_,a,hstart,rfl⟩) hbounded
  have hm : 0<mass b:=(mul_pos (bp_pos _) (bp_pos _)).trans hb.2.2
  let v:=onW w (fun x=>x∈s b)
  have hv : IsLaw v:=normW_law (subW_nonneg hw _) hm
  have hp:=bound b hb
  have hba : imagePlanRank a.sp≤ imagePlanRank b.sp:=image_plan_rank_mono hb.1
  refine ⟨s b,b,Finset.filter_subset _ _,hm,fun x hx=>(Finset.mem_filter.mp hx).2,
    hb.1,hb.2.1,?_,?_,?_⟩
  · dsimp only [q] at hp
    omega
  · intro B
    by_contra! he
    let S₀:=b.sp⊔B.sp
    let T₀:=cl.close S₀
    let E (x : A):=x∈s b ∧ imagePinAgree X B x
    have hEprob : pr v E=pr v (imagePinAgree X B) := by
      dsimp only [v]
      rw [pr_on,pr_on]
      congr 1
      apply congrArg (pr w)
      funext x
      exact propext (by dsimp only [E]; tauto)
    have hS : imagePlanRank b.sp≤ imagePlanRank S₀:=image_plan_rank_mono le_sup_left
    have hgrowth : ((imagePlanRank T₀-imagePlanRank b.sp:ℕ):ℝ)≤
        (c:ℝ)*(imagePlanRank S₀-imagePlanRank b.sp:ℕ) := by
      exact_mod_cast cl.growth b.sp S₀ le_sup_left hb.2.1
    have he' : fee N ζ (imagePlanRank S₀-imagePlanRank b.sp)<pr v E:=hEprob.symm ▸ he
    obtain ⟨x₀,hx₀,hcost⟩:=closed_pin_family_completion v hv.nz E X S₀ T₀
      (cl.extensive S₀) (fun x hx y hy e z hz=>by
        obtain ⟨u,hu,t,ht,rfl⟩:=Submodule.mem_sup.mp hz
        rw [Matrix.mulVec_add,Matrix.mulVec_add,
          (Finset.mem_filter.mp hx.1).2 e u hu,(Finset.mem_filter.mp hy.1).2 e u hu,
          hx.2 e t ht,hy.2 e t ht])
      (imagePlanRank b.sp) hS c ζ hc' hz.le hgrowth he'
    let J : ImagePin C I N:=⟨T₀,X x₀⟩
    have hBJ : b.sp≤J.sp:=le_trans le_sup_left (cl.extensive S₀)
    have hJclosed : cl.close J.sp=J.sp:=cl.idempotent S₀
    have hjoin : mass J=mass b*pr v (fun x=>E x ∧ imagePinAgree X J x) := by
      rw [←pr_of_on hw]
      apply congrArg (pr w)
      funext x
      apply propext
      constructor
      · intro hx
        obtain ⟨hr,hj⟩:=Finset.mem_filter.mp hx
        have hf : imagePinAgree X ⟨S₀,X x₀⟩ x:=fun e u hu=>hj e u (cl.extensive S₀ e hu)
        obtain ⟨hbp,hBp⟩:=(image_pin_agree_sup X b B
          (Finset.mem_filter.mp hx₀.1).2 hx₀.2).mp hf
        exact ⟨Finset.mem_filter.mpr ⟨hr,hbp⟩,⟨Finset.mem_filter.mpr ⟨hr,hbp⟩,hBp⟩,hj⟩
      · rintro ⟨hx,_,hj⟩
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,hj⟩
    have hdim : imagePlanRank b.sp≤ imagePlanRank J.sp:=image_plan_rank_mono hBJ
    have hdim' : imagePlanRank b.sp≤ imagePlanRank T₀:=hdim
    have hsum : q b+(imagePlanRank T₀-imagePlanRank b.sp)=q J:=by
      change imagePlanRank b.sp-imagePlanRank a.sp+(imagePlanRank T₀-imagePlanRank b.sp)=
        imagePlanRank T₀-imagePlanRank a.sp
      omega
    have hfee : fee N η (q J)=fee N η (q b)*fee N η (imagePlanRank T₀-imagePlanRank b.sp) := by
      unfold fee
      rw [←bp_add,←hsum]
      push_cast
      ring_nf
    have hJh : heavy J := by
      refine ⟨hb.1.trans hBJ,hJclosed,?_⟩
      rw [hjoin,hfee,←mul_assoc]
      exact (mul_lt_mul_of_pos_right hb.2.2 (bp_pos _)).trans
        (mul_lt_mul_of_pos_left hcost hm)
    have ht : 0< imagePlanRank S₀-imagePlanRank b.sp := by
      by_contra! h
      have hz0 : imagePlanRank S₀-imagePlanRank b.sp=0:=Nat.eq_zero_of_le_zero h
      change fee N ζ (imagePlanRank S₀-imagePlanRank b.sp)<_ at he
      simp only [hz0,fee,Nat.cast_zero,mul_zero,zero_mul,bp_zero] at he
      exact not_lt_of_ge ((pr_le_tot hv.nz).trans_eq hv.total) he
    have hsT : imagePlanRank S₀≤ imagePlanRank T₀:=image_plan_rank_mono (cl.extensive S₀)
    have hsup : q J≤sSup T:=le_csSup hbounded ⟨J,hJh,rfl⟩
    have hle : q J≤q b:=hsup.trans_eq hmax.symm
    omega
  · intro x
    apply (on_mon hw (mul_pos (bp_pos _) (bp_pos _)) hb.2.2.le x).trans
    apply (mul_le_mul_of_nonneg_left (hcap x)
      (inv_nonneg_of_nonneg (mul_pos (bp_pos _) (bp_pos _)).le)).trans
    rw [←mul_assoc,←bp_add,←bp_neg,←bp_add]
    apply mul_le_mul_of_nonneg_right _ (hr x)
    apply bp_le
    have hq : (0:ℝ)≤q b:=Nat.cast_nonneg _
    have hqK : (q b:ℝ)≤K:=by exact_mod_cast hp
    nlinarith [mul_le_mul_of_nonneg_right hqK hn'.le,
      mul_nonneg hq (mul_pos hη hn').le,mul_lt_mul_of_pos_right hz' hn']

end
end Lax793645Proofs.Simplifications
