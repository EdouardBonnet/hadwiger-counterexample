import Lax793645Proofs.Simplifications.ImageGramHits

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] {N : ℕ}

/-- Conditioning on a heavy key-and-record cell retains spreading after
the key directions are added to the stored pins. -/
theorem image_cell_clear (X : A→C→Mat (Fin N) I)
    {a f : ImagePin C I N} {k : ℕ} {ζ : ℝ} {w : Wgt A}
    (hz : ζ≤0.004) (hkz : ζ*k≤0.004) (hw : SubLaw w)
    (ha : imagePinClear X a ζ w) (hF : a.sp≤f.sp)
    (hk : imagePlanRank f.sp=imagePlanRank a.sp+k)
    (S : A→Prop) (hS : ∀ x,S x→imagePinAgree X f x)
    (ht : tau N k≤pr w S) : IsLaw (onW w S) ∧ imagePinClear X f 0.05 (onW w S) := by
  classical
  have hpos : 0<pr w S:=(bp_pos _).trans_le ht
  have hl : IsLaw (onW w S):=normW_law (subW_nonneg hw.nz _) hpos
  refine ⟨hl,fun b=>?_⟩
  let t:=imagePlanRank (f.sp⊔b.sp)-imagePlanRank f.sp
  by_cases he : t=0
  · change pr _ _≤fee N _ t
    rw [he,fee]
    simp only [Nat.cast_zero,mul_zero,zero_mul,bp_zero]
    exact (pr_le_tot hl.nz).trans_eq hl.total
  let R (x : A):=S x ∧ imagePinAgree X b x
  by_cases hr : 0<pr w R
  · obtain ⟨x,⟨hx,hB⟩,_⟩:=exists_of_pr_pos hw.nz hr
    let c : ImagePin C I N:=⟨f.sp⊔b.sp,X x⟩
    have hc : pr w R≤fee N ζ (imagePlanRank (a.sp⊔c.sp)-imagePlanRank a.sp):=
      (pr_mono hw.nz (q:=imagePinAgree X c)
        (fun y hy=>(image_pin_agree_sup X f b (hS x hx) hB).mpr ⟨hS y hy.1,hy.2⟩)).trans (ha c)
    have hnew : imagePlanRank (a.sp⊔c.sp)-imagePlanRank a.sp=k+t:=by
      rw [sup_eq_right.mpr (hF.trans le_sup_left)]
      have hle : imagePlanRank f.sp≤ imagePlanRank c.sp:=image_plan_rank_mono le_sup_left
      change imagePlanRank c.sp-imagePlanRank a.sp=k+(imagePlanRank c.sp-imagePlanRank f.sp)
      omega
    rw [hnew] at hc
    rw [pr_on]
    apply (div_le_div₀ (bp_pos _).le hc (bp_pos _) ht).trans
    unfold fee
    rw [←bp_sub]
    apply bp_le
    have h1 : (1:ℝ)≤t:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr he
    have hg:=mul_le_mul_of_nonneg_right hz (show (0:ℝ)≤t by positivity)
    rw [Nat.cast_add]
    change _≤ -(1-0.05)*(t:ℝ)*N
    rw [←sub_mul]
    exact mul_le_mul_of_nonneg_right (by linarith only [hkz,h1,hg]) (Nat.cast_nonneg _)
  · rw [pr_on]
    exact (div_nonpos_of_nonpos_of_nonneg (not_lt.mp hr) hpos.le).trans (bp_pos _).le

abbrev ImageLedger (P : ImagePlan C I) := ∀ e,Mat (Fin (dim (P e))) I

instance imageLedgerFintype (P : ImagePlan C I) : Fintype (ImageLedger P) := by
  classical
  letI (e : C) : Fintype (Mat (Fin (dim (P e))) I):=inferInstance
  infer_instance

theorem image_ledger_dimension (P : ImagePlan C I) :
    dim (ImageLedger P)=imagePlanRank P*Fintype.card I := by
  unfold ImageLedger dim imagePlanRank
  rw [finrank_pi_fintype,Finset.sum_mul]
  exact Finset.sum_congr rfl (fun e _=>(dim_mat _ _).trans (by simp))

def imageLedger (X : A→C→Mat (Fin N) I) (a : ImagePin C I N) (x : A) : ImageLedger a.sp:=
  fun e=>(pack (a.sp e))ᵀ*(a.target e)ᵀ*X x e

theorem image_pin_pack (X : A→C→Mat (Fin N) I) (a : ImagePin C I N) {x : A}
    (hx : imagePinAgree X a x) (e : C) : X x e*pack (a.sp e)=a.target e*pack (a.sp e) := by
  apply Matrix.ext
  intro i j
  have hj : (pack (a.sp e)).col j∈a.sp e:=by
    apply (colSp_pack (a.sp e)).le
    refine ⟨Pi.single j 1,?_⟩
    simp [Matrix.mulVec_single]
  exact congrFun (hx e _ hj) i

theorem image_ledger_value (X Y : A→C→Mat (Fin N) I) (a : ImagePin C I N)
    {x y : A} (hy : imagePinAgree X a y) (e : C) :
    imageLedger Y a x e=(pack (a.sp e))ᵀ*imageActual X Y y x e := by
  have he:=image_pin_pack X a hy e
  unfold imageLedger imageActual
  rw [←transpose_mul,←he,transpose_mul,Matrix.mul_assoc]

theorem image_ledger_rows (X Y : A→C→Mat (Fin N) I) (a : ImagePin C I N)
    {x y x' y' : A} (hy : imagePinAgree X a y) (hy' : imagePinAgree X a y')
    (hx : imageLedger Y a x=imageLedger Y a x') :
    imageRowAgree a.sp (imageActual X Y y x) (imageActual X Y y' x') := by
  intro e u hu v
  have he : (pack (a.sp e))ᵀ*imageActual X Y y x e=
      (pack (a.sp e))ᵀ*imageActual X Y y' x' e:=by
    rw [←image_ledger_value X Y a hy,←image_ledger_value X Y a hy',hx]
  obtain ⟨r,rfl⟩:=(pack_mem_iff ..).mp hu
  have hv (P : Mat I I) : evmat P (pack (a.sp e)*ᵥr) v=
      evmat ((pack (a.sp e))ᵀ*P) r v:=by
    unfold evmat
    rw [←Matrix.mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_comm]
  rw [hv,hv,he]

end
end Lax793645Proofs.Simplifications
