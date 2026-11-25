/-
Generalizes the finite Gram-character quotient argument in the vendored
Apache-2.0 OpenAI construction to arbitrary finite image arrays.
-/
import Lax793645Proofs.Simplifications.ImageTupleBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] {N : ℕ}
abbrev ImageCross (C I : Type) := C→Mat I I

def imageCrossPair (M : ImageCross C I) : ImageCross C I→ₗ[F]F:=
  ∑ e,mpair (M e)∘ₗLinearMap.proj e

theorem image_cross_pair_apply (M Q : ImageCross C I) :
    imageCrossPair M Q=∑ e,mpair (M e) (Q e) := by
  simp only [imageCrossPair,LinearMap.sum_apply]
  rfl

def imageRowAgree (P : ImagePlan C I) (M Q : ImageCross C I) :=
  ∀ e,∀ v∈P e,∀ w,evmat (M e) v w=evmat (Q e) v w

def imageActual (X Y : A→C→Mat (Fin N) I) (x y : A) : ImageCross C I:=
  fun e=>(X x e)ᵀ*Y y e

theorem image_pair_transfer {J U : Type} [Fintype J] [Fintype U]
    (X Y : Mat U I) (B T : Mat I J) :
    mpair (B*Tᵀ) (Xᵀ*Y)=mpair (X*B) (Y*T) := by
  have pair_trace {K L : Type} [Fintype K] [Fintype L] (P Q : Mat K L) :
      mpair P Q=(P*Qᵀ).trace:=rfl
  rw [pair_trace,pair_trace,Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose]
  rw [←Matrix.mul_assoc _ Yᵀ X,Matrix.trace_mul_comm _ X]
  simp only [Matrix.mul_assoc]

theorem image_opposite_projection (S : Space (Vec I)) :
    ∃ P : Mat I I,(∀ x,x-P*ᵥx∈S) ∧ Disjoint (colSp P) S := by
  classical
  obtain ⟨B,hB⟩:=proj_exists S ⊥ disjoint_bot_right
  refine ⟨1-B,fun x=>?_,?_⟩
  · rw [Matrix.sub_mulVec,Matrix.one_mulVec,sub_sub_cancel]
    exact hB.onto x
  rw [disjoint_iff_inf_le]
  rintro x ⟨⟨y,rfl⟩,hy⟩
  rw [mulVecLin_apply,Matrix.sub_mulVec,Matrix.one_mulVec] at hy ⊢
  have hx:=hB.fixes _ hy
  rw [Matrix.mulVec_sub,hB.fixes (B*ᵥy) (hB.onto _),sub_self] at hx
  rw [←hx]
  exact Submodule.zero_mem _

theorem image_free_pull (M : ImageCross C I) (s t : ImagePlan C I) :
    ∃ P : ImageCross C I,(∀ e,Disjoint (colSp (P e)) (s e) ∧
      Disjoint (colSp (P e)ᵀ) (t e)) ∧
      ∀ X Y,imageRowAgree s X Y→
        imageRowAgree t (fun e=>(X e)ᵀ) (fun e=>(Y e)ᵀ)→
        imageCrossPair M (X-Y)=imageCrossPair P (X-Y) := by
  classical
  choose S hS hL using fun e=>image_opposite_projection (s e)
  choose T hT hR using fun e=>image_opposite_projection (t e)
  let P (e : C):=liftM (S e) (T e) (M e)
  refine ⟨P,fun e=>⟨(hL e).mono_left (colSp_lift_le ..),by
    unfold P; rw [liftM_transpose]; exact (hR e).mono_left (colSp_lift_le ..)⟩,
    fun X Y hX hY=>?_⟩
  rw [image_cross_pair_apply,image_cross_pair_apply]
  apply Finset.sum_congr rfl
  intro e _
  let Z:=X e-Y e
  have he : pullM (S e) (T e) Z=Z:=by
    apply evmat_ext
    intro x y
    rw [evmat_pull]
    let x':=S e*ᵥx
    let y':=T e*ᵥy
    have h₁ : evmat Z (x-x') y=0:=by
      rw [show Z=X e-Y e from rfl,evmat_subM,hX e _ (hS e x),sub_self]
    have h₂ : evmat Z x' (y-y')=0:=by
      have h:=hY e _ (hT e y) x'
      simp only [evmat_transpose] at h
      rw [show Z=X e-Y e from rfl,evmat_subM,h,sub_self]
    unfold evmat at h₁ h₂ ⊢
    rw [sub_dotProduct,sub_eq_zero] at h₁
    rw [Matrix.mulVec_sub,dotProduct_sub,sub_eq_zero] at h₂
    exact h₂.symm.trans h₁.symm
  change mpair (M e) Z=mpair (liftM _ _ _) Z
  rw [mpair_comm (M e),mpair_comm (liftM _ _ _),mpair_liftM,
    show liftM (S e)ᵀ (T e)ᵀ Z=Z from he]

theorem image_factor_free (M : ImageCross C I) (s t : ImagePlan C I)
    (h : ∀ e,Disjoint (colSp (M e)) (s e) ∧ Disjoint (colSp (M e)ᵀ) (t e)) :
    ∃ (r : C→ℕ) (B T : ∀ e,Mat I (Fin (r e))),
      (∀ e,Function.Injective (B e).mulVec ∧ Disjoint (colSp (B e)) (s e)) ∧
      (∀ e,Function.Injective (T e).mulVec ∧ Disjoint (colSp (T e)) (t e)) ∧
      ∀ e,M e=B e*(T e)ᵀ := by
  classical
  choose B T hB hT hM using fun e=>rank_product (M e)
  let G (e : C):=(T e)ᵀ
  have hg e : Function.Injective (G e).mulVec:=
    transpose_surj_iff.mp (by unfold G; rw [Matrix.transpose_transpose]; exact hT e)
  refine ⟨_,B,G,fun e=>⟨hB e,(h e).1.mono_left ?_⟩,
    fun e=>⟨hg e,(h e).2.mono_left ?_⟩,
    fun e=>by unfold G; rw [Matrix.transpose_transpose,hM]⟩
  · rintro x ⟨v,rfl⟩
    obtain ⟨w,rfl⟩:=hT e v
    refine ⟨w,?_⟩
    rw [mulVecLin_apply,mulVecLin_apply,Matrix.mulVec_mulVec,hM]
  · rintro x ⟨v,rfl⟩
    obtain ⟨w,rfl⟩:=transpose_surj_iff.mpr (hB e) v
    refine ⟨w,?_⟩
    rw [mulVecLin_apply,mulVecLin_apply]
    unfold G
    rw [Matrix.mulVec_mulVec,←transpose_mul,hM]

/-- Quotient out the frozen rows and columns before applying the
bilinear character estimate. No raw-law or frame hypothesis is needed. -/
theorem image_gram_character (X Y : A→C→Mat (Fin N) I) (Q M : ImageCross C I)
    {u w : Wgt A} (hu : IsLaw u) (hw : IsLaw w) {a b : ImagePin C I N}
    (hc : imagePinClear X a 0.05 u) (hd : imagePinClear Y b 0.05 w)
    (h : ∀ x,u x≠0→∀ y,w y≠0→imageRowAgree a.sp (imageActual X Y x y) Q ∧
      imageRowAgree b.sp (fun e=>(imageActual X Y x y e)ᵀ) (fun e=>(Q e)ᵀ)) :
    let Z:=avg (pairW u w) (fun x=>wsign (imageCrossPair M (imageActual X Y x.1 x.2-Q)))
    Z=1 ∨ |Z|≤bp (-0.45*N) := by
  classical
  dsimp only
  obtain ⟨P,hP,hpull⟩:=image_free_pull M a.sp b.sp
  obtain ⟨r,B,T,hB,hT,hfactor⟩:=image_factor_free P a.sp b.sp hP
  have he : avg (pairW u w) (fun x=>wsign (imageCrossPair M (imageActual X Y x.1 x.2-Q)))=
      avg (pairW u w) (fun x=>wsign (imageCrossPair P (imageActual X Y x.1 x.2-Q))) := by
    apply avg_congr
    intro x hx
    rw [hpull _ _ (h x.1 (left_ne_zero_of_mul hx) x.2 (right_ne_zero_of_mul hx)).1
      (h x.1 (left_ne_zero_of_mul hx) x.2 (right_ne_zero_of_mul hx)).2]
  rw [he]
  by_cases hr : 1≤∑ e,r e
  · right
    have hi (x y : A) : imageCrossPair P (imageActual X Y x y)=
        imageTuplePair r N (imageTuple X r B x) (imageTuple Y r T y) := by
      rw [image_cross_pair_apply,image_tuple_pair_apply]
      apply Finset.sum_congr rfl
      intro e _
      rw [hfactor,imageActual,image_pair_transfer]
      rfl
    simp only [ZModModule.sub_eq_add,map_add,wsign_add,hi]
    rw [avg_mul,abs_mul,wsign_abs,mul_one]
    exact image_tuple_character X Y r B T hu hw hc hd hB hT hr
  · left
    have hzero (e : C) : P e=0:=by
      have he : r e≤∑ j,r j:=Finset.single_le_sum (fun j _=>Nat.zero_le _) (Finset.mem_univ e)
      have hz : r e=0:=by omega
      have : IsEmpty (Fin (r e)):=hz ▸ Fin.isEmpty'
      rw [hfactor]
      ext i j
      simp [Matrix.mul_apply]
    have hz (Z : ImageCross C I) : wsign (imageCrossPair P Z)=1:=by
      rw [image_cross_pair_apply]
      have he e : mpair (P e) (Z e)=0:=by rw [hzero,mpair_comm,map_zero]
      simp_rw [he]
      simp
    simp_rw [hz]
    exact (pairW_law hu hw).avg_const _

end
end Lax793645Proofs.Simplifications
