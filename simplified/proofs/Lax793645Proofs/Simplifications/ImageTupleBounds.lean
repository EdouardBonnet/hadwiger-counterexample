/-
Generalizes the finite image-character argument in ImageCharacterBounds
from the vendored Apache-2.0 OpenAI construction to arbitrary image arrays.
-/
import Lax793645Proofs.Simplifications.ImagePinFamilies
import Lax793645Proofs.Simplifications.ClosedImagePeeling
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ImageCharacterBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] {N : ℕ}

abbrev ImageTuple (C : Type) (r : C→ℕ) (N : ℕ) := ∀ e,Mat (Fin N) (Fin (r e))

theorem image_plan_disjoint_rank (P Q : ImagePlan C I) (h : ∀ e,Disjoint (P e) (Q e)) :
    imagePlanRank (P⊔Q)=imagePlanRank P+imagePlanRank Q := by
  unfold imagePlanRank
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have he:=Submodule.finrank_sup_add_finrank_inf_eq (P e) (Q e)
  rw [(h e).eq_bot,finrank_bot,add_zero] at he
  exact he

def imageTuple (X : A→C→Mat (Fin N) I) (r : C→ℕ) (M : ∀ e,Mat I (Fin (r e)))
    (x : A) : ImageTuple C r N:=fun e=>X x e*M e

theorem image_tuple_cap (X : A→C→Mat (Fin N) I) (r : C→ℕ)
    (M : ∀ e,Mat I (Fin (r e))) {w : Wgt A} {a : ImagePin C I N} {ζ : ℝ}
    (hM : ∀ e,Function.Injective (M e).mulVec)
    (hfree : ∀ e,Disjoint (colSp (M e)) (a.sp e))
    (hw : SubLaw w) (hc : imagePinClear X a ζ w) :
    ∀ y,mapW w (imageTuple X r M) y≤fee N ζ (∑ e,r e) := by
  classical
  intro y
  let P (x : A):=imageTuple X r M x=y
  change pr w P≤_
  by_cases hp : 0<pr w P
  · obtain ⟨x,hx,_⟩:=exists_of_pr_pos hw.nz hp
    let Q : ImagePlan C I:=fun e=>colSp (M e)
    let b : ImagePin C I N:=⟨Q,X x⟩
    have hm : pr w P≤pr w (imagePinAgree X b):=by
      apply pr_mono hw.nz
      intro z hz e v hv
      obtain ⟨u,rfl⟩:=hv
      have he:=congrFun (hz.trans hx.symm) e
      change X z e*M e=X x e*M e at he
      change X z e*ᵥ(M e*ᵥu)=X x e*ᵥ(M e*ᵥu)
      rw [mulVec_mulVec,mulVec_mulVec,he]
    have hr : imagePlanRank Q=∑ e,r e:=by
      apply Finset.sum_congr rfl
      intro e _
      exact (mrk_inj.mp (hM e)).trans (Fintype.card_fin _)
    have hd : imagePlanRank (a.sp⊔b.sp)-imagePlanRank a.sp=∑ e,r e:=by
      rw [image_plan_disjoint_rank a.sp Q (fun e=>(hfree e).symm),Nat.add_sub_cancel_left,hr]
    exact hm.trans (hd ▸ hc b)
  · exact (not_lt.mp hp).trans (bp_pos _).le

def imageTuplePair (r : C→ℕ) (N : ℕ) :
    ImageTuple C r N→ₗ[F]ImageTuple C r N→ₗ[F]F where
  toFun x:=∑ e,mpair (x e)∘ₗLinearMap.proj e
  map_add' x y:=LinearMap.ext fun v=>by
    simp only [LinearMap.sum_apply,LinearMap.comp_apply,Pi.add_apply,LinearMap.add_apply,
      mpair_add,Finset.sum_add_distrib]
  map_smul' c x:=LinearMap.ext fun v=>by
    simp only [LinearMap.sum_apply,LinearMap.comp_apply,Pi.smul_apply,RingHom.id_apply,
      LinearMap.smul_apply,mpair_smul,Finset.mul_sum,smul_eq_mul]

theorem image_tuple_pair_apply (r : C→ℕ) (x y : ImageTuple C r N) :
    imageTuplePair r N x y=∑ e,mpair (x e) (y e) := by
  simp only [imageTuplePair,LinearMap.sum_apply,LinearMap.coe_mk,AddHom.coe_mk]
  rfl

theorem image_tuple_pair_inj (r : C→ℕ) (N : ℕ) : Function.Injective (imageTuplePair r N) := by
  classical
  rw [←LinearMap.ker_eq_bot]
  refine le_bot_iff.mp (fun x hx=>?_)
  change imageTuplePair r N x=0 at hx
  have hh (e : C) : mpair (x e)=0:=by
    apply LinearMap.ext
    intro M
    have he:=LinearMap.congr_fun hx (Pi.single e M)
    rw [image_tuple_pair_apply,Finset.sum_eq_single e] at he
    · rwa [Pi.single_eq_same] at he
    · intro j _ hj; simp [hj]
    · simp
  have he : x=0:=funext (fun e=>mpair_nondeg _ (hh e))
  exact he ▸ Submodule.zero_mem _

theorem image_tuple_dimension (r : C→ℕ) (N : ℕ) :
    dim (ImageTuple C r N)=N*∑ e,r e := by
  unfold ImageTuple dim
  rw [finrank_pi_fintype,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact (dim_mat _ _).trans (by simp)

/-- The character estimate needs only spreading of finite image arrays;
it is independent of the number of primal modes and the raw frame law. -/
theorem image_tuple_character (X Y : A→C→Mat (Fin N) I) (r : C→ℕ)
    (M T : ∀ e,Mat I (Fin (r e))) {u w : Wgt A} (hu : IsLaw u) (hw : IsLaw w)
    {a b : ImagePin C I N} (hc : imagePinClear X a 0.05 u) (hd : imagePinClear Y b 0.05 w)
    (hM : ∀ e,Function.Injective (M e).mulVec ∧ Disjoint (colSp (M e)) (a.sp e))
    (hT : ∀ e,Function.Injective (T e).mulVec ∧ Disjoint (colSp (T e)) (b.sp e))
    (hr : 1≤∑ e,r e) :
    |avg (pairW u w) (fun x=>wsign (imageTuplePair r N
      (imageTuple X r M x.1) (imageTuple Y r T x.2)))|≤bp (-0.45*N) := by
  classical
  let H:=imageTuplePair r N
  let g:=imageTuple X r M
  let g':=imageTuple Y r T
  let q:=mapW u g
  let v:=mapW w g'
  let t:=∑ e,r e
  have he : avg (pairW u w) (fun x=>wsign (H (g x.1) (g' x.2)))=
      avg v (fun y=>avg q (fun x=>wsign (H x y))) := by
    rw [pairW_avg]
    unfold q v
    rw [mapW_avg]
    simp_rw [mapW_avg]
    exact avg_avg ..
  have hp (x) : q x≤fee N 0.05 t:=image_tuple_cap X r M
    (fun e=>(hM e).1) (fun e=>(hM e).2) hu.sub hc x
  have hq (x) : v x≤fee N 0.05 t:=image_tuple_cap Y r T
    (fun e=>(hT e).1) (fun e=>(hT e).2) hw.sub hd x
  have hh:=walsh_mass H (image_tuple_pair_inj r N) q v (fun _=>1) (fun _=>1)
    (fun _=>by norm_num) (fun _=>by norm_num) (mapW_law hu g).sub (mapW_law hw g').sub hp hq
  change |avg (pairW u w) _|≤_
  rw [he]
  let R:=avg v (fun y=>avg q (fun x=>wsign (H x y)))
  have hi : R^2≤(bp (-0.45*N))^2:=by
    simp only [one_mul] at hh
    apply hh.trans
    rw [card_space,image_tuple_dimension]
    unfold fee
    change bp (↑(N*t))*_*_≤_
    rw [←bp_add,←bp_add,pow_two,←bp_add]
    apply bp_le
    have ht : 1≤(t:ℝ):=by exact_mod_cast hr
    push_cast
    have hn:=mul_le_mul_of_nonneg_left ht (show (0:ℝ)≤N by positivity)
    linarith only [hn]
  exact le_of_pow_le_pow_left₀ (show (2:ℕ)≠0 by decide) (bp_pos _).le (sq_abs R ▸ hi)

end
end Lax793645Proofs.Simplifications
