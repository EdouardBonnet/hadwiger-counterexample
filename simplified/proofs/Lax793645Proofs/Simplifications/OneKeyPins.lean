import Lax793645Proofs.Simplifications.OneUnaryRecords

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

abbrev OneKeyAt (t : Tagging p I) (e : Comp p.g) := {a : I // inc e (t a)}

instance oneKeyAtFintype (t : Tagging p I) (e : Comp p.g) : Fintype (OneKeyAt t e):=by
  classical
  infer_instance

def oneKeyMatrix (v : Volley p n I) (t : Tagging p I) (e : Comp p.g) :
    Mat (OneColumn p n) (OneKeyAt t e):=
  fun i a=>oneEndpointInjection (v.obj a.val) (v.rayAt a.val,0) i

def oneKeyPlan (v : Volley p n I) (t : Tagging p I) : ImagePlan (Comp p.g) (OneColumn p n):=
  fun e=>colSp (oneKeyMatrix v t e)

def oneKeySlots (t : Tagging p I) := ∑ e,Fintype.card (OneKeyAt t e)

theorem one_key_slots (t : Tagging p I) : oneKeySlots t=Fintype.card I*tagDegree p.g := by
  classical
  let E : (Σ e : Comp p.g,OneKeyAt t e)≃(Σ a : I,TagStar (t a)):={
    toFun:=fun ⟨e,a⟩=>⟨a.val,⟨e,a.property⟩⟩
    invFun:=fun ⟨a,e⟩=>⟨e.val,⟨a,e.property⟩⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  have h:=Fintype.card_congr E
  simpa only [Fintype.card_sigma,card_star,Finset.sum_const,Finset.card_univ,
    smul_eq_mul,oneKeySlots] using h

theorem one_key_matrix_image (v : Volley p n I) (t : Tagging p I)
    (x : OneUnit p n N) (e : Comp p.g) (a : OneKeyAt t e) :
    (oneCoordinateImages x e*oneKeyMatrix v t e).col a=
      oneAmbientCoordinates N (oneVolleyKeys v t x a.val ⟨e,a.property⟩) := by
  have he:=one_endpoint_images x e (v.obj a.val) (v.rayAt a.val,0)
  exact he

theorem one_keys_freeze (v : Volley p n I) (t : Tagging p I)
    (a : ImagePin (Comp p.g) (OneColumn p n) (2*N)) (x y : OneUnit p n N)
    (hx : imagePinAgree oneCoordinateImages a x) (hy : imagePinAgree oneCoordinateImages a y)
    (hkey : oneVolleyKeys v t x=oneVolleyKeys v t y) :
    imagePinAgree oneCoordinateImages ⟨a.sp⊔oneKeyPlan v t,oneCoordinateImages x⟩ y := by
  intro e u hu
  obtain ⟨s,hs,k,hk,rfl⟩:=Submodule.mem_sup.mp hu
  rw [Matrix.mulVec_add,Matrix.mulVec_add,hy e s hs,hx e s hs]
  congr 1
  obtain ⟨z,rfl⟩:=hk
  have hM : oneCoordinateImages y e*oneKeyMatrix v t e=
      oneCoordinateImages x e*oneKeyMatrix v t e := by
    apply Matrix.ext
    intro i j
    have h:=congrArg (fun K : OneKeys t N=>oneAmbientCoordinates N (K j.val ⟨e,j.property⟩)) hkey.symm
    exact congrFun ((one_key_matrix_image v t y e j).trans (h.trans (one_key_matrix_image v t x e j).symm)) i
  change oneCoordinateImages y e*ᵥ(oneKeyMatrix v t e*ᵥz)=
    oneCoordinateImages x e*ᵥ(oneKeyMatrix v t e*ᵥz)
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hM]

theorem one_key_frozen_rank (v : Volley p n I) (t : Tagging p I)
    (P : ImagePlan (Comp p.g) (OneColumn p n))
    (hi : ∀ e,Function.Injective (oneKeyMatrix v t e).mulVec)
    (hd : ∀ e,Disjoint (oneKeyPlan v t e) (P e)) :
    imagePlanRank (P⊔oneKeyPlan v t)=imagePlanRank P+oneKeySlots t := by
  rw [image_plan_disjoint_rank P (oneKeyPlan v t) (fun e=>(hd e).symm)]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact mrk_inj.mp (hi e)

end
end Lax793645Proofs.Simplifications
