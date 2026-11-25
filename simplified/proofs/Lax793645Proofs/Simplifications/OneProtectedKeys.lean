import Lax793645Proofs.Simplifications.OnePinProtection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]

theorem one_pin_extractors (v : Volley p n I) (t : Tagging p I)
    (a : ImagePlan (Comp p.g) (OneColumn p n)) (R : ℕ)
    (hv : OneProtectedVolley v t (oneEndpointPrimalPins a) R) (i : Bool) :
    ∃ E : Ray p n→ₗ[F]Vec (CallsAt v i),
      (∀ j : CallsAt v i,E (v.rayAt j.val)=Pi.single j 1) ∧
      ∀ e,oneEndpointPrimalPins a i e≤E.ker := by
  obtain ⟨E,hE,hL⟩:=selected_tensor_extractors (hv.selector i) (hv.base i) _ _
    (hv.selectorIndependent i) (hv.baseIndependent i)
  exact ⟨E,hE,fun e=>(hv.pinCross i e).trans hL⟩

theorem one_key_miss (v : Volley p n I) (t : Tagging p I)
    (a : ImagePlan (Comp p.g) (OneColumn p n)) (R : ℕ)
    (hv : OneProtectedVolley v t (oneEndpointPrimalPins a) R)
    (e : Comp p.g) (c : Vec (OneKeyAt t e)) (hc : oneKeyMatrix v t e*ᵥc∈a e) : c=0 := by
  classical
  funext j
  let i:=v.obj j.val
  let jj : CallsAt v i:=⟨j.val,by simp [Volley.here,i]⟩
  obtain ⟨E,hE,hpin⟩:=one_pin_extractors v t a R hv i
  let L : Vec (OneColumn p n)→ₗ[F]F:=
    (LinearMap.proj jj).comp (E.comp ((jointProjection i).comp
      ((LinearMap.fst F _ _).comp (oneNominalCoordinates p n).toLinearMap)))
  have hz : L (oneKeyMatrix v t e*ᵥc)=0 := by
    have hh : jointProjection i ((oneNominalCoordinates p n (oneKeyMatrix v t e*ᵥc)).1)
        ∈oneEndpointPrimalPins a i e:=⟨_,⟨_,hc,rfl⟩,rfl⟩
    exact congrFun (hpin e hh) jj
  have hcol (k : OneKeyAt t e) : L ((oneKeyMatrix v t e).col k)=if k=j then 1 else 0 := by
    change E (jointProjection i ((oneNominalCoordinates p n
      (oneEndpointInjection (v.obj k.val) (v.rayAt k.val,0))).1)) jj=_
    rw [one_nominal_endpoint_primal,joint_projection_injection]
    by_cases hk : i=v.obj k.val
    · rw [if_pos hk]
      let kk : CallsAt v i:=⟨k.val,by simp [Volley.here,←hk]⟩
      rw [hE kk]
      by_cases hj : k=j
      · subst k
        have he : kk=jj:=Subtype.ext rfl
        simp [he]
      · have he : jj≠kk:=fun he=>hj (Subtype.ext (congrArg Subtype.val he).symm)
        simp [hj,Pi.single_eq_of_ne he]
    · rw [if_neg hk,map_zero]
      have hj : k≠j:=fun h=>hk (by subst k;rfl)
      simp [hj]
  have hs : oneKeyMatrix v t e*ᵥc=∑ k,c k • ((oneKeyMatrix v t e).col k) := by
    rw [Matrix.mulVec_eq_sum]
    simp_rw [op_smul_eq_smul]
    rfl
  rw [hs,map_sum] at hz
  simp only [map_smul,hcol] at hz
  simpa using hz

theorem one_key_independent (v : Volley p n I) (t : Tagging p I)
    (a : ImagePlan (Comp p.g) (OneColumn p n)) (R : ℕ)
    (hv : OneProtectedVolley v t (oneEndpointPrimalPins a) R) (e : Comp p.g) :
    Function.Injective (oneKeyMatrix v t e).mulVec ∧ Disjoint (oneKeyPlan v t e) (a e) := by
  constructor
  · rw [←Matrix.coe_mulVecLin,←LinearMap.ker_eq_bot,Matrix.ker_mulVecLin_eq_bot_iff]
    intro c hc
    apply one_key_miss v t a R hv e c
    rw [hc]
    exact Submodule.zero_mem _
  · rw [disjoint_iff_inf_le]
    rintro x ⟨⟨c,rfl⟩,hc⟩
    have hh:=one_key_miss v t a R hv e c hc
    rw [hh,map_zero]
    exact Submodule.zero_mem _

/-- The key extension pays exactly one ambient vector for each incident
component of each selected atom. -/
theorem one_protected_key_rank (v : Volley p n I) (t : Tagging p I)
    (a : ImagePlan (Comp p.g) (OneColumn p n)) (R : ℕ)
    (hv : OneProtectedVolley v t (oneEndpointPrimalPins a) R) :
    imagePlanRank (a⊔oneKeyPlan v t)=imagePlanRank a+Fintype.card I*tagDegree p.g := by
  rw [←one_key_slots t]
  exact one_key_frozen_rank v t a (fun e=>(one_key_independent v t a R hv e).1)
    (fun e=>(one_key_independent v t a R hv e).2)

end
end Lax793645Proofs.Simplifications
