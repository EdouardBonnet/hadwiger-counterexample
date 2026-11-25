import Lax793645Proofs.Simplifications.OneKeyPins
import Lax793645Proofs.Simplifications.OneSelectedObstructions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem joint_injection_sum {D B : Type} [Fintype D] [Fintype B] [DecidableEq B] (v : Vec (D×B)) :
    ∑ i,jointInjection i (jointProjection i v)=v := by
  funext x
  simp only [Finset.sum_apply,jointInjection,LinearMap.coe_mk,AddHom.coe_mk]
  simp [jointProjection]

theorem joint_space_sup {D B : Type} [Fintype D] [Fintype B] [DecidableEq B]
    (P Q : B→Space (Vec D)) : jointSpace P⊔jointSpace Q=jointSpace (fun i=>P i⊔Q i) := by
  apply le_antisymm
  · exact sup_le (joint_space_mono (fun _=>le_sup_left)) (joint_space_mono (fun _=>le_sup_right))
  intro v hv
  choose a ha b hb he using fun i=>Submodule.mem_sup.mp (hv i)
  apply Submodule.mem_sup.mpr
  refine ⟨(fun x=>a x.2 x.1),ha,(fun x=>b x.2 x.1),hb,?_⟩
  funext ⟨d,i⟩
  exact congrFun (he i) d

theorem joint_space_of_stable {D B : Type} [Fintype D] [Fintype B] [DecidableEq B]
    (S : Space (Vec (D×B)))
    (h : ∀ i,∀ v∈S,jointInjection i (jointProjection i v)∈S) :
    S=jointSpace (fun i=>S.map (jointProjection i)) := by
  apply le_antisymm
  · intro v hv i
    exact ⟨v,hv,rfl⟩
  intro v hv
  rw [←joint_injection_sum v]
  apply S.sum_mem
  intro i _
  obtain ⟨w,hw,he⟩:=hv i
  rw [←he]
  exact h i w hw

variable {p : Shape} {n : ℕ}

def oneEndpointPrimalPins (P : ImagePlan (Comp p.g) (OneColumn p n))
    (i : Bool) (e : Comp p.g) : Space (Ray p n) :=
  (onePrimalPins P e).map (jointProjection i)

theorem one_endpoint_primal_pin_dimension (P : ImagePlan (Comp p.g) (OneColumn p n))
    (i : Bool) (e : Comp p.g) : dim (oneEndpointPrimalPins P i e)≤dim (P e) :=
  (Submodule.finrank_map_le ..).trans (one_primal_pin_dimension P e)

theorem one_nominal_endpoint_primal (i : Bool) (v : OneFull p n) :
    (oneNominalCoordinates p n (oneEndpointInjection i v)).1=jointInjection i v.1 := by
  funext ⟨r,j⟩
  cases i <;> cases j <;> simp [oneNominalCoordinates,oneEndpointInjection,
    oneEndpointCoordinates,jointInjection]

theorem one_closed_primal_pins (P : ImagePlan (Comp p.g) (OneColumn p n))
    (hP : (onePinClosure p n).close P=P) (e : Comp p.g) :
    onePrimalPins P e=jointSpace (fun i=>oneEndpointPrimalPins P i e) := by
  apply joint_space_of_stable
  intro i v hv
  obtain ⟨u,hu,rfl⟩:=hv
  have he:=one_endpoint_pin_mem (P e) (congrFun hP e) i
    (show oneEndpointProjection i u∈(P e).map (oneEndpointProjection i) from ⟨u,hu,rfl⟩)
  refine ⟨oneEndpointInjection i (oneEndpointProjection i u),he,?_⟩
  exact one_nominal_endpoint_primal i (oneEndpointProjection i u)

variable {I : Type} [Fintype I] [DecidableEq I]

theorem one_key_primal_pins (v : Volley p n I) (t : Tagging p I) (e : Comp p.g) :
    onePrimalPins (oneKeyPlan v t) e=jointSpace (fun i=>selectedAtComponent
      (fun a : CallsAt v i=>t a.val) (fun a=>v.sel a.val) (fun a=>v.par a.val) e) := by
  classical
  let L : Vec (OneColumn p n)→ₗ[F]JointRay p n:=
    (LinearMap.fst F _ _).comp (oneNominalCoordinates p n).toLinearMap
  have hcol (a : OneKeyAt t e) : L ((oneKeyMatrix v t e).col a)=
      jointInjection (v.obj a.val) (v.rayAt a.val) :=
    one_nominal_endpoint_primal (v.obj a.val) (v.rayAt a.val,0)
  apply le_antisymm
  · rintro z ⟨u,hu,rfl⟩
    change L u∈_
    have hu' : u∈Submodule.span F (Set.range (oneKeyMatrix v t e).col) := by
      change u∈LinearMap.range (oneKeyMatrix v t e).mulVecLin at hu
      rw [Matrix.range_mulVecLin] at hu
      convert hu using 1
    clear hu
    induction hu' using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨a,rfl⟩:=hu
      rw [hcol]
      apply joint_injection_mem
      apply Submodule.subset_span
      exact ⟨⟨a.val,by simp [Volley.here]⟩,a.property,rfl⟩
    | zero => exact map_zero L ▸ Submodule.zero_mem _
    | add a b _ _ ha hb => exact (map_add L a b).symm ▸ Submodule.add_mem _ ha hb
    | smul c a _ ha => exact (map_smul L c a).symm ▸ Submodule.smul_mem _ c ha
  intro z hz
  rw [←joint_injection_sum z]
  apply Submodule.sum_mem
  intro i _
  suffices hh : ∀ u∈selectedAtComponent
      (fun a : CallsAt v i=>t a.val) (fun a=>v.sel a.val) (fun a=>v.par a.val) e,
      jointInjection i u∈onePrimalPins (oneKeyPlan v t) e by exact hh _ (hz i)
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a,he,rfl⟩:=hu
    have ha : v.obj a.val=i:=(Finset.mem_filter.mp a.property).2
    have hc:=hcol (⟨a.val,he⟩ : OneKeyAt t e)
    rw [ha] at hc
    exact ⟨(oneKeyMatrix v t e).col ⟨a.val,he⟩,colSp_mem _,hc⟩
  | zero => exact map_zero (jointInjection (D:=Row p n) i) ▸ Submodule.zero_mem _
  | add a b _ _ ha hb => exact (map_add (jointInjection (D:=Row p n) i) a b).symm ▸ Submodule.add_mem _ ha hb
  | smul c a _ ha => exact (map_smul (jointInjection (D:=Row p n) i) c a).symm ▸ Submodule.smul_mem _ c ha

/-- Freezing the keys produces exactly the selected primal space used
by the quadratic realization theorem. -/
theorem one_frozen_primal_pins (v : Volley p n I) (t : Tagging p I)
    (P : ImagePlan (Comp p.g) (OneColumn p n)) (hP : (onePinClosure p n).close P=P) :
    onePrimalPins (P⊔oneKeyPlan v t)=oneSelectedPrimal v t (oneEndpointPrimalPins P) := by
  funext e
  change (P e⊔oneKeyPlan v t e).map _=_
  rw [Submodule.map_sup]
  change onePrimalPins P e⊔onePrimalPins (oneKeyPlan v t) e=_
  rw [one_closed_primal_pins P hP e,one_key_primal_pins,joint_space_sup]
  rfl

/-- Keys have no channel coordinates, so freezing them leaves the
original channel pins unchanged. -/
theorem one_key_channel_pins (v : Volley p n I) (t : Tagging p I)
    (i : Bool) (e : Comp p.g) : oneChannelPins (oneKeyPlan v t) i e=⊥ := by
  classical
  let L : Vec (OneColumn p n)→ₗ[F]Hyperbolic p.h :=
    (LinearMap.proj i).comp ((LinearMap.snd F _ _).comp (oneNominalCoordinates p n).toLinearMap)
  have hcol (a : OneKeyAt t e) : L ((oneKeyMatrix v t e).col a)=0 := by
    by_cases ha : i=v.obj a.val
    · subst i
      simp [L,oneKeyMatrix,oneEndpointInjection,oneEndpointCoordinates,oneNominalCoordinates]
      rfl
    · simp [L,oneKeyMatrix,oneEndpointInjection,oneEndpointCoordinates,oneNominalCoordinates,
        Pi.single_eq_of_ne ha]
      rfl
  apply le_antisymm _ bot_le
  rintro u ⟨z,⟨c,rfl⟩,rfl⟩
  rw [Submodule.mem_bot]
  change L (oneKeyMatrix v t e*ᵥc)=0
  rw [Matrix.mulVec_eq_sum]
  simp_rw [op_smul_eq_smul]
  change L (∑ a,c a • ((oneKeyMatrix v t e).col a))=0
  rw [map_sum]
  simp only [map_smul,hcol,smul_zero,Finset.sum_const_zero]

theorem one_frozen_channel_pins (v : Volley p n I) (t : Tagging p I)
    (P : ImagePlan (Comp p.g) (OneColumn p n)) :
    oneChannelPins (P⊔oneKeyPlan v t)=oneChannelPins P := by
  funext i e
  change (P e⊔oneKeyPlan v t e).map _=_
  rw [Submodule.map_sup]
  change oneChannelPins P i e⊔oneChannelPins (oneKeyPlan v t) i e=_
  rw [one_key_channel_pins,sup_bot_eq]

end
end Lax793645Proofs.Simplifications
