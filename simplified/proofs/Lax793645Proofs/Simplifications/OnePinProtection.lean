import Lax793645Proofs.Simplifications.OneKeyPinSpaces
import Lax793645Proofs.Simplifications.AffinePinProtection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ}

/-- The actual one-frame primal pins have common protected spaces.
The selector budget does not depend on the selector dimension. -/
theorem one_plan_protection (a : ImagePlan (Comp p.g) (OneColumn p n)) (q K : ℕ)
    (hK : ∀ e,dim (a e)≤K) :
    ∃ (U : Space (Vec (SelIdx p.b p.j))) (V : Space (Vec (AIdx p.g n))),
      dim U≤q*(Fintype.card (Bool×Comp p.g)*K) ∧
      dim V≤Fintype.card (SelIdx p.b p.j)*(Fintype.card (Bool×Comp p.g)*K) ∧
      (∀ i e,oneEndpointPrimalPins a i e≤tensorCross U V) ∧
      (∀ i e x,x∈oneEndpointPrimalPins a i e→Matrix.rank (flattenMatrix.symm x)≤q→
        x∈tensorRectangle U V) := by
  classical
  let P (z : Bool×Comp p.g) : Space (Mat (SelIdx p.b p.j) (AIdx p.g n)) :=
    (oneEndpointPrimalPins a z.1 z.2).map flattenMatrix.symm.toLinearMap
  have hdim (z : Bool×Comp p.g) : dim (P z)≤K :=
    (Submodule.finrank_map_le _ _).trans
      ((one_endpoint_primal_pin_dimension a z.1 z.2).trans (hK z.2))
  have hsum : (∑ z,dim (P z))≤Fintype.card (Bool×Comp p.g)*K := by
    simpa using Finset.sum_le_sum (fun z (_ : z∈Finset.univ)=>hdim z)
  obtain ⟨U,V,hU,hV,hall,hlow⟩:=common_pin_protection P q
  refine ⟨U,V,hU.trans (Nat.mul_le_mul_left _ hsum),
    hV.trans (Nat.mul_le_mul_left _ hsum),?_,?_⟩
  · intro i e x hx
    apply (le_sup_right : tensorRectangle ⊤ V≤tensorCross U V)
    exact ⟨flattenMatrix.symm x,(box_mem ..).mpr
      ⟨le_top,hall (i,e) _ ⟨x,hx,rfl⟩⟩,flattenMatrix.apply_symm_apply x⟩
  intro i e x hx hr
  exact ⟨flattenMatrix.symm x,hlow (i,e) _ ⟨x,hx,rfl⟩ hr,flattenMatrix.apply_symm_apply x⟩

variable {I : Type} [Fintype I] [DecidableEq I]

theorem one_selected_primal_dimension (v : Volley p n I) (t : Tagging p I)
    (P : Bool→Comp p.g→Space (Ray p n)) (K : ℕ) (hK : ∀ i e,dim (P i e)≤K)
    (e : Comp p.g) : dim (oneSelectedPrimal v t P e)≤2*(K+Fintype.card I) := by
  classical
  rw [oneSelectedPrimal,joint_space_dimension]
  have hb (i : Bool) : dim (P i e⊔selectedAtComponent
      (fun a : CallsAt v i=>t a.val) (fun a=>v.sel a.val) (fun a=>v.par a.val) e :
        Space (Ray p n))≤K+Fintype.card I := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (P i e)
      (selectedAtComponent (fun a : CallsAt v i=>t a.val) (fun a=>v.sel a.val)
        (fun a=>v.par a.val) e)
    apply (Nat.le_add_right _ _ |>.trans_eq hd).trans
    apply Nat.add_le_add (hK i e)
    apply (Submodule.finrank_mono (selected_at_component_le ..)).trans
    exact (finrank_range_le_card (R:=F) _).trans (Fintype.card_subtype_le _)
  simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>hb i)

/-- Independence modulo the protected spaces is the only additional
query input condition; the rank and low-pin hypotheses are then automatic. -/
def one_protected_volley (v : Volley p n I) (t : Tagging p I)
    (a : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ) (hK : ∀ e,dim (a e)≤K)
    (U : Space (Vec (SelIdx p.b p.j))) (V : Space (Vec (AIdx p.g n)))
    (hcross : ∀ i e,oneEndpointPrimalPins a i e≤tensorCross U V)
    (hlow : ∀ i e x,x∈oneEndpointPrimalPins a i e→
      Matrix.rank (flattenMatrix.symm x)≤(4*(K+Fintype.card I))^2+Fintype.card I→
      x∈tensorRectangle U V)
    (hs : ∀ i,LinearIndependent F (U.mkQ∘fun a : CallsAt v i=>selV p.j (v.sel a.val)))
    (ht : ∀ i,LinearIndependent F (V.mkQ∘fun a : CallsAt v i=>baseV (v.par a.val))) :
    OneProtectedVolley v t (oneEndpointPrimalPins a) (4*(K+Fintype.card I)) := by
  refine ⟨fun _=>U,fun _=>V,hcross,hs,ht,?_,?_⟩
  · intro e
    have hh:=one_selected_primal_dimension v t (oneEndpointPrimalPins a) K
      (fun i e=>(one_endpoint_primal_pin_dimension a i e).trans (hK e)) e
    omega
  intro i e x hx hr
  exact hlow i e x hx (hr.trans (Nat.add_le_add_left (Fintype.card_subtype_le _) _))

end
end Lax793645Proofs.Simplifications
