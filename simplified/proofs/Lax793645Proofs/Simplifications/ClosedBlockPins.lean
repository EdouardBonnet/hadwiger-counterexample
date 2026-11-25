import Lax793645Proofs.Simplifications.ClosedPinStep
import Mathlib.LinearAlgebra.Pi

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Submodule Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem linear_image_dimension_growth {V W : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F V]
    (f : V→ₗ[F]W) (S T : Space V) (hST : S≤T) :
    dim (T.map f)-dim (S.map f)≤dim T-dim S := by
  let fS:=f.comp S.subtype
  let fT:=f.comp T.subtype
  let g : fS.ker→ₗ[F]fT.ker:=
    ((Submodule.inclusion hST).comp fS.ker.subtype).codRestrict fT.ker (fun x=>x.property)
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : fT.ker=>(z.val:V)) h
  have hk:=LinearMap.finrank_le_finrank_of_injective hg
  have hs:=fS.finrank_range_add_finrank_ker
  have ht:=fT.finrank_range_add_finrank_ker
  have hrS : fS.range=S.map f := by rw [LinearMap.range_comp,Submodule.range_subtype]
  have hrT : fT.range=T.map f := by rw [LinearMap.range_comp,Submodule.range_subtype]
  rw [hrS] at hs
  rw [hrT] at ht
  have hm:=Submodule.finrank_mono hST
  change dim fS.ker≤dim fT.ker at hk
  change dim (S.map f)+dim fS.ker=dim S at hs
  change dim (T.map f)+dim fT.ker=dim T at ht
  omega

variable {I : Type} [Fintype I] {V : I→Type}
  [∀ i,AddCommGroup (V i)] [∀ i,Module F (V i)]

/-- Close a pin space under the coordinate block projections. -/
def blockClosure (S : Space (∀ i,V i)) : Space (∀ i,V i) :=
  Submodule.pi Set.univ (fun i=>S.map (LinearMap.proj i))

omit [Fintype I] in
theorem le_blockClosure (S : Space (∀ i,V i)) : S≤blockClosure S := by
  intro x hx
  exact Submodule.mem_pi.mpr (fun i _=>⟨x,hx,rfl⟩)

omit [Fintype I] in
theorem blockClosure_projection (S : Space (∀ i,V i)) (i : I) :
    (blockClosure S).map (LinearMap.proj i)=S.map (LinearMap.proj i) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact (Submodule.mem_pi.mp hx) i (Set.mem_univ i)
  · exact Submodule.map_mono (le_blockClosure S)

omit [Fintype I] in
theorem blockClosure_idempotent (S : Space (∀ i,V i)) :
    blockClosure (blockClosure S)=blockClosure S := by
  unfold blockClosure
  congr 1
  funext i
  exact blockClosure_projection S i

def blockClosureEquiv (S : Space (∀ i,V i)) :
    blockClosure S≃ₗ[F](∀ i,S.map (LinearMap.proj i)) where
  toFun x i:=⟨x.val i,(Submodule.mem_pi.mp x.property) i (Set.mem_univ i)⟩
  invFun x:=⟨fun i=>(x i).val,Submodule.mem_pi.mpr (fun i _=>(x i).property)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

variable [∀ i,FiniteDimensional F (V i)]

theorem blockClosure_dimension (S : Space (∀ i,V i)) :
    dim (blockClosure S)=∑ i,dim (S.map (LinearMap.proj i)) := by
  unfold dim
  rw [(blockClosureEquiv S).finrank_eq]
  exact Module.finrank_pi_fintype F

theorem blockClosure_dimension_bound (S : Space (∀ i,V i)) :
    dim (blockClosure S)≤Fintype.card I*dim S := by
  rw [blockClosure_dimension]
  calc
    _ ≤ ∑ _ : I,dim S:=Finset.sum_le_sum (fun i _=>Submodule.finrank_map_le _ _)
    _ = _:=by simp

/-- Closing a new t-dimensional extension of an already closed pin space
adds at most one copy of t for each coordinate block. -/
theorem blockClosure_dimension_step (S T : Space (∀ i,V i)) (hST : S≤T)
    (hS : blockClosure S=S) :
    dim (blockClosure T)-dim S≤Fintype.card I*(dim T-dim S) := by
  have h (i : I) : dim (T.map (LinearMap.proj i))≤
      dim (S.map (LinearMap.proj i))+(dim T-dim S) := by
    have hi:=linear_image_dimension_growth (LinearMap.proj i) S T hST
    omega
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>h i)
  rw [Finset.sum_add_distrib,←blockClosure_dimension,←blockClosure_dimension,hS] at hh
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
  omega

end
end Lax793645Proofs.Simplifications
