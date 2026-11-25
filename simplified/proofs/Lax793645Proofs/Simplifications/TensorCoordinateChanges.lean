import Lax793645Proofs.Simplifications.AffineTensorMoments
import Lax793645Proofs.Simplifications.AdaptedTensorBases
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module LinearMap
open scoped BigOperators Kronecker
noncomputable section

variable {S T S' T' : Type} [Fintype S] [Fintype T] [Fintype S'] [Fintype T']

theorem tensor_map_ray (A : Mat S' S) (B : Mat T' T) (s : Vec S) (t : Vec T) :
    (A ⊗ₖ B) *ᵥ tensorRay s t=tensorRay (A *ᵥ s) (B *ᵥ t) := by
  funext x
  simp only [Matrix.mulVec,dotProduct,tensorRay,Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem affineTensor_change (A : Mat S' S) (B : Mat T' T)
    (εS : Vec S) (εT : Vec T) (εS' : Vec S') (εT' : Vec T')
    (hS : Aᵀ *ᵥ εS'=εS) (hT : Bᵀ *ᵥ εT'=εT)
    {w : Mat (S × T) (S × T)} (hw : w ∈ affineTensorSpace εS εT) :
    liftM (A ⊗ₖ B) (A ⊗ₖ B) w ∈ affineTensorSpace εS' εT' := by
  have hle : affineTensorSpace εS εT ≤
      (affineTensorSpace εS' εT').comap (liftM (A ⊗ₖ B) (A ⊗ₖ B)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s,t,hs,ht,rfl⟩
    change liftM _ _ _ ∈ affineTensorSpace εS' εT'
    rw [liftM_outer,tensor_map_ray]
    apply Submodule.subset_span
    refine ⟨A *ᵥ s,B *ᵥ t,?_,?_,rfl⟩
    · rw [← dotProduct_transpose_mulVec,hS,dotProduct_comm]
      exact hs
    · rw [← dotProduct_transpose_mulVec,hT,dotProduct_comm]
      exact ht
  exact hle hw

def basisColumns (B : Basis S' F (Vec S)) : Mat S S' := fun a i => B i a

def basisCoordinates (B : Basis S' F (Vec S)) : Mat S' S := by
  classical
  exact LinearMap.toMatrix' B.equivFun.toLinearMap

theorem basisColumns_mulVec (B : Basis S' F (Vec S)) (v : Vec S') :
    basisColumns B *ᵥ v=B.equivFun.symm v := by
  rw [B.equivFun_symm_apply,Matrix.mulVec_eq_sum]
  simp only [op_smul_eq_smul]
  rfl

theorem basisCoordinates_mulVec (B : Basis S' F (Vec S)) (v : Vec S) :
    basisCoordinates B *ᵥ v=B.equivFun v := by
  classical
  exact LinearMap.congr_fun (toMat_map B.equivFun.toLinearMap) v

theorem basisCoordinates_columns [DecidableEq S'] (B : Basis S' F (Vec S)) :
    basisCoordinates B*basisColumns B=1 := by
  classical
  apply coe_mv_inj
  apply LinearMap.ext
  intro x
  change (basisCoordinates B*basisColumns B)*ᵥ x=(1 : Mat S' S')*ᵥ x
  rw [←Matrix.mulVec_mulVec,basisColumns_mulVec,basisCoordinates_mulVec,
    B.equivFun.apply_symm_apply,Matrix.one_mulVec]

theorem basisColumns_coordinates [DecidableEq S] (B : Basis S' F (Vec S)) :
    basisColumns B*basisCoordinates B=1 := by
  classical
  apply coe_mv_inj
  apply LinearMap.ext
  intro x
  change (basisColumns B*basisCoordinates B)*ᵥ x=(1 : Mat S S)*ᵥ x
  rw [←Matrix.mulVec_mulVec,basisCoordinates_mulVec,basisColumns_mulVec,
    B.equivFun.symm_apply_apply,Matrix.one_mulVec]

/-- Moment identities transform with the constant-coordinate functionals.
They therefore hold in bases adapted to protected spaces and witness points. -/
theorem affineTensor_basis_change (B : Basis S' F (Vec S)) (C : Basis T' F (Vec T))
    (εS : Vec S) (εT : Vec T) {w : Mat (S × T) (S × T)}
    (hw : w ∈ affineTensorSpace εS εT) :
    liftM (basisCoordinates B ⊗ₖ basisCoordinates C)
      (basisCoordinates B ⊗ₖ basisCoordinates C) w ∈
    affineTensorSpace ((basisColumns B)ᵀ *ᵥ εS) ((basisColumns C)ᵀ *ᵥ εT) := by
  classical
  apply affineTensor_change _ _ εS εT _ _ _ _ hw
  · rw [Matrix.mulVec_mulVec,←Matrix.transpose_mul,basisColumns_coordinates,
      Matrix.transpose_one,Matrix.one_mulVec]
  · rw [Matrix.mulVec_mulVec,←Matrix.transpose_mul,basisColumns_coordinates,
      Matrix.transpose_one,Matrix.one_mulVec]

end
end Lax793645Proofs.Simplifications
