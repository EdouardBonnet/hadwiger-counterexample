import Lax793645Proofs.Simplifications.WeightedFourCorners

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
  [DecidableEq I] [DecidableEq J] [DecidableEq U]

/-- Coordinate identification, retaining every original matrix column. -/
def matrixCoordinates (U I : Type) : Vec (U×I)≃ₗ[F] Mat U I where
  toFun x u i := x (u,i)
  invFun X v := X v.1 v.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fourier_norm_point (f : Wgt (Vec I)) (x : Vec I) :
    |f x|≤fourierNorm f := by
  rw [←hat_eqn f x]
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
  simp only [abs_mul,vectorPhase,wsign_abs,mul_one]
  rfl

/-- Exactly one, not merely a dimension-dependent upper bound. -/
theorem fourier_norm_kernel_eq_one (A : Mat J I) :
    fourierNorm (fun x=>ind (A*ᵥx=0))=1 := by
  apply le_antisymm (fourier_norm_kernel A)
  have hh := fourier_norm_point (fun x=>ind (A*ᵥx=0)) 0
  simpa only [Matrix.mulVec_zero,ind_true,abs_one] using hh

/-- The normalized character expansion of any homogeneous linear relation
system. Redundant equations and cross-batch relations are both permitted. -/
theorem linear_relation_expansion (T : Vec I→ₗ[F] Vec J) (x : Vec I) :
    ind (T x=0)=avg unif (fun η : Vec J=>
      vectorPhase ((LinearMap.toMatrix' T)ᵀ*ᵥη) x) := by
  rw [vector_expand]
  apply avg_congr
  intro η _
  simp only [vectorPhase,dotProduct_zero,wsign_zero,mul_one]
  congr 1
  rw [Matrix.mulVec_transpose,←Matrix.dotProduct_mulVec]
  exact congrArg (dotProduct η) (LinearMap.congr_fun (toMat_map T) x).symm

theorem linear_relation_fourier_norm (T : Vec I→ₗ[F] Vec J) :
    fourierNorm (fun x=>ind (T x=0))=1 := by
  have he (x : Vec I) : (LinearMap.toMatrix' T)*ᵥx=T x :=
    LinearMap.congr_fun (toMat_map T) x
  simpa only [he] using fourier_norm_kernel_eq_one (LinearMap.toMatrix' T)

/-- The map imposing X*A=0 in the original column coordinates. -/
def columnRelationMap (A : Mat I J) : Vec (U×I)→ₗ[F] Vec (U×J) :=
  (matrixCoordinates U J).symm.toLinearMap.comp
    ((rmult U A).comp (matrixCoordinates U I).toLinearMap)

theorem column_relation_expansion (A : Mat I J) (X : Mat U I) :
    ind (X*A=0)=bp (-num U*num J)*
      ∑ η : Vec (U×J), vectorPhase
        ((LinearMap.toMatrix' (columnRelationMap (U:=U) A))ᵀ*ᵥη)
        ((matrixCoordinates U I).symm X) := by
  have he : columnRelationMap A ((matrixCoordinates U I).symm X)=0 ↔ X*A=0 := by
    change (matrixCoordinates U J).symm (X*A)=0 ↔ X*A=0
    exact LinearEquiv.map_eq_zero_iff _
  rw [←he,linear_relation_expansion]
  unfold avg
  simp only [unif_apply,card_space,dim_vec,Fintype.card_prod,Nat.cast_mul,←bp_neg]
  rw [Finset.mul_sum]
  simp only [neg_mul,num]

theorem column_relation_fourier_norm (A : Mat I J) :
    fourierNorm (fun x : Vec (U×I)=>ind ((matrixCoordinates U I x)*A=0))=1 := by
  have he (x : Vec (U×I)) : columnRelationMap A x=0 ↔ matrixCoordinates U I x*A=0 := by
    exact LinearEquiv.map_eq_zero_iff (matrixCoordinates U J).symm
  simpa only [he] using linear_relation_fourier_norm (columnRelationMap (U:=U) A)

omit [DecidableEq U] in
/-- Every character factors over the original columns, whether or not the
equations from which it arose couple all those columns. -/
theorem character_factors_columns (ξ : Vec (U×I)) (X : Mat U I) :
    vectorPhase ξ ((matrixCoordinates U I).symm X)=
      ∏ i:I,wsign (∑ u:U,ξ (u,i)*X u i) := by
  unfold vectorPhase dotProduct
  rw [Fintype.sum_prod_type,Finset.sum_comm,wsign_sum]
  rfl

/-- Inserting a cross-batch relation indicator loses none of the small
Fourier factors. Its normalization cost must be accounted for separately. -/
theorem relation_preserves_product_bound {T : Type} [Fintype T] [DecidableEq T]
    (f : T→Wgt (Vec I)) (ε : T→ℝ)
    (hf : ∀ t ξ,|linearFourier (f t) ξ|≤ε t)
    (A : Mat J (T×I)) :
    |avg unif (fun x=>(∏ t,f t (fun i=>x (t,i)))*ind (A*ᵥx=0))|≤∏ t,ε t := by
  simpa only [fourier_norm_kernel_eq_one,mul_one] using
    fourier_product_weight f ε hf (fun x=>ind (A*ᵥx=0))

end
end Lax793645Proofs.Simplifications
