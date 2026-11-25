import Lax793645Proofs.Simplifications.QuadraticFrameLowerBound
import Lax793645Proofs.Simplifications.QuadraticMomentMaps

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Quadratic Gram information is the diagonal evaluation of a matrix.
Using its image avoids redundant ordered Gram equations. -/
def matrixQuadraticRead : Mat I I→ₗ[F](Vec I→F) where
  toFun M v:=evmat M v v
  map_add' M L:=by funext v; exact evmat_addM M L v v
  map_smul' c M:=by funext v; simp [evmat,Matrix.smul_mulVec,dotProduct_smul]

abbrev QuadraticGramCode (I : Type) [Fintype I] [DecidableEq I] :=
  LinearMap.range (matrixQuadraticRead (I:=I))

def quadraticGramCode : Mat I I→ₗ[F]QuadraticGramCode I:=matrixQuadraticRead.rangeRestrict

theorem quadratic_gram_code_surjective : Surjective (quadraticGramCode (I:=I)) := by
  rintro ⟨x,M,rfl⟩
  exact ⟨M,rfl⟩

theorem quadratic_gram_code_eq (M L : Mat I I) :
    quadraticGramCode M=quadraticGramCode L ↔M.toQuadraticForm'=L.toQuadraticForm' := by
  constructor
  · intro h
    apply QuadraticMap.ext
    intro v
    change M.toBilin' v v=L.toBilin' v v
    rw [Matrix.toBilin'_apply',Matrix.toBilin'_apply']
    exact congrFun (congrArg Subtype.val h) v
  · intro h
    apply Subtype.ext
    funext v
    have hh:=DFunLike.congr_fun h v
    change M.toBilin' v v=L.toBilin' v v at hh
    change evmat M v v=evmat L v v
    simpa only [Matrix.toBilin'_apply',evmat] using hh

/-- The quadratic Gram code of a uniformly random ordered matrix is
exactly uniform, including in characteristic two. -/
theorem quadratic_gram_code_uniform :
    mapW (unif : Wgt (Mat I I)) quadraticGramCode=unif :=
  map_unif_surjective quadraticGramCode quadratic_gram_code_surjective

/-- The number of independent quadratic equations is at most the
number of ordered matrix entries. -/
theorem quadratic_gram_code_dimension : dim (QuadraticGramCode I)≤Fintype.card I*Fintype.card I :=
  (LinearMap.finrank_range_le _).trans_eq (dim_mat I I)

/-- Read the prescribed quadratic Gram data from an arbitrary image
matrix. This does not assume the columns are independent. -/
def quadraticImageCode {N : ℕ} (P : Mat (HyperbolicIdx N) I) : QuadraticGramCode I:=
  quadraticGramCode (Pᵀ*hyperbolicMatrix N*P)

theorem quadratic_image_code_value {N : ℕ} (P : Mat (HyperbolicIdx N) I) (v : Vec I) :
    (quadraticImageCode P).val v=(hyperbolicMatrix N).toQuadraticForm' (P*ᵥv) := by
  change evmat (Pᵀ*hyperbolicMatrix N*P) v v=(hyperbolicMatrix N).toBilin' (P*ᵥv) (P*ᵥv)
  rw [Matrix.toBilin'_apply']
  change evmat (Pᵀ*hyperbolicMatrix N*P) v v=evmat (hyperbolicMatrix N) (P*ᵥv) (P*ᵥv)
  rw [evmat,evmat,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

theorem quadratic_stack_code {N : ℕ} (P : Mat (Fin N) I×Mat (Fin N) I) :
    quadraticImageCode (stackMatrixEquiv N P)=quadraticGramCode (P.1ᵀ*P.2) := by
  apply Subtype.ext
  funext v
  rw [quadratic_image_code_value,hyperbolic_matrix_apply]
  change hyperbolicQuadratic N (hyperbolicCoordinates N ((Matrix.fromRows P.1 P.2)*ᵥv))=
    evmat (P.1ᵀ*P.2) v v
  rw [Matrix.fromRows_mulVec,hyperbolic_apply]
  change dotProduct (P.1*ᵥv) (P.2*ᵥv)=evmat (P.1ᵀ*P.2) v v
  rw [evmat,←Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

end
end Lax793645Proofs.Simplifications
