import Lax793645Proofs.Simplifications.TensorAtomIsolation

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module LinearMap
open scoped BigOperators
noncomputable section

variable {X I : Type} [Fintype X] [Fintype I] [DecidableEq X]

def matrixRead (E : Vec X →ₗ[F] Vec I) (i : I) : Mat X X →ₗ[F] F := by
  classical
  exact LinearMap.proj i ∘ₗ LinearMap.proj i ∘ₗ
    liftM (LinearMap.toMatrix' E) (LinearMap.toMatrix' E)

theorem matrixRead_outer (E : Vec X →ₗ[F] Vec I) (i : I) (v : Vec X) :
    matrixRead E i (vecMulVec v v)=(E v i)*(E v i) := by
  classical
  change (liftM (LinearMap.toMatrix' E) (LinearMap.toMatrix' E) (vecMulVec v v)) i i=_
  rw [liftM_outer]
  have he : (LinearMap.toMatrix' E)*ᵥ v=E v := LinearMap.congr_fun (toMat_map E) v
  rw [he]
  rfl

theorem matrixRead_zero (E : Vec X →ₗ[F] Vec I) (i : I) (L : Space (Vec X))
    (hE : L ≤ E.ker) (M : Mat X X) (hM : colSp M ≤ L) : matrixRead E i M=0 := by
  classical
  have he : (LinearMap.toMatrix' E)*M=0 := by
    apply coe_mv_inj
    change ((LinearMap.toMatrix' E)*M).mulVecLin=(0 : Mat I X).mulVecLin
    rw [Matrix.mulVecLin_mul,toMat_map,Matrix.mulVecLin_zero]
    apply LinearMap.ext
    intro v
    exact hE (hM ⟨v,rfl⟩)
  change (liftM (LinearMap.toMatrix' E) (LinearMap.toMatrix' E) M) i i=0
  rw [liftM_def,he,Matrix.zero_mul]
  rfl

theorem matrixRead_eval (E : Vec X →ₗ[F] Vec I) (i : I) (M : Mat X X) :
    matrixRead E i M=evmat M ((LinearMap.toMatrix' E).row i) ((LinearMap.toMatrix' E).row i) := by
  classical
  change (liftM (LinearMap.toMatrix' E) (LinearMap.toMatrix' E) M) i i = _
  exact liftM_coordinate (LinearMap.toMatrix' E) M i i

end
end Lax793645Proofs.Simplifications
