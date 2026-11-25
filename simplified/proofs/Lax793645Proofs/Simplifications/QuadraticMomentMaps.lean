import Lax793645Proofs.Simplifications.QuadraticChannelFrames
import Lax793645Proofs.Simplifications.QuadraticKernelIntersection
import Mathlib.LinearAlgebra.Matrix.BilinearForm

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A J : Type} [Fintype I] [Fintype A] [Fintype J]

/-- A single primal map acts on both factors of a moment. -/
def quadraticMomentMap (P : Vec I→ₗ[F]Vec A) : Mat I I→ₗ[F]Mat A A := by
  classical
  exact liftM (LinearMap.toMatrix' P) (LinearMap.toMatrix' P)

omit [Fintype A] in
theorem quadratic_moment_outer (P : Vec I→ₗ[F]Vec A) (v w : Vec I) :
    quadraticMomentMap P (vecMulVec v w)=vecMulVec (P v) (P w) := by
  classical
  simp only [quadraticMomentMap,liftM_outer,LinearMap.toMatrix'_mulVec]

theorem quadratic_moment_injective (P : Vec I→ₗ[F]Vec A)
    (hP : Function.Injective P) : Function.Injective (quadraticMomentMap P) := by
  classical
  have hi : Function.Injective (LinearMap.toMatrix' P).mulVec := by
    intro x y he
    exact hP (by simpa only [LinearMap.toMatrix'_mulVec] using he)
  exact liftM_inj hi hi

theorem matrix_quadratic_outer [DecidableEq A] (E : Mat A A) (v : Vec A) :
    mpair E (vecMulVec v v)=E.toQuadraticForm' v := by
  classical
  rw [mpair_outer]
  exact (Matrix.toBilin'_apply' E v v).symm

/-- An isometry preserves the quadratic readout on the entire square span,
not just on individual point moments. No division by two is used. -/
theorem quadratic_moment_invariant [DecidableEq A] [DecidableEq I]
    (P : Vec I→ₗ[F]Vec A)
    (E : Mat A A) (M : Mat I I)
    (hP : E.toQuadraticForm'.comp P=M.toQuadraticForm')
    {W : Mat I I} (hW : W∈quadraticSquares (⊤ : Space (Vec I))) :
    mpair E (quadraticMomentMap P W)=mpair M W := by
  classical
  induction hW using Submodule.span_induction with
  | mem W h =>
    obtain ⟨v,_,rfl⟩:=h
    rw [quadratic_moment_outer,matrix_quadratic_outer,matrix_quadratic_outer]
    exact congrArg (fun Q : QuadraticForm F (Vec I)=>Q v) hP
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add,hx,hy]
  | smul c x _ hx => simp only [map_smul,hx]

/-- The ordered product of two polar channel evaluations. Its matrix is
used only as a representative of a quadratic functional. -/
def quadraticChannelBilin (q : QuadraticForm F (Vec A))
    (X Y : J→Vec A) : LinearMap.BilinForm F (Vec A) :=
  ∑ j,(q.polarBilin (X j)).smulRight (q.polarBilin (Y j))

def quadraticChannelFunctional (q : QuadraticForm F (Vec A))
    (X Y : J→Vec A) : Mat A A→ₗ[F]F := by
  classical
  exact mpair (quadraticChannelBilin q X Y).toMatrix'

theorem quadratic_channel_functional_outer (q : QuadraticForm F (Vec A))
    (X Y : J→Vec A) (v w : Vec A) :
    quadraticChannelFunctional q X Y (vecMulVec v w)=
      ∑ j,q.polarBilin (X j) v*q.polarBilin (Y j) w := by
  classical
  rw [quadraticChannelFunctional,mpair_outer,evmat]
  rw [←Matrix.toBilin'_apply',Matrix.toBilin'_toMatrix']
  simp [quadraticChannelBilin]

/-- Own X-channels annihilate every lifted matrix. This is stronger than
vanishing merely on the point-moment span. -/
theorem quadratic_channel_self (q : QuadraticForm F (Vec A))
    (X Y : J→Vec A) (P : Vec I→ₗ[F]Vec A)
    (hX : ∀ j v,q.polarBilin (X j) (P v)=0) (W : Mat I I) :
    quadraticChannelFunctional q X Y (quadraticMomentMap P W)=0 := by
  classical
  have hB : (quadraticChannelBilin q X Y).comp P P=0 := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change (quadraticChannelBilin q X Y) (P v) (P w)=0
    simp only [quadraticChannelBilin,LinearMap.sum_apply,LinearMap.smulRight_apply,
      hX,zero_smul,Finset.sum_const_zero,LinearMap.zero_apply]
  have hM := congrArg LinearMap.BilinForm.toMatrix' hB
  rw [LinearMap.BilinForm.toMatrix'_comp,map_zero] at hM
  unfold quadraticChannelFunctional quadraticMomentMap
  rw [mpair_liftM,liftM_def,transpose_transpose,hM,mpair_comm,map_zero]

end
end Lax793645Proofs.Simplifications
