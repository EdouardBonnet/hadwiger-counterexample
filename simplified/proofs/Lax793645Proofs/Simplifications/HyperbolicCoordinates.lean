import Lax793645Proofs.Simplifications.HyperbolicExtension
import Mathlib.Data.Matrix.Block

namespace Lax793645Proofs.Simplifications
open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev HyperbolicIdx (h : ℕ) := Fin h⊕Fin h

/-- An ordered matrix representative: its symmetric part is the polar
form, whereas the matrix itself retains the quadratic values. -/
def hyperbolicMatrix (h : ℕ) : Matrix (HyperbolicIdx h) (HyperbolicIdx h) QField :=
  Matrix.fromBlocks 0 1 0 0

def hyperbolicCoordinates (h : ℕ) :
    (HyperbolicIdx h→QField)≃ₗ[QField]Hyperbolic h :=
  LinearEquiv.sumArrowLequivProdArrow _ _ _ _

theorem hyperbolic_matrix_apply (h : ℕ) (v : HyperbolicIdx h→QField) :
    (hyperbolicMatrix h).toQuadraticForm' v=
      hyperbolicQuadratic h (hyperbolicCoordinates h v) := by
  change Matrix.toBilin' (hyperbolicMatrix h) v v=_
  rw [Matrix.toBilin'_apply',hyperbolic_apply]
  change dotProduct v (hyperbolicMatrix h*ᵥv)=dotProduct (v∘Sum.inl) (v∘Sum.inr)
  simp only [hyperbolicMatrix,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,
    Matrix.one_mulVec,zero_add,add_zero]
  rw [show v=Sum.elim (v∘Sum.inl) (v∘Sum.inr) from by ext i; cases i <;> rfl]
  simp only [sumElim_dotProduct_sumElim,dotProduct_zero,add_zero]
  rfl

theorem hyperbolic_matrix_polar (h : ℕ) (v w : HyperbolicIdx h→QField) :
    (hyperbolicMatrix h).toQuadraticForm'.polarBilin v w=
      (hyperbolicQuadratic h).polarBilin
        (hyperbolicCoordinates h v) (hyperbolicCoordinates h w) := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    hyperbolic_matrix_apply,map_add]

theorem hyperbolic_matrix_nondegenerate (h : ℕ) :
    (hyperbolicMatrix h).toQuadraticForm'.polarBilin.Nondegenerate := by
  constructor
  · intro v hv
    apply (hyperbolicCoordinates h).injective
    rw [map_zero]
    apply (hyperbolic_nondegenerate h).1
    intro w
    obtain ⟨x,rfl⟩:=(hyperbolicCoordinates h).surjective w
    rw [←hyperbolic_matrix_polar]
    exact hv x
  · intro v hv
    apply (hyperbolicCoordinates h).injective
    rw [map_zero]
    apply (hyperbolic_nondegenerate h).2
    intro w
    obtain ⟨x,rfl⟩:=(hyperbolicCoordinates h).surjective w
    rw [←hyperbolic_matrix_polar]
    exact hv x

end
end Lax793645Proofs.Simplifications
