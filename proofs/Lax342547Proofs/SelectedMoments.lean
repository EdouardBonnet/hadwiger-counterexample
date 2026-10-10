import Lax342547.SelectedMoments
import Lax342547Proofs.BaseMoments
import Mathlib.Tactic.LinearCombination

namespace Lax342547Proofs.SelectedMoments

open Lax342547.MomentSpace Lax342547.BaseMoments Lax342547.SelectedMoments
open Matrix

variable {Base : Type} [Fintype Base] [DecidableEq Base]

theorem projection_apply (z : Base → Binary) (x : Option Base → Binary) :
    (rayProjection z).mulVecLin x = x - x none • baseEval z := by
  change (rayProjection z) *ᵥ x = _
  simp [rayProjection, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec,
    single_dotProduct]

/--
---
conclusion: Lax342547.SelectedMoments.projection_kernel
---
Subtracting the constant-coordinate multiple of the affine point has
kernel exactly its ray; the point's constant coordinate is one.
-/
theorem projection_kernel (z : Base → Binary) :
    LinearMap.ker (rayProjection z).mulVecLin =
      Submodule.span Binary {baseEval z} := by
  ext x
  rw [LinearMap.mem_ker, projection_apply, sub_eq_zero, Submodule.mem_span_singleton]
  constructor
  · intro h; exact ⟨x none, h.symm⟩
  · rintro ⟨c, rfl⟩
    simp [baseEval]

theorem projection_entries (z : Base → Binary)
    (Z : Matrix (Option Base) (Option Base) Binary) (i j : Option Base) :
    (rayProjection z * Z * (rayProjection z).transpose) i j =
      Z i j - baseEval z i * Z none j - Z i none * baseEval z j +
        baseEval z i * Z none none * baseEval z j := by
  simp only [rayProjection, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_vecMulVec, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.vecMulVec_mul,
    Matrix.mul_vecMulVec, Matrix.single_vecMul,
    Matrix.mulVec_single, one_mul, mul_one]
  simp only [op_smul_eq_smul, one_smul, Matrix.col, Matrix.row, Matrix.transpose_apply,
    Matrix.sub_apply, Matrix.vecMulVec_apply]
  ring

/--
---
conclusion: Lax342547.SelectedMoments.moment_ray
---
Expand the sandwich entrywise. On the diagonal symmetry cancels its
two mixed terms; the Boolean square and moment diagonal identity force
the constant row to be the selected affine vector times the constant
entry. Substitution in every entry leaves only its point moment.
-/
theorem moment_ray (z : Base → Binary)
    (Z : Matrix (Option Base) (Option Base) Binary) (hZ : IsBaseMoment Z)
    (h : rayProjection z * Z * (rayProjection z).transpose = 0) :
    Z = Z none none • baseMoment z := by
  have he (i j : Option Base) :
      Z i j - baseEval z i * Z none j - Z i none * baseEval z j +
        baseEval z i * Z none none * baseEval z j = 0 := by
    rw [← projection_entries, h]; rfl
  have hrow (i : Option Base) : Z none i = Z none none * baseEval z i := by
    have hd := he i i
    rw [hZ.2 i, hZ.1 i none] at hd
    ring_nf at hd
    simp only [show (2 : Binary) = 0 from rfl, mul_zero, sub_zero, pow_two,
      BaseMoments.binary_mul_self] at hd
    simpa only [mul_comm] using (eq_neg_of_add_eq_zero_left hd).trans
      (ZModModule.neg_eq_self _)
  ext i j
  have hij := he i j
  rw [hrow j, hZ.1 i none, hrow i] at hij
  change Z i j = Z none none * (baseEval z i * baseEval z j)
  linear_combination hij

end Lax342547Proofs.SelectedMoments
