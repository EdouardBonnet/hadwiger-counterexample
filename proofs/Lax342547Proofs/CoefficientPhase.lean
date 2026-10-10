import Lax342547.CoefficientPhase
import Lax342547Proofs.TargetMatrices
import Lax342547Proofs.GramTests

namespace Lax342547Proofs.CoefficientPhase
open Lax342547.CoefficientPhase

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Walsh

/--
---
conclusion: Lax342547.CoefficientPhase.coefficient_trace
---
-/
theorem coefficient_trace {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    (C : Matrix I J Binary) (X : Matrix N I Binary) (Y : Matrix N J Binary) :
    coefficientPair C X Y = Matrix.trace (C.transpose * (X.transpose * Y)) := by
  unfold coefficientPair Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

/--
---
conclusion: Lax342547.CoefficientPhase.independent_factor_phase
---
-/
theorem independent_factor_phase {I J R N : Type}
    [Fintype I] [Fintype J] [Fintype R] [Fintype N]
    (A : Matrix I R Binary) (B : Matrix J R Binary) (X : Matrix N I Binary) (Y : Matrix N J Binary) :
    coefficientPair (A * B.transpose) X Y = dotProduct (factorImage A X) (factorImage B Y) := by
  classical
  rw [coefficient_trace, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm B, ← Matrix.mul_assoc,
    ← Matrix.transpose_mul]
  rw [Matrix.mul_assoc]
  unfold Matrix.trace dotProduct factorImage
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type]

end Lax342547Proofs.CoefficientPhase
