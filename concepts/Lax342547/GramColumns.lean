import Lax342547.AffineImages

/-!
---
title: Gram-conditioned columns and their rank-failure probability
type: definition and theorem
---
At an injective plus frame, a prescribed Gram matrix has probability
exactly 2^(-pq). Its completions are independent affine columns parallel
to the plus annihilator. Their failure of injectivity costs at most
2^(p+q-N), uniformly in the prescribed Gram values.
-/

namespace Lax342547.GramColumns

open Lax342547.MomentSpace
open scoped ENNReal

variable {I J N : Type} [Fintype I] [Fintype J] [Fintype N]

def gramMap (A : Matrix N I Binary) : Matrix N J Binary →ₗ[Binary] Matrix I J Binary where
  toFun B := A.transpose * B
  map_add' B C := by simp [Matrix.mul_add]
  map_smul' c B := by simp [Matrix.mul_smul]

abbrev GramFiber (A : Matrix N I Binary) (G : Matrix I J Binary) :=
  {B : Matrix N J Binary // A.transpose * B = G}

noncomputable instance (A : Matrix N I Binary) (G : Matrix I J Binary) : Fintype (GramFiber A G) := by
  classical exact Subtype.fintype _

axiom gram_uniform [DecidableEq I] [DecidableEq J] [DecidableEq N]
    (A : Matrix N I Binary) (hA : Function.Injective A.mulVec) :
    (PMF.uniformOfFintype (Matrix N J Binary)).map (gramMap A) =
      PMF.uniformOfFintype (Matrix I J Binary)

axiom gram_probability [DecidableEq I] [DecidableEq J] [DecidableEq N]
    (A : Matrix N I Binary) (hA : Function.Injective A.mulVec) (G : Matrix I J Binary) :
    (PMF.uniformOfFintype (Matrix N J Binary)).toOuterMeasure {B | A.transpose * B = G} =
      1 / (2 : ℝ≥0∞) ^ (Fintype.card I * Fintype.card J)

axiom conditional_failure [DecidableEq I] [DecidableEq J] [DecidableEq N]
    (A : Matrix N I Binary) (hA : Function.Injective A.mulVec) (G : Matrix I J Binary)
    [Nonempty (GramFiber A G)] :
    (PMF.uniformOfFintype (GramFiber A G)).toOuterMeasure {B | ¬ Function.Injective B.val.mulVec} ≤
      (2 : ℝ≥0∞) ^ (Fintype.card I + Fintype.card J) / 2 ^ Fintype.card N

end Lax342547.GramColumns
