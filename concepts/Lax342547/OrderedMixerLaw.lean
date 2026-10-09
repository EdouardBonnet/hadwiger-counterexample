import Lax342547.AtomDirections
import Lax342547.FiniteLinearLaw

/-!
---
title: Independent ordered mixer blocks at distinct labels
type: definition and theorem
---
Two direction spaces with independent combined columns can receive any
prescribed forward and reverse bilinear blocks. A uniform ambient matrix
therefore induces a uniform pair of blocks; any nonzero ordered parity
is itself uniform. This applies to the free Z directions of distinct
selector labels in Lemma 5.5.
-/

namespace Lax342547.OrderedMixerLaw

variable {K I N P : Type} [Field K] [Fintype I]

def orders (D : Matrix I N K) (E : Matrix I P K) :
    Matrix I I K →ₗ[K] (Matrix N P K × Matrix P N K) where
  toFun L := (D.transpose * L * E, E.transpose * L * D)
  map_add' L M := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a L := by simp [Matrix.mul_smul, Matrix.smul_mul]

def parity (a b : K) : (Matrix N P K × Matrix P N K) →ₗ[K] Matrix N P K where
  toFun x := a • x.1 + b • x.2.transpose
  map_add' x y := by simp [smul_add, add_add_add_comm]
  map_smul' c x := by simp [smul_add, smul_smul, mul_comm]

axiom orders_surjective [Fintype N] [Fintype P]
    (D : Matrix I N K) (E : Matrix I P K)
    (hDE : Function.Injective (Matrix.fromCols D E).mulVec) :
    Function.Surjective (orders D E)

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.AtomDirections

axiom orders_uniform {I N P : Type} [Fintype I] [Fintype N] [Fintype P]
    [DecidableEq I] [DecidableEq N] [DecidableEq P]
    (D : Matrix I N Binary) (E : Matrix I P Binary)
    (hDE : Function.Injective (Matrix.fromCols D E).mulVec) :
    (PMF.uniformOfFintype (Matrix I I Binary)).map (orders D E) =
      PMF.uniformOfFintype (Matrix N P Binary × Matrix P N Binary)

axiom ordered_parity_uniform {I N P : Type} [Fintype I] [Fintype N] [Fintype P]
    [DecidableEq I] [DecidableEq N] [DecidableEq P]
    (D : Matrix I N Binary) (E : Matrix I P Binary)
    (hDE : Function.Injective (Matrix.fromCols D E).mulVec)
    (a b : Binary) (hab : a ≠ 0 ∨ b ≠ 0) :
    (PMF.uniformOfFintype (Matrix I I Binary)).map ((parity a b).comp (orders D E)) =
      PMF.uniformOfFintype (Matrix N P Binary)

axiom atom_orders_uniform {k n b degree : ℕ} (hd : 1 ≤ degree)
    (s t : Fin b → Binary) (hst : s ≠ t) :
    (PMF.uniformOfFintype (Moment k n b degree)).map
      (orders (blockDirections s free) (blockDirections t free)) =
      PMF.uniformOfFintype (Matrix (Fin n) (Fin n) Binary × Matrix (Fin n) (Fin n) Binary)

end Lax342547.OrderedMixerLaw
