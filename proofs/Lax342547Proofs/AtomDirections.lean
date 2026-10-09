import Lax342547.AtomDirections
import Lax342547Proofs.ConcreteGeometry
import Mathlib.Tactic.LinearCombination

namespace Lax342547Proofs.AtomDirections

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.AtomDirections
open Lax342547Proofs.ConcreteGeometry

variable {k n b degree : ℕ}

/--
---
conclusion: Lax342547.AtomDirections.point_varyBlock
---
At a fixed selector label, varying one base block changes the point
input by exactly the direction matrix. The constant base coordinate
does not change, so this formula keeps the affine shift explicit.
-/
theorem point_varyBlock (s : Fin b → Binary) (z : Base k n → Binary)
    (c : Fin n → Base k n) (v : Fin n → Binary) :
    point (selectorEval (degree := degree)) s (varyBlock z c v) =
      point selectorEval s z + (blockDirections s c).mulVec v := by
  classical
  ext ⟨S, i⟩
  cases i <;> simp [point, baseEval, varyBlock, blockDirections, Matrix.mulVec, dotProduct,
    mul_add, Finset.mul_sum, eq_comm, ite_mul, mul_ite]

theorem blockDirections_mulVec (s : Fin b → Binary) (c : Fin n → Base k n)
    (hc : Function.Injective c) (v : Fin n → Binary) (S : SelectorCoordinates b degree) (i : Fin n) :
    (blockDirections s c).mulVec v (S, some (c i)) = selectorEval s S * v i := by
  classical
  simp [Matrix.mulVec, dotProduct, blockDirections, hc.eq_iff]

/--
---
conclusion: Lax342547.AtomDirections.blockDirections_injective
---
The empty-selector coordinate on the chosen block recovers each input bit.
-/
theorem blockDirections_injective (s : Fin b → Binary)
    (c : Fin n → Base k n) (hc : Function.Injective c) :
    Function.Injective (blockDirections (degree := degree) s c).mulVec := by
  intro v w he
  funext i
  have h := congrFun he (emptySelector b degree, some (c i))
  simpa only [blockDirections_mulVec s c hc, eval_empty, one_mul] using h

/--
---
conclusion: Lax342547.AtomDirections.distinct_directions_injective
---
Choose a bit on which the labels differ. The empty-selector equation
gives u+v, and the singleton-selector equation gives s_a u+t_a v.
Their nonzero determinant recovers u and v coordinate by coordinate.
-/
theorem distinct_directions_injective (hd : 1 ≤ degree)
    (s t : Fin b → Binary) (hst : s ≠ t) (c : Fin n → Base k n) (hc : Function.Injective c) :
    Function.Injective (Matrix.fromCols (blockDirections (degree := degree) s c)
      (blockDirections t c)).mulVec := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, s a ≠ t a := Function.ne_iff.mp hst
  change Function.Injective (Matrix.fromCols (blockDirections (degree := degree) s c)
    (blockDirections t c)).mulVecLin
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have he (i : Fin n) : v (Sum.inl i) + v (Sum.inr i) = 0 := by
    have h := congrFun hv (emptySelector b degree, some (c i))
    simpa only [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec, Pi.add_apply,
      blockDirections_mulVec _ c hc, eval_empty, one_mul, Pi.zero_apply, Function.comp_apply] using h
  have hb (i : Fin n) : s a * v (Sum.inl i) + t a * v (Sum.inr i) = 0 := by
    have h := congrFun hv (bitSelector hd a, some (c i))
    simpa only [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec, Pi.add_apply,
      blockDirections_mulVec _ c hc, eval_bit, Pi.zero_apply, Function.comp_apply] using h
  have hl (i : Fin n) : v (Sum.inl i) = 0 := by
    have h : (s a - t a) * v (Sum.inl i) = 0 := by
      linear_combination hb i - t a * he i
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr ha)
  funext i
  cases i with
  | inl i => exact hl i
  | inr i => simpa only [hl i, zero_add, Pi.zero_apply] using he i

end Lax342547Proofs.AtomDirections
