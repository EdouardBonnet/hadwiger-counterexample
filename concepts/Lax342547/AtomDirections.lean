import Lax342547.ConcreteGeometry
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
---
title: Independent free-direction spaces at distinct selector labels
type: definition and theorem
---
The linear variation of a point input when a single base block varies.
For distinct labels the two direction spaces are independent, because
the empty selector and a separating singleton selector recover both
sets of input coefficients. This is the geometric input to the ordered
binary mixer tests in Lemma 5.5.
-/

namespace Lax342547.AtomDirections

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry

noncomputable def blockDirections {k n b degree : ℕ} (s : Fin b → Binary)
    (c : Fin n → Base k n) : Matrix (Coordinate k n b degree) (Fin n) Binary := by
  classical
  exact fun i j => if i.2 = some (c j) then selectorEval s i.1 else 0

noncomputable def varyBlock {k n : ℕ} (z : Base k n → Binary) (c : Fin n → Base k n)
    (v : Fin n → Binary) : Base k n → Binary := by
  classical
  exact fun i => z i + ∑ j, if c j = i then v j else 0

axiom point_varyBlock {k n b degree : ℕ} (s : Fin b → Binary) (z : Base k n → Binary)
    (c : Fin n → Base k n) (v : Fin n → Binary) :
    point (selectorEval (degree := degree)) s (varyBlock z c v) =
      point selectorEval s z + (blockDirections s c).mulVec v

axiom blockDirections_injective {k n b degree : ℕ} (s : Fin b → Binary)
    (c : Fin n → Base k n) (hc : Function.Injective c) :
    Function.Injective (blockDirections (degree := degree) s c).mulVec

axiom distinct_directions_injective {k n b degree : ℕ} (hd : 1 ≤ degree)
    (s t : Fin b → Binary) (hst : s ≠ t) (c : Fin n → Base k n) (hc : Function.Injective c) :
    Function.Injective (Matrix.fromCols (blockDirections (degree := degree) s c)
      (blockDirections t c)).mulVec

end Lax342547.AtomDirections
