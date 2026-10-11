import Lax342547.QuadraticDegree
import Lax342547.BaseMoments

/-!
---
title: Boolean degree of actual point-tensor evaluations
type: definition and theorem
---
The actual base evaluations and pointMoment tensor map have Boolean degree at most two after composition with any linear functional.
-/

namespace Lax342547.PointQuadratics

open Lax342547.MomentSpace Lax342547.SelectorInterpolation

axiom base_evaluation_degree {b : ℕ} (i : Option (Fin b)) :
    (fun x : Fin b → Binary => baseEval x i) ∈ selectorSpan b 1

axiom point_tensor_evaluation_degree {b : ℕ} {Label Coord : Type} [Fintype Coord]
    (p : Label → Coord → Binary) (s : Label)
    (φ : Module.Dual Binary (Matrix (Coord × Option (Fin b)) (Coord × Option (Fin b)) Binary)) :
    (fun x : Fin b → Binary => φ (pointMoment p s x)) ∈ selectorSpan b 2

end Lax342547.PointQuadratics
