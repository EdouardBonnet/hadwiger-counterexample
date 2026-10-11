import Lax342547.CommonExactification
import Lax342547.PointQuadratics
import Lax342547.BooleanWeight

/-!
---
title: Common predictions from actual point tensors
type: definition and theorem
---
Degree-two actual point-tensor evaluations yield an exact common marked prediction after an explicitly bounded mass loss.
-/

namespace Lax342547.PointPrediction

open Lax342547.MomentSpace Lax342547.SelectorInterpolation Lax342547.RetainedImages
open Lax342547.RelativeEntropy
open scoped BigOperators

axiom marked_point_degree {b : ℕ} {Label Coord : Type} [Fintype Coord]
    (p : Label → Coord → Binary) (s : Label)
    (φ : Module.Dual Binary (Matrix (Coord × Option (Fin b)) (Coord × Option (Fin b)) Binary))
    (α : Binary) (q : (Fin b → Binary) → Binary) (hq : q ∈ selectorSpan b 2) :
    (fun x => φ (pointMoment p s x)+α*q x) ∈ selectorSpan b 2

axiom retained_point_prediction {U Label Coord : Type} [Fintype U] [Fintype Coord] {b : ℕ}
    (β : U → ℝ) (f : (Fin b → Binary) → Binary) (p : Label → Coord → Binary) (s : Label)
    (φ : U → Module.Dual Binary (Matrix (Coord × Option (Fin b)) (Coord × Option (Fin b)) Binary))
    (α : U → Binary) (q : (Fin b → Binary) → Binary) (ε : ℝ)
    (hβ : Probability β) (hq : q ∈ selectorSpan b 2) (hε : ε < 1/16)
    (herror : (∑ u, β u*cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b)
      (fun x => φ u (pointMoment p s x)+α u*q x ≠ f x)) ≤ ε) :
    ∃ u₀ : U, 1-16*ε ≤ cellMass β (fun u =>
      (fun x => φ u (pointMoment p s x)+α u*q x) =
      (fun x => φ u₀ (pointMoment p s x)+α u₀*q x))

end Lax342547.PointPrediction
