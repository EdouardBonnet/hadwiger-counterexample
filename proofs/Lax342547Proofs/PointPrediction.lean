import Lax342547.PointPrediction
import Lax342547Proofs.CommonExactification
import Lax342547Proofs.PointQuadratics
import Lax342547Proofs.BooleanWeight

namespace Lax342547Proofs.PointPrediction
open Lax342547.PointPrediction

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.SelectorInterpolation Lax342547.RetainedImages
open Lax342547.RelativeEntropy
open scoped BigOperators

/--
---
conclusion: Lax342547.PointPrediction.marked_point_degree
---
-/
theorem marked_point_degree {b : ℕ} {Label Coord : Type} [Fintype Coord]
    (p : Label → Coord → Binary) (s : Label)
    (φ : Module.Dual Binary (Matrix (Coord × Option (Fin b)) (Coord × Option (Fin b)) Binary))
    (α : Binary) (q : (Fin b → Binary) → Binary) (hq : q ∈ selectorSpan b 2) :
    (fun x => φ (pointMoment p s x)+α*q x) ∈ selectorSpan b 2 := by
  have hp := Lax342547Proofs.PointQuadratics.point_tensor_evaluation_degree p s φ
  have hα := (selectorSpan b 2).smul_mem α hq
  have hs := (selectorSpan b 2).add_mem hp hα
  exact hs

/--
---
conclusion: Lax342547.PointPrediction.retained_point_prediction
---
-/
theorem retained_point_prediction {U Label Coord : Type} [Fintype U] [Fintype Coord] {b : ℕ}
    (β : U → ℝ) (f : (Fin b → Binary) → Binary) (p : Label → Coord → Binary) (s : Label)
    (φ : U → Module.Dual Binary (Matrix (Coord × Option (Fin b)) (Coord × Option (Fin b)) Binary))
    (α : U → Binary) (q : (Fin b → Binary) → Binary) (ε : ℝ)
    (hβ : Probability β) (hq : q ∈ selectorSpan b 2) (hε : ε < 1/16)
    (herror : (∑ u, β u*cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b)
      (fun x => φ u (pointMoment p s x)+α u*q x ≠ f x)) ≤ ε) :
    ∃ u₀ : U, 1-16*ε ≤ cellMass β (fun u =>
      (fun x => φ u (pointMoment p s x)+α u*q x) =
      (fun x => φ u₀ (pointMoment p s x)+α u₀*q x)) := by
  have hh := Lax342547Proofs.CommonExactification.retained_common_prediction β f
    (fun u x => φ u (pointMoment p s x)+α u*q x) ε (1/16) hβ
    (fun u => marked_point_degree p s (φ u) (α u) q hq) (by norm_num) hε (by norm_num) herror
  have he : ε/(1/16) = 16*ε := by ring
  simpa only [he] using hh

end Lax342547Proofs.PointPrediction
