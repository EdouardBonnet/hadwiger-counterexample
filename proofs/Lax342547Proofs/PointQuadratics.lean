import Lax342547.PointQuadratics
import Lax342547Proofs.QuadraticDegree
import Lax342547Proofs.BaseMoments

namespace Lax342547Proofs.PointQuadratics
open Lax342547.PointQuadratics

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.SelectorInterpolation

/--
---
conclusion: Lax342547.PointQuadratics.base_evaluation_degree
---
-/
theorem base_evaluation_degree {b : ℕ} (i : Option (Fin b)) :
    (fun x : Fin b → Binary => baseEval x i) ∈ selectorSpan b 1 := by
  cases i with
  | none => exact Lax342547Proofs.SelectorInterpolation.constant_mem 1 1
  | some j =>
    have he : (fun x : Fin b → Binary => baseEval x (some j)) = monomial {j} := by
      ext x
      simp [baseEval,monomial]
    rw [he]
    exact Lax342547Proofs.SelectorInterpolation.monomial_mem _ (by simp)

/--
---
conclusion: Lax342547.PointQuadratics.point_tensor_evaluation_degree
---
-/
theorem point_tensor_evaluation_degree {b : ℕ} {Label Coord : Type} [Fintype Coord]
    (p : Label → Coord → Binary) (s : Label)
    (φ : Module.Dual Binary (Matrix (Coord × Option (Fin b)) (Coord × Option (Fin b)) Binary)) :
    (fun x : Fin b → Binary => φ (pointMoment p s x)) ∈ selectorSpan b 2 := by
  have hz (i : Coord × Option (Fin b)) :
      (fun x : Fin b → Binary => point p s x i) ∈ selectorSpan b 1 := by
    have hh := (selectorSpan b 1).smul_mem (p s i.1) (base_evaluation_degree i.2)
    have he : p s i.1 • (fun x : Fin b → Binary => baseEval x i.2) =
        (fun x : Fin b → Binary => point p s x i) := by ext x; rfl
    rw [he] at hh
    exact hh
  exact Lax342547Proofs.QuadraticDegree.linear_outer_product_degree φ
    (fun i x => point p s x i) hz

end Lax342547Proofs.PointQuadratics
