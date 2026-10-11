import Lax342547.BooleanWeight
import Mathlib.Data.Matrix.Basis

/-!
---
title: Linear point-tensor evaluations are Boolean quadratics
type: definition and theorem
---
Actual outer-product tensors evaluated by an arbitrary linear functional have Boolean degree at most two; the checked nonvanishing bound exactifies error below one quarter.
-/

namespace Lax342547.QuadraticDegree

open Lax342547.MomentSpace Lax342547.SelectorInterpolation
open scoped BigOperators

axiom quadratic_function_degree {b : ℕ} {I : Type} [Fintype I]
    (A : Matrix I I Binary) (z : I → (Fin b → Binary) → Binary)
    (hz : ∀ i, z i ∈ selectorSpan b 1) :
    (fun x => ∑ i, ∑ j, A i j*z i x*z j x) ∈ selectorSpan b 2

axiom linear_outer_product_degree {b : ℕ} {I : Type} [Fintype I]
    (φ : Module.Dual Binary (Matrix I I Binary)) (z : I → (Fin b → Binary) → Binary)
    (hz : ∀ i, z i ∈ selectorSpan b 1) :
    (fun x => φ (Matrix.of (fun i j => z i x*z j x))) ∈ selectorSpan b 2

axiom quadratic_error_exactification {b : ℕ} (f : (Fin b → Binary) → Binary)
    (hf : f ∈ selectorSpan b 2)
    (herr : Lax342547.RetainedImages.cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b)
      (fun x => f x ≠ 0) < 1/4) : f = 0

end Lax342547.QuadraticDegree
