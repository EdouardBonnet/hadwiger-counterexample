import Lax342547.QuadraticDegree

/-!
---
title: Polynomial degree of actual tensor evaluations
type: definition and theorem
---
Linear tensor evaluations retain the sum of coordinate degrees, including the exact twice-selector-degree bound for point tensors.
-/

namespace Lax342547.PolynomialTensors

open Lax342547.MomentSpace Lax342547.SelectorInterpolation
open scoped BigOperators

axiom linear_outer_product_degree_bound {b d : ℕ} {I : Type} [Fintype I]
    (φ : Module.Dual Binary (Matrix I I Binary)) (z : I → (Fin b → Binary) → Binary)
    (hz : ∀ i, z i ∈ selectorSpan b d) :
    (fun x => φ (Matrix.of (fun i j => z i x*z j x))) ∈ selectorSpan b (d+d)

axiom selector_tensor_degree {b degree : ℕ} {Base : Type} [Fintype Base]
    (φ : Module.Dual Binary (Matrix (SelectorCoordinates b degree × Option Base)
      (SelectorCoordinates b degree × Option Base) Binary)) (z : Base → Binary) :
    (fun s => φ (pointMoment selectorEval s z)) ∈ selectorSpan b (degree+degree)

end Lax342547.PolynomialTensors
