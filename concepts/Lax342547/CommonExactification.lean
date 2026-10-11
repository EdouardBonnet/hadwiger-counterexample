import Lax342547.BooleanWeight
import Lax342547.MomentTails
import Lax342547.FiniteSampling

/-!
---
title: Exact common predictions on retained mass
type: definition and theorem
---
An actual average-error bound retains a large set of units; Boolean polynomial nonvanishing turns their approximate predictions into one exact common function.
-/

namespace Lax342547.CommonExactification

open Lax342547.MomentSpace Lax342547.SelectorInterpolation Lax342547.RetainedImages
open Lax342547.RelativeEntropy
open scoped BigOperators

axiom discrepancy_mass_union {X : Type} [Fintype X]
    (α : X → ℝ) (f p q : X → Binary) (hα : ∀ x, 0 ≤ α x) :
    cellMass α (fun x => p x ≠ q x) ≤
      cellMass α (fun x => p x ≠ f x)+cellMass α (fun x => q x ≠ f x)

axiom common_prediction_exact {b d : ℕ}
    (f p q : (Fin b → Binary) → Binary)
    (hp : p ∈ selectorSpan b d) (hq : q ∈ selectorSpan b d)
    (herr : cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b) (fun x => p x ≠ f x)+
      cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b) (fun x => q x ≠ f x) < 1/(2 : ℝ)^d) : p = q

axiom prediction_good_mass {U X : Type} [Fintype U] [Fintype X]
    (β : U → ℝ) (α : X → ℝ) (f : X → Binary) (p : U → X → Binary) (ε a : ℝ)
    (hβ : Probability β) (hα : ∀ x, 0 ≤ α x) (ha : 0 < a)
    (herror : (∑ u, β u*cellMass α (fun x => p u x ≠ f x)) ≤ ε) :
    1-ε/a ≤ cellMass β (fun u => cellMass α (fun x => p u x ≠ f x) < a)

axiom retained_common_prediction {U : Type} [Fintype U] {b d : ℕ}
    (β : U → ℝ) (f : (Fin b → Binary) → Binary)
    (p : U → (Fin b → Binary) → Binary) (ε a : ℝ)
    (hβ : Probability β) (hp : ∀ u, p u ∈ selectorSpan b d)
    (ha : 0 < a) (hε : ε < a) (hdegree : 2*a ≤ 1/(2 : ℝ)^d)
    (herror : (∑ u, β u*cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b)
      (fun x => p u x ≠ f x)) ≤ ε) :
    ∃ u₀ : U, 1-ε/a ≤ cellMass β (fun u => p u = p u₀)

end Lax342547.CommonExactification
