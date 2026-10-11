import Lax342547.AtomParameters
import Lax342547.SharedTesterPoint
import Lax342547.BooleanWeight

/-!
---
title: Exactification of actual vanishing point predictions
type: definition and theorem
---
Degree-two generic parameter error removes base discrepancies; excluded-selector recovery and an actual common tester-one point force the diagonal coefficient and the whole cut-space residual to vanish.
-/

namespace Lax342547.EmptyPredictions

open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteCut
open Lax342547.ConcreteGeometry Lax342547.SelectorInterpolation Lax342547.RetainedImages
open Lax342547.AtomParameters Lax342547.SharedTesterPoint
open scoped BigOperators

axiom nonexceptional_prediction_exact {k n b degree r : ℕ} (hr : 2*r ≤ n)
    (l : Tag k) (s : Fin b → Binary) (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary)
    (herr : cellMass (fun _ : Fin (ParameterSize n l Flavor.generic) → Binary =>
      1/(2 : ℝ)^(ParameterSize n l Flavor.generic))
      (fun x => φ (parameterAtom (degree := degree) l s Flavor.generic x)+
        γ*eta (b := b) (degree := degree) hr (pointMoment selectorEval s (parameterBase l Flavor.generic x)) ≠ 0) < 1/4) :
    ∀ z (hz : ∀ i,i ∉ allowedBase k n l → z i = 0),
      φ (atom (degree := degree) l s z hz)+γ*eta (b := b) (degree := degree) hr (pointMoment selectorEval s z) = 0

axiom vanishing_prediction_exact {k n b degree r : ℕ} (hr : 2*r ≤ n) (hr0 : 0 < r)
    (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary)
    (E : Finset (Fin b → Binary)) (hE : 2^(degree+degree)*E.card < 2^b)
    (herr : ∀ l s,s ∉ E → cellMass (fun _ : Fin (ParameterSize n l Flavor.generic) → Binary =>
      1/(2 : ℝ)^(ParameterSize n l Flavor.generic))
      (fun x => φ (parameterAtom (degree := degree) l s Flavor.generic x)+
        γ*eta (b := b) (degree := degree) hr (pointMoment selectorEval s (parameterBase l Flavor.generic x)) ≠ 0) < 1/4) :
    γ = 0 ∧ φ = 0

end Lax342547.EmptyPredictions
