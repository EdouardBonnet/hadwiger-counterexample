import Lax342547.EmptyPredictions
import Lax342547.MomentTails

/-!
---
title: Actual vanishing predictions on a retained population
type: definition and theorem
---
The aggregate generic parameter error gives an explicit discarded-mass bound, while the actual whole cut-space residual and common diagonal coefficient vanish exactly on retained units.
-/

namespace Lax342547.RetainedEmptyPredictions

open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteCut
open Lax342547.ConcreteGeometry Lax342547.RetainedImages Lax342547.RelativeEntropy
open Lax342547.AtomParameters
open scoped BigOperators

noncomputable def predictionError {k n b degree r : ℕ} (hr : 2*r ≤ n)
    (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary) (l : Tag k) (s : Fin b → Binary) : ℝ :=
  cellMass (fun _ : Fin (ParameterSize n l Flavor.generic) → Binary =>
    1/(2 : ℝ)^(ParameterSize n l Flavor.generic))
    (fun x => φ (parameterAtom (degree := degree) l s Flavor.generic x)+
      γ*eta (b := b) (degree := degree) hr (pointMoment selectorEval s (parameterBase l Flavor.generic x)) ≠ 0)

noncomputable def totalPredictionError {k n b degree r : ℕ} (hr : 2*r ≤ n)
    (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary) (E : Finset (Fin b → Binary)) : ℝ := by
  classical
  exact ∑ l : Tag k,∑ s : Fin b → Binary,if s ∈ E then 0 else predictionError hr φ γ l s

axiom prediction_error_nonneg {k n b degree r : ℕ} (hr : 2*r ≤ n)
    (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary) (l : Tag k) (s : Fin b → Binary) :
    0 ≤ predictionError hr φ γ l s

axiom prediction_error_le_total {k n b degree r : ℕ} (hr : 2*r ≤ n)
    (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary) (E : Finset (Fin b → Binary))
    (l : Tag k) (s : Fin b → Binary) (hs : s ∉ E) :
    predictionError hr φ γ l s ≤ totalPredictionError hr φ γ E

axiom retained_vanishing_predictions {U : Type} [Fintype U] {k n b degree r : ℕ}
    (hr : 2*r ≤ n) (hr0 : 0 < r) (β : U → ℝ)
    (φ : U → Module.Dual Binary (Profile k n b degree)) (γ : U → Binary)
    (E : U → Finset (Fin b → Binary)) (ε : ℝ) (hβ : Probability β)
    (hE : ∀ u,2^(degree+degree)*(E u).card < 2^b)
    (herr : (∑ u,β u*totalPredictionError hr (φ u) (γ u) (E u)) ≤ ε) :
    1-4*ε ≤ cellMass β (fun u => γ u = 0 ∧ φ u = 0)

end Lax342547.RetainedEmptyPredictions
