import Lax342547.EmptyPredictions
import Lax342547Proofs.AtomParameters
import Lax342547Proofs.SharedTesterPoint
import Lax342547Proofs.BooleanWeight

namespace Lax342547Proofs.EmptyPredictions
open Lax342547.EmptyPredictions

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteCut
open Lax342547.ConcreteGeometry Lax342547.SelectorInterpolation Lax342547.RetainedImages
open Lax342547.AtomParameters Lax342547.SharedTesterPoint
open scoped BigOperators

/--
---
conclusion: Lax342547.EmptyPredictions.nonexceptional_prediction_exact
---
-/
theorem nonexceptional_prediction_exact {k n b degree r : ℕ} (hr : 2*r ≤ n)
    (l : Tag k) (s : Fin b → Binary) (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary)
    (herr : cellMass (fun _ : Fin (ParameterSize n l Flavor.generic) → Binary =>
      1/(2 : ℝ)^(ParameterSize n l Flavor.generic))
      (fun x => φ (parameterAtom (degree := degree) l s Flavor.generic x)+
        γ*eta (b := b) (degree := degree) hr (pointMoment selectorEval s (parameterBase l Flavor.generic x)) ≠ 0) < 1/4) :
    ∀ z (hz : ∀ i,i ∉ allowedBase k n l → z i = 0),
      φ (atom (degree := degree) l s z hz)+γ*eta (b := b) (degree := degree) hr (pointMoment selectorEval s z) = 0 := by
  have hp := Lax342547Proofs.AtomParameters.parameter_atom_degree l s Flavor.generic φ
  have hq := Lax342547Proofs.AtomParameters.parameter_tensor_degree l s Flavor.generic (eta (b := b) (degree := degree) hr)
  have hd := (selectorSpan (ParameterSize n l Flavor.generic) 2).add_mem hp
    ((selectorSpan (ParameterSize n l Flavor.generic) 2).smul_mem γ hq)
  have he : (fun x => φ (parameterAtom (degree := degree) l s Flavor.generic x)+
      γ*eta (b := b) (degree := degree) hr (pointMoment selectorEval s (parameterBase l Flavor.generic x))) = 0 :=
    Lax342547Proofs.QuadraticDegree.quadratic_error_exactification _ hd herr
  intro z hz
  obtain ⟨x,hx⟩ := Lax342547Proofs.AtomParameters.generic_parameters_cover l z hz
  have hh := congrFun he x
  change φ (atom l s (parameterBase l Flavor.generic x) _)+
    γ*eta (b := b) (degree := degree) hr (pointMoment selectorEval s (parameterBase l Flavor.generic x)) = 0 at hh
  simpa only [hx] using hh

/--
---
conclusion: Lax342547.EmptyPredictions.vanishing_prediction_exact
---
-/
theorem vanishing_prediction_exact {k n b degree r : ℕ} (hr : 2*r ≤ n) (hr0 : 0 < r)
    (φ : Module.Dual Binary (Profile k n b degree)) (γ : Binary)
    (E : Finset (Fin b → Binary)) (hE : 2^(degree+degree)*E.card < 2^b)
    (herr : ∀ l s,s ∉ E → cellMass (fun _ : Fin (ParameterSize n l Flavor.generic) → Binary =>
      1/(2 : ℝ)^(ParameterSize n l Flavor.generic))
      (fun x => φ (parameterAtom (degree := degree) l s Flavor.generic x)+
        γ*eta (b := b) (degree := degree) hr (pointMoment selectorEval s (parameterBase l Flavor.generic x)) ≠ 0) < 1/4) :
    γ = 0 ∧ φ = 0 := by
  have hall (l : Tag k) (z : Base k n → Binary) (hz : ∀ i,i ∉ allowedBase k n l → z i = 0) (s : Fin b → Binary) :
      φ (atom (degree := degree) l s z hz)+γ*eta (b := b) (degree := degree) hr (pointMoment selectorEval s z) = 0 := by
    have hp := Lax342547Proofs.AtomParameters.atom_selector_degree l φ z hz
    have hq := Lax342547Proofs.PolynomialTensors.selector_tensor_degree (eta (b := b) (degree := degree) hr) z
    have hd := (selectorSpan b (degree+degree)).add_mem hp ((selectorSpan b (degree+degree)).smul_mem γ hq)
    have he := Lax342547Proofs.BooleanWeight.excluded_labels_exactification
      (fun s => φ (atom (degree := degree) l s z hz)+γ*eta (b := b) (degree := degree) hr (pointMoment selectorEval s z)) hd E
      (fun s hs => nonexceptional_prediction_exact hr l s φ γ (herr l s hs) z hz) hE
    exact congrFun he s
  have hg : γ = 0 := by
    apply Lax342547Proofs.CommonAtoms.common_atom_constant_zero (0 : Fin b → Binary)
      sharedTesterPoint (fun l => Lax342547Proofs.SharedTesterPoint.shared_point_allowed l) φ γ
    intro l
    have hh := hall l sharedTesterPoint (Lax342547Proofs.SharedTesterPoint.shared_point_allowed l) 0
    rw [Lax342547Proofs.SharedTesterPoint.shared_point_eta_one hr hr0,mul_one] at hh
    exact add_right_cancel (hh.trans (ZModModule.add_self γ).symm)
  refine ⟨hg,Lax342547Proofs.AtomFunctionals.atom_functional_ext φ ?_⟩
  intro l s z hz
  simpa only [hg,zero_mul,add_zero] using hall l z hz s

end Lax342547Proofs.EmptyPredictions
