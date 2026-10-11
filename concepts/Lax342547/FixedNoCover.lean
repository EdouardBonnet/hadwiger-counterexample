import Lax342547.NoCoverPhase
import Lax342547.DyadicMoments

/-!
---
title: Uniform no-cover phase cancellation with fixed parameters
type: definition and theorem
---
Fixed parameters, chosen before the actual unit laws, control every bounded-rank opposite tensor target under the actual raw frame marginal density; a proved ambient threshold supplies the dyadic moment order.
-/

namespace Lax342547.FixedNoCover

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ChannelDensity Lax342547.ChannelCharacters
open Lax342547.RealCellLaws Lax342547.FiniteSampling Lax342547.TensorCharacters
open Lax342547.PushforwardWalsh Lax342547.RetainedImages Lax342547.ChannelColumns
open Lax342547.RelativeEntropy Lax342547.ComponentSpaces Lax342547.ComponentDuals Lax342547.CoverProjection
open scoped BigOperators

axiom fixed_parameter_no_cover_phase {e B N Ω : Type} [Fintype e] [Fintype B] [Fintype N] [Fintype Ω]
    [DecidableEq e] [DecidableEq N] (E : Matrix B B Binary)
    (μ : Ω → ℝ) (A : Ω → e → Matrix N N Binary) (ψ : (e → Matrix N N Binary) → Ω → ℝ) (r h a c Γ P : ℕ)
    [Nonempty (Frame B (Fin h) N E)] (hN : 2*h+1 ≤ Fintype.card N)
    (hμ : Probability μ) (hr : 1 ≤ r)
    (hA : ∀ x, ∑ i, (A x i).rank ≤ r) (hψ : ∀ S, (∑ i, (S i).rank) ≤ r → ∀ x, |ψ S x| ≤ 1)
    (hc : 0 < c) (hscale : c*2^(100*r+12) ≤ Fintype.card N)
    (hP : 2^(100*r+10)*(2+a+Γ*(2*c)+1) ≤ P)
    (hh : 4*2^(100*r+10)*(a+Γ*(2*c)+1) ≤ h)
    (β : (e → Frame B (Fin h) N E) → ℝ) (L : ℝ)
    (S : (e → Frame B (Fin h) N E) → e → Matrix N N Binary)
    (hβ : Probability β) (hL : 0 ≤ L)
    (hβcap : ∀ o, β o ≤ L*weights (Lax342547.RawLaw.uniformLaw E) o)
    (hS : ∀ o, (∑ i, (S o i).rank) ≤ r)
    (hcover : ∀ S : Submodule Binary (e → N → Binary),
      ∀ T : Submodule Binary (Module.Dual Binary (e → N → Binary)),
      Componentwise S → DualComponentwise T →
      (Module.finrank Binary S : ℝ) ≤ (r : ℝ)*(Fintype.card N/c) →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(Fintype.card N/c) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) S T = 0) ≤ 1/(2 : ℝ)^P) :
    |∑ o, β o*(∑ x, μ x*ψ (S o) x*tensorCharacter h (A x) (columnsEquiv h (fun a => channels (o a))))| ≤
      1/(2 : ℝ)^a+L*((r+1 : ℝ)^Fintype.card e*(2 : ℝ)^(2*Fintype.card N*r)*
        (2 : ℝ)^(Fintype.card e*(h*h+2))/(2 : ℝ)^(Γ*Fintype.card N))

end Lax342547.FixedNoCover
