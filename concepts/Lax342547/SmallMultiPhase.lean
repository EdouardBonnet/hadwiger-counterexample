import Lax342547.FixedMultiPhase
import Lax342547.GroupPhaseScale
import Lax342547.PhaseScales
import Lax342547.PhaseScales

/-!
---
title: Small phases on selected endpoint channel groups
type: definition and theorem
---
The explicit numerical phase margin holds for arbitrary selected endpoint images and whole-unit marks while preserving the original no-cover rank parameter.
-/

namespace Lax342547.SmallMultiPhase

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ChannelDensity Lax342547.ChannelCharacters
open Lax342547.RealCellLaws Lax342547.FiniteSampling Lax342547.TensorCharacters
open Lax342547.PushforwardWalsh Lax342547.RetainedImages Lax342547.ChannelColumns
open Lax342547.RelativeEntropy Lax342547.ComponentSpaces Lax342547.ComponentDuals Lax342547.CoverProjection
open scoped BigOperators

axiom no_cover_marked_unit_phase_small {e d B N Ω U : Type} [Fintype e] [Fintype d] [Nonempty d] [Fintype U] [Fintype B] [Fintype N] [Fintype Ω]
    [DecidableEq e] [DecidableEq d] [DecidableEq N] (E : Matrix B B Binary)
    (μ : Ω → ℝ) (A : Ω → e → Matrix N N Binary) (ψ : (e → Matrix N N Binary) → Ω → ℝ) (r h a c P m : ℕ)
    [Nonempty (Frame B (Fin h) N E)] (hN : 2*h+1 ≤ Fintype.card N)
    (hμ : Probability μ) (hr : 1 ≤ r)
    (hA : ∀ x, ∑ i, (A x i).rank ≤ r) (hψ : ∀ S, (∑ i, (S i).rank) ≤ r → ∀ x, |ψ S x| ≤ 1)
    (hc : 0 < c) (hscale : c*2^(100*r+12) ≤ Fintype.card N)
    (hP : 2^(100*r+10)*(2+a+(2*r+10)*(2*c)+1) ≤ P)
    (hh : 4*2^(100*r+10)*(a+(2*r+10)*(2*c)+1) ≤ h)
    (β : U → ℝ) (image : U → (e × d) → Frame B (Fin h) N E) (L : ℝ)
    (S : U → e → Matrix N N Binary)
    (hβ : Probability β) (hL : 0 ≤ L)
    (hLcap : L ≤ (2 : ℝ)^(m+Fintype.card N))
    (hbig : m+r*Fintype.card e+Fintype.card (e × d)*(h*h+2) ≤ Fintype.card N)
    (ha : 14 ≤ a) (hpos : 1 ≤ Fintype.card N)
    (hβcap : ∀ o, push β image o ≤ L*weights (Lax342547.RawLaw.uniformLaw E) o)
    (hS : ∀ o, (∑ i, (S o i).rank) ≤ r)
    (hcover : ∀ S : Submodule Binary (e → N → Binary),
      ∀ T : Submodule Binary (Module.Dual Binary (e → N → Binary)),
      Componentwise S → DualComponentwise T →
      (Module.finrank Binary S : ℝ) ≤ (r : ℝ)*(Fintype.card N/c) →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(Fintype.card N/c) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) S T = 0) ≤ 1/(2 : ℝ)^P) :
    |∑ o, β o*(∑ x, μ x*ψ (S o) x*tensorCharacter h (fun i : e × d => A x i.1) (columnsEquiv h (fun a => channels (image o a))))| < 1/200

end Lax342547.SmallMultiPhase
