import Lax342547.ChannelDensity
import Lax342547.NoCoverMoments
import Lax342547.RealCellLaws

/-!
---
title: Actual raw frame channel phase tails
type: lemma
---
Reindexing the actual frame channels transfers independent channel character tails to the raw frame law with the explicit joint density factor.
-/

namespace Lax342547.ChannelColumns

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ChannelDensity Lax342547.ChannelCharacters
open Lax342547.RealCellLaws Lax342547.FiniteSampling Lax342547.TensorCharacters
open Lax342547.PushforwardWalsh Lax342547.RetainedImages
open Lax342547.RelativeEntropy Lax342547.ComponentSpaces Lax342547.ComponentDuals Lax342547.CoverProjection
open scoped BigOperators

noncomputable def columnsEquiv {e N : Type} (h : ℕ) :
    (e → Matrix N (Fin h) Binary × Matrix N (Fin h) Binary) ≃
      (e × Fin h → (N → Binary) × (N → Binary)) where
  toFun z := fun a => (fun i => (z a.1).1 i a.2,fun i => (z a.1).2 i a.2)
  invFun c := fun a => (fun i j => (c (a,j)).1 i,fun i j => (c (a,j)).2 i)
  left_inv _ := rfl
  right_inv _ := rfl

axiom columns_uniform_weights {e N : Type} [Fintype e] [Fintype N] [DecidableEq e] [DecidableEq N] (h : ℕ)
    (z : e → Matrix N (Fin h) Binary × Matrix N (Fin h) Binary) :
    weights (PMF.uniformOfFintype (e → Matrix N (Fin h) Binary × Matrix N (Fin h) Binary)) z =
      productLaw (fun _ : e × Fin h => channelLaw) (columnsEquiv h z)

axiom pmf_weights_map {Ω X : Type} [Fintype Ω] (p : PMF Ω) (f : Ω → X) (x : X) :
    weights (p.map f) x = push (weights p) f x

axiom push_cell_mass {Ω X : Type} [Fintype Ω] [Fintype X]
    (ρ : Ω → ℝ) (f : Ω → X) (P : X → Prop) :
    cellMass (push ρ f) P = cellMass ρ (fun o => P (f o))

axiom raw_channel_point_cap {e B N : Type} [Fintype e] [Fintype B] [Fintype N]
    [DecidableEq e] [DecidableEq N] (h : ℕ) (E : Matrix B B Binary)
    [Nonempty (Frame B (Fin h) N E)] (hN : 2*h+1 ≤ Fintype.card N)
    (z : e → Matrix N (Fin h) Binary × Matrix N (Fin h) Binary) :
    weights ((Lax342547.RawLaw.uniformLaw E).map (fun o a => channels (o a))) z ≤
      (2 : ℝ)^(Fintype.card e*(h*h+2))*
        productLaw (fun _ : e × Fin h => channelLaw) (columnsEquiv h z)

axiom raw_channel_event_cap {e B N : Type} [Fintype e] [Fintype B] [Fintype N]
    [DecidableEq e] [DecidableEq N] (h : ℕ) (E : Matrix B B Binary)
    [Nonempty (Frame B (Fin h) N E)] (hN : 2*h+1 ≤ Fintype.card N)
    (P : (e × Fin h → (N → Binary) × (N → Binary)) → Prop) :
    cellMass (weights (Lax342547.RawLaw.uniformLaw E))
      (fun o => P (columnsEquiv h (fun a => channels (o a)))) ≤
      (2 : ℝ)^(Fintype.card e*(h*h+2))*cellMass (productLaw (fun _ : e × Fin h => channelLaw)) P

axiom no_cover_raw_phase_tail {e B N Ω : Type} [Fintype e] [Fintype B] [Fintype N] [Fintype Ω]
    [DecidableEq e] [DecidableEq N] (E : Matrix B B Binary)
    (μ : Ω → ℝ) (A : Ω → e → Matrix N N Binary) (ψ : Ω → ℝ) (r h t k : ℕ) (p θ : ℝ)
    [Nonempty (Frame B (Fin h) N E)] (hN : 2*h+1 ≤ Fintype.card N)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r)
    (hA : ∀ x, ∑ i, (A x i).rank ≤ r) (hψ : ∀ x, |ψ x| ≤ 1)
    (hsize : 2*t = 2^k) (hk : 100*r+12 ≤ k) (hθ : 0 < θ)
    (hcover : ∀ S : Submodule Binary (e → N → Binary),
      ∀ T : Submodule Binary (Module.Dual Binary (e → N → Binary)),
      Componentwise S → DualComponentwise T →
      (Module.finrank Binary S : ℝ) ≤ (r : ℝ)*(2*t) →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(2*t) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) S T = 0) ≤ p) :
    cellMass (weights (Lax342547.RawLaw.uniformLaw E))
      (fun o => θ ≤ |∑ x, μ x*ψ x*tensorCharacter h (A x) (columnsEquiv h (fun a => channels (o a)))|) ≤
      (2 : ℝ)^(Fintype.card e*(h*h+2))*
        (((4 : ℝ)^(2*t)*p^(2^(k-(100*r+10)))+1/(2 : ℝ)^(h*2^(k-(100*r+12))))/θ^(2*t))

end Lax342547.ChannelColumns
