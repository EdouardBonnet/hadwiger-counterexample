import Lax342547.AcceptingInjection
import Lax342547.InjectionBudgets
import Lax342547.InjectiveDensity

/-!
---
title: Raw accepting-family injection with exponential loss
type: lemma
---
Actual raw primal frames and channel images discharge the finite sampling hypotheses; an early channel margin gives an exponential absolute accepting-pair loss.
-/

namespace Lax342547.RawAcceptingInjection

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages
open Lax342547.RealCellLaws Lax342547.PushforwardWalsh Lax342547.FiniteInjection
open Lax342547.RawFrames Lax342547.FrameSymmetry
open scoped BigOperators

axiom capped_frame_channel {B P N H : Type} [Fintype B] [Fintype P] [Fintype N] [Fintype H]
    [DecidableEq N] [DecidableEq H] (E : Matrix P P Binary) [Nonempty (Frame P H N E)]
    (β : B → ℝ) (image : B → Frame P H N E) (channel : Frame P H N E → Matrix N H Binary)
    (M : ℝ) (hM : 0 ≤ M)
    (hcap : ∀ f,push β image f ≤ M*weights (PMF.uniformOfFintype (Frame P H N E)) f)
    (hraw : ∀ y,push (weights (PMF.uniformOfFintype (Frame P H N E))) channel y ≤
      2*weights (PMF.uniformOfFintype (Matrix N H Binary)) y) :
    ∀ y,push β (fun b => channel (image b)) y ≤
      (2*M)*weights (PMF.uniformOfFintype (Matrix N H Binary)) y

axiom raw_minus_accepting_injection {A B I P N H : Type}
    [Fintype A] [Fintype B] [Fintype I] [Fintype P] [Fintype N] [Fintype H]
    [DecidableEq P] [DecidableEq N] [DecidableEq H]
    (E : Matrix P P Binary) [Nonempty (Frame P H N E)]
    (α : A → ℝ) (β : B → ℝ) (C : I → A → Prop) (key : B → I)
    (imageA : A → Frame P H N E) (imageB : B → Frame P H N E)
    (V : A → Submodule Binary (N → Binary)) (S : B → Submodule Binary (H → Binary))
    (K ℓ : ℕ) (M MB η τ : ℝ)
    (hα : Probability α) (hβ : Probability β) (hM : 0 ≤ M) (hMB : 0 ≤ MB)
    (hη : 0 ≤ η) (hτ : 0 < τ)
    (hN : Fintype.card P+Fintype.card H+1 ≤ Fintype.card N)
    (hV : ∀ a,V a ≤ LinearMap.range (imageA a).P.mulVecLin)
    (hdV : ∀ a,Module.finrank Binary (V a) ≤ K)
    (hS : ∀ b,Module.finrank Binary (S b) ≤ K)
    (hAcap : ∀ f,push α imageA f ≤ M*weights (PMF.uniformOfFintype (Frame P H N E)) f)
    (hBcap : ∀ f,push β imageB f ≤ MB*weights (PMF.uniformOfFintype (Frame P H N E)) f)
    (hgap : (M/τ)*(2*((2 : ℝ)^(Fintype.card P+Fintype.card H+K*ℓ)/(2 : ℝ)^Fintype.card N)) < η) :
    (∑ b,β b*cellMass α (fun a => C (key b) a ∧ pinFailure (V a) (imageB b).Y (S b))) ≤
      η*(∑ b,β b*cellMass α (C (key b))) + τ +
      Fintype.card I*(((2*MB)*((2 : ℝ)^(Fintype.card H*K+2*K*ℓ)/(2 : ℝ)^(Fintype.card H*ℓ)))/
        (η-(M/τ)*(2*((2 : ℝ)^(Fintype.card P+Fintype.card H+K*ℓ)/(2 : ℝ)^Fintype.card N)))^ℓ)

axiom exponential_accepting_injection {A B I P N H : Type}
    [Fintype A] [Fintype B] [Fintype I] [Fintype P] [Fintype N] [Fintype H]
    [DecidableEq P] [DecidableEq N] [DecidableEq H]
    (E : Matrix P P Binary) [Nonempty (Frame P H N E)]
    (α : A → ℝ) (β : B → ℝ) (C : I → A → Prop) (key : B → I)
    (imageA : A → Frame P H N E) (imageB : B → Frame P H N E)
    (V : A → Submodule Binary (N → Binary)) (S : B → Submodule Binary (H → Binary))
    (K m t Cs : ℕ) (M MB η : ℝ)
    (hα : Probability α) (hβ : Probability β) (hM : 0 ≤ M) (hMB : 0 ≤ MB)
    (hη : 0 ≤ η) (hηt : 1/(2 : ℝ)^t ≤ η/2)
    (hN : Fintype.card P+Fintype.card H+1 ≤ Fintype.card N)
    (hb : Fintype.card P ≤ Fintype.card N/8)
    (hm : m+Fintype.card H+1 ≤ Fintype.card N/10)
    (hMcap : M ≤ (2 : ℝ)^m) (hMBcap : 2*MB ≤ (2 : ℝ)^(m+Fintype.card N))
    (hcount : (Fintype.card I : ℝ) ≤ (2 : ℝ)^(Cs*Fintype.card N))
    (hearly : 2*K+t+20*(K+1)*(Cs+3) ≤ Fintype.card H)
    (hlength : 20*(K+1) ≤ Fintype.card N)
    (hconstant : m+Fintype.card H*K ≤ Fintype.card N)
    (hsmall : 1/(2 : ℝ)^(Fintype.card N/2) ≤ η/2)
    (hV : ∀ a,V a ≤ LinearMap.range (imageA a).P.mulVecLin)
    (hdV : ∀ a,Module.finrank Binary (V a) ≤ K)
    (hS : ∀ b,Module.finrank Binary (S b) ≤ K)
    (hAcap : ∀ f,push α imageA f ≤ M*weights (PMF.uniformOfFintype (Frame P H N E)) f)
    (hBcap : ∀ f,push β imageB f ≤ MB*weights (PMF.uniformOfFintype (Frame P H N E)) f) :
    (∑ b,β b*cellMass α (fun a => C (key b) a ∧ pinFailure (V a) (imageB b).Y (S b))) ≤
      η*(∑ b,β b*cellMass α (C (key b))) + 1/(2 : ℝ)^(Fintype.card N/100) + 1/(2 : ℝ)^Fintype.card N

end Lax342547.RawAcceptingInjection
