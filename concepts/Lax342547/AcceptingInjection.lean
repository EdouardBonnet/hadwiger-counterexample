import Lax342547.FiniteInjection
import Lax342547.AcceptingFamilies
import Lax342547.UnitSpanAvoidance
import Lax342547.GreedySpaces

/-!
---
title: Actual finite accepting-pair injection
type: definition and theorem
---
Greedy pin probes and whole-unit protected spaces give a finite accepting-pair loss bound for the entire accepting family, with raw primal avoidance and retained masses.
-/

namespace Lax342547.AcceptingInjection

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages
open Lax342547.RealCellLaws Lax342547.PushforwardWalsh Lax342547.FiniteInjection
open Lax342547.RawFrames
open scoped BigOperators

axiom accepting_family_injection {A B I N H : Type}
    [Fintype A] [Fintype B] [Fintype I] [Fintype N] [Fintype H]
    [DecidableEq N] [DecidableEq H]
    (α : A → ℝ) (β : B → ℝ) (C : I → A → Prop) (key : B → I)
    (V : A → Submodule Binary (N → Binary)) (Y : B → Matrix N H Binary)
    (S : B → Submodule Binary (H → Binary)) (K ℓ : ℕ) (L η δ τ : ℝ)
    (hα : Probability α) (hβ : Probability β) (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hτ : 0 < τ) (hgap : δ < η)
    (hV : ∀ a,Module.finrank Binary (V a) ≤ K)
    (hS : ∀ b,Module.finrank Binary (S b) ≤ K)
    (hcap : ∀ y,push β Y y ≤ L*weights (PMF.uniformOfFintype (Matrix N H Binary)) y)
    (havoid : ∀ i,τ ≤ cellMass α (C i) → ∀ j,j < ℓ → ∀ t : Fin j → A,
      cellMass (conditionalLaw α (C i)) (fun a => ¬ Disjoint (V a) (⨆ k : Fin j,V (t k))) ≤ δ) :
    (∑ b,β b*cellMass α (fun a => C (key b) a ∧ pinFailure (V a) (Y b) (S b))) ≤
      η*(∑ b,β b*cellMass α (C (key b))) + τ +
      Fintype.card I*((L*((2 : ℝ)^(Fintype.card H*K+2*K*ℓ)/(2 : ℝ)^(Fintype.card H*ℓ)))/(η-δ)^ℓ)

axiom primal_accepting_family_injection {A B I P N H : Type}
    [Fintype A] [Fintype B] [Fintype I] [Fintype P] [Fintype N] [Fintype H]
    [DecidableEq P] [DecidableEq N] [DecidableEq H]
    (E : Matrix P P Binary) [Nonempty (Frame P H N E)]
    (α : A → ℝ) (β : B → ℝ) (C : I → A → Prop) (key : B → I)
    (image : A → Frame P H N E) (V : A → Submodule Binary (N → Binary))
    (Y : B → Matrix N H Binary) (S : B → Submodule Binary (H → Binary))
    (K ℓ : ℕ) (M L η τ : ℝ)
    (hα : Probability α) (hβ : Probability β) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hη : 0 ≤ η) (hτ : 0 < τ)
    (hN : Fintype.card P+Fintype.card H+1 ≤ Fintype.card N)
    (hV : ∀ a,V a ≤ LinearMap.range (image a).P.mulVecLin)
    (hdV : ∀ a,Module.finrank Binary (V a) ≤ K)
    (hS : ∀ b,Module.finrank Binary (S b) ≤ K)
    (hAcap : ∀ f,push α image f ≤ M*weights (PMF.uniformOfFintype (Frame P H N E)) f)
    (hBcap : ∀ y,push β Y y ≤ L*weights (PMF.uniformOfFintype (Matrix N H Binary)) y)
    (hgap : (M/τ)*(2*((2 : ℝ)^(Fintype.card P+Fintype.card H+K*ℓ)/(2 : ℝ)^Fintype.card N)) < η) :
    (∑ b,β b*cellMass α (fun a => C (key b) a ∧ pinFailure (V a) (Y b) (S b))) ≤
      η*(∑ b,β b*cellMass α (C (key b))) + τ +
      Fintype.card I*((L*((2 : ℝ)^(Fintype.card H*K+2*K*ℓ)/(2 : ℝ)^(Fintype.card H*ℓ)))/
        (η-(M/τ)*(2*((2 : ℝ)^(Fintype.card P+Fintype.card H+K*ℓ)/(2 : ℝ)^Fintype.card N)))^ℓ)

end Lax342547.AcceptingInjection
