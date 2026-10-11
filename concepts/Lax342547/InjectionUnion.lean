import Lax342547.InjectionAsymptotics
import Lax342547.FiniteSampling

/-!
---
title: Accepting-pair test unions and relative loss
type: lemma
---
Actual product-pair event masses and finite injection tests retain accepting probability; the exponential tail gives arbitrary relative error under inverse-polynomial accepting mass.
-/

namespace Lax342547.InjectionUnion

open Lax342547.RelativeEntropy Lax342547.RetainedImages
open scoped BigOperators

axiom pair_event_mass {A B : Type} [Fintype A] [Fintype B] (α : A → ℝ) (β : B → ℝ)
    (E : A → B → Prop) :
    cellMass (fun p : A × B => α p.1*β p.2) (fun p => E p.1 p.2) =
      ∑ b,β b*cellMass α (fun a => E a b)

axiom finite_injection_union {A B J : Type} [Fintype A] [Fintype B] [Fintype J]
    (α : A → ℝ) (β : B → ℝ) (accept : A → B → Prop) (F : J → A → B → Prop)
    (η τ : ℝ) (hα : ∀ a,0 ≤ α a) (hβ : ∀ b,0 ≤ β b)
    (hF : ∀ j,(∑ b,β b*cellMass α (fun a => accept a b ∧ F j a b)) ≤
      η*(∑ b,β b*cellMass α (fun a => accept a b))+τ) :
    cellMass (fun p : A × B => α p.1*β p.2) (fun p => accept p.1 p.2 ∧ ∃ j,F j p.1 p.2) ≤
      Fintype.card J*(η*cellMass (fun p : A × B => α p.1*β p.2) (fun p => accept p.1 p.2)+τ)

axiom inverse_polynomial_relative_union {A B J : Type} [Fintype A] [Fintype B] [Fintype J]
    (α : A → ℝ) (β : B → ℝ) (accept : A → B → Prop) (F : J → A → B → Prop)
    (N c : ℕ) (ε : ℝ) (hJ : 0 < Fintype.card J) (hε : 0 ≤ ε)
    (hα : ∀ a,0 ≤ α a) (hβ : ∀ b,0 ≤ β b)
    (haccept : 1/(N : ℝ)^c ≤ cellMass (fun p : A × B => α p.1*β p.2) (fun p => accept p.1 p.2))
    (hF : ∀ j,(∑ b,β b*cellMass α (fun a => accept a b ∧ F j a b)) ≤
      (ε/(2*Fintype.card J))*(∑ b,β b*cellMass α (fun a => accept a b))+
        (1/(2 : ℝ)^(N/100)+1/(2 : ℝ)^N))
    (htail : (Fintype.card J : ℝ)*(1/(2 : ℝ)^(N/100)+1/(2 : ℝ)^N) ≤ (ε/2)/(N : ℝ)^c) :
    cellMass (fun p : A × B => α p.1*β p.2) (fun p => accept p.1 p.2 ∧ ∃ j,F j p.1 p.2) ≤
      ε*cellMass (fun p : A × B => α p.1*β p.2) (fun p => accept p.1 p.2)

end Lax342547.InjectionUnion
