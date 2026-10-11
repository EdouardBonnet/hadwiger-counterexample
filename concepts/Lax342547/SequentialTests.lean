import Lax342547.FiniteSampling
import Mathlib.Data.Fin.Tuple.Basic

/-!
---
title: Finite sequential tests
type: definition and theorem
---
Independent finite draws satisfy sequential lower bounds under prefix-dependent tests, including a bounded sampling horizon.
-/

namespace Lax342547.SequentialTests

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling
open scoped BigOperators

def accepts {Ω : Type} (P : ∀ j,(Fin j → Ω) → Ω → Prop) : ∀ n,(Fin n → Ω) → Prop
  | 0,_ => True
  | n+1,s => accepts P n (Fin.init s) ∧ P n (Fin.init s) (s (Fin.last n))

axiom step_probability {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (P : ∀ j,(Fin j → Ω) → Ω → Prop) (n : ℕ) :
    by
      classical
      exact cellMass (productLaw (fun _ : Fin (n+1) => μ)) (accepts P (n+1)) =
      ∑ s : Fin n → Ω,productLaw (fun _ : Fin n => μ) s*
        (if accepts P n s then cellMass μ (P n s) else 0)

axiom sequential_lower_probability {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (P : ∀ j,(Fin j → Ω) → Ω → Prop) (c : ℝ)
    (hμ : Probability μ) (hc : 0 ≤ c)
    (hstep : ∀ j s,accepts P j s → c ≤ cellMass μ (P j s)) (n : ℕ) :
    c^n ≤ cellMass (productLaw (fun _ : Fin n => μ)) (accepts P n)

axiom bounded_sequential_lower_probability {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (P : ∀ j,(Fin j → Ω) → Ω → Prop) (c : ℝ)
    (hμ : Probability μ) (hc : 0 ≤ c)
    (n : ℕ) (hstep : ∀ j,j < n → ∀ s,accepts P j s → c ≤ cellMass μ (P j s)) :
    c^n ≤ cellMass (productLaw (fun _ : Fin n => μ)) (accepts P n)

axiom safe_failure_mass {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (F S : Ω → Prop) (hμ : ∀ x,0 ≤ μ x) :
    cellMass μ F-cellMass μ (fun x => ¬ S x) ≤ cellMass μ (fun x => F x ∧ S x)

axiom sequential_failure_lower {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (F : Ω → Prop) (S : ∀ j,(Fin j → Ω) → Ω → Prop) (η δ : ℝ)
    (hμ : Probability μ) (hgap : δ ≤ η) (hF : η ≤ cellMass μ F)
    (havoid : ∀ j s,accepts (fun j s x => F x ∧ S j s x) j s →
      cellMass μ (fun x => ¬ S j s x) ≤ δ) (n : ℕ) :
    (η-δ)^n ≤ cellMass (productLaw (fun _ : Fin n => μ))
      (accepts (fun j s x => F x ∧ S j s x) n)

axiom bounded_sequential_failure_lower {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (F : Ω → Prop) (S : ∀ j,(Fin j → Ω) → Ω → Prop) (η δ : ℝ)
    (hμ : Probability μ) (hgap : δ ≤ η) (hF : η ≤ cellMass μ F)
    (n : ℕ) (havoid : ∀ j,j < n → ∀ s,accepts (fun j s x => F x ∧ S j s x) j s →
      cellMass μ (fun x => ¬ S j s x) ≤ δ) :
    (η-δ)^n ≤ cellMass (productLaw (fun _ : Fin n => μ))
      (accepts (fun j s x => F x ∧ S j s x) n)

axiom accepts_pointwise {Ω : Type} (P : ∀ j,(Fin j → Ω) → Ω → Prop) (F : Ω → Prop)
    (hP : ∀ j t x,P j t x → F x) (n : ℕ) (s : Fin n → Ω)
    (hs : accepts P n s) : ∀ i,F (s i)

end Lax342547.SequentialTests
