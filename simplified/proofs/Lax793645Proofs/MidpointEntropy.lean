import Lax793645.MidpointEntropy
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteEntropy

namespace Lax793645Proofs.MidpointEntropy
open Lax793645.FiniteProbability Lax793645.MidpointEntropy

/--
---
conclusion: Lax793645.MidpointEntropy.midpoint_gap
---
-/
theorem midpoint_gap {A : Type*} [Fintype A] (ρ σ : Weight A)
    (hρ : ∀ x, 0 ≤ ρ x) (hσ : ∀ x, 0 ≤ σ x)
    (D : A → Prop) (hD : ∀ x, D x → σ x = 0) :
    mass ρ D * Real.log 2 ≤ potential ρ + potential σ - 2 * potential (midpoint ρ σ) := by
  exact Upstream.OAI.HadwigerCounterexample.negEnt_gap_implementation hρ hσ D hD

/--
---
conclusion: Lax793645.MidpointEntropy.progress
---
-/
theorem progress {A : Type*} [Fintype A] (ρ σ : Weight A)
    (hρ : ∀ x, 0 ≤ ρ x) (hσ : ∀ x, 0 ≤ σ x)
    (D : A → Prop) (hD : ∀ x, D x → σ x = 0)
    (hmin : potential ρ ≤ potential (midpoint ρ σ)) :
    mass ρ D * Real.log 2 ≤ potential σ - potential ρ := by
  have h := Lax793645.MidpointEntropy.midpoint_gap ρ σ hρ hσ D hD
  linarith

end Lax793645Proofs.MidpointEntropy
