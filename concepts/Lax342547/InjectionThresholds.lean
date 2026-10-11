import Lax342547.InjectionAsymptotics

/-!
---
title: Injection parameter quantifiers
type: definition and theorem
---
The channel dimension is chosen before density constants and laws; subsequent ambient thresholds pay every fixed conditioning and probe cost.
-/

namespace Lax342547.InjectionThresholds

open Filter

axiom exists_dyadic_gap (η : ℝ) (hη : 0 < η) : ∃ t : ℕ,1/(2 : ℝ)^t ≤ η/2

axiom exists_early_parameters (K Cs : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ t h : ℕ,1/(2 : ℝ)^t ≤ η/2 ∧ 2*K+t+20*(K+1)*(Cs+3) ≤ h ∧
      ∀ m : ℕ,∃ N₀ : ℕ,∀ N : ℕ,N₀ ≤ N →
        20*(K+1) ≤ N ∧ m+h*K ≤ N ∧ m+h+1 ≤ N/10 ∧
        1/(2 : ℝ)^(N/2) ≤ η/2

end Lax342547.InjectionThresholds
