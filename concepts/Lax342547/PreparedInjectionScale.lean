import Lax342547.PreparedInjection

/-!
---
title: Early channel choice for prepared accepting-pair injection
type: theorem
---
Choose channel size before the ambient dimension, density law, or accepting
mass exponent. The later onset pays every fixed polynomial loss; a density
exponent at most N/100 and primal dimension at most N/8 suffice.
-/

namespace Lax342547.PreparedInjectionScale

open Lax342547.PreparedInjection

axiom exists_prepared_parameters (K Cs J : ℕ) (ε : ℝ) (hJ : 0 < J) (hε : 0 < ε) :
    ∃ t h : ℕ,∀ c : ℕ,∃ N₀ : ℕ,∀ N : ℕ,N₀ ≤ N → ∀ p m : ℕ,
      p ≤ N/8 → m ≤ N/100 →
      Budget K m t Cs p h N (ε/(2*J)) ∧
      (J : ℝ)*(1/(2 : ℝ)^(N/100)+1/(2 : ℝ)^N) ≤ (ε/2)/(N : ℝ)^c

end Lax342547.PreparedInjectionScale
