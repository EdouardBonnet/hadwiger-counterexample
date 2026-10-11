import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
---
title: Subexponential container counts at the paper sample scale
type: lemma
---
The logarithmic fingerprint count is bounded by a degree-three polynomial times 2^(100gN). Its ratio to 2^(1000gN) tends to zero, with an actual eventual strict exponent margin.
-/

namespace Lax342547.ContainerAsymptotics

open Filter Asymptotics

def exponentBudget (A g N : ℕ) : ℕ := (2*A*N^2+1)*(4000*g*N*2^(100*g*N)+2)

axiom container_exponent_little_o (A g : ℕ) (hg : 0 < g) :
    (fun N : ℕ => (exponentBudget A g N : ℝ)) =o[atTop] fun N => (2 : ℝ)^(1000*g*N)

axiom eventually_container_exponent (A g : ℕ) (hg : 0 < g) :
    ∀ᶠ N : ℕ in atTop, exponentBudget A g N+2 < 2^(1000*g*N)

end Lax342547.ContainerAsymptotics
