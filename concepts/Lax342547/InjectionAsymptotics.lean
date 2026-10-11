import Lax342547.InjectionBudgets
import Mathlib.Analysis.SpecificLimits.Normed

/-!
---
title: Relative injection loss for polynomial accepting mass
type: lemma
---
Dyadic exceptions with the actual floor exponent vanish against every fixed polynomial, and finite test unions retain arbitrary relative error.
-/

namespace Lax342547.InjectionAsymptotics

open Filter

axiom polynomial_dyadic_floor_tends_zero (c d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (N : ℝ)^c/(2 : ℝ)^(N/d)) atTop (nhds 0)

axiom eventually_relative_exception (c d : ℕ) (hd : 0 < d) (J ε : ℝ)
    (hJ : 0 ≤ J) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,J*(1/(2 : ℝ)^(N/d)+1/(2 : ℝ)^N) ≤ ε/(N : ℝ)^c

axiom relative_union_budget (J : ℕ) (ε a τ bad : ℝ) (hJ : 0 < J) (hε : 0 ≤ ε)
    (ha : 0 ≤ a) (hbad : bad ≤ J*((ε/(2*J))*a+τ)) (htail : J*τ ≤ (ε/2)*a) :
    bad ≤ ε*a

end Lax342547.InjectionAsymptotics
