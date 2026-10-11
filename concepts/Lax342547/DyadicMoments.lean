import Lax342547.MomentBudgets
import Mathlib.Data.Nat.Log

/-!
---
title: Fixed dyadic moment orders at the ambient scale
type: definition and theorem
---
An explicit natural logarithm choice supplies even dyadic moments below N/c and above N/(2*c), with a fixed parameter budget independent of the actual law.
-/

namespace Lax342547.DyadicMoments



axiom exists_dyadic_moment_order (c n N : ℕ) (hc : 0 < c) (hN : c*2^(n+2) ≤ N) :
    ∃ k t : ℕ, n+2 ≤ k ∧ 2*t = 2^k ∧ c*2^k ≤ N ∧ N ≤ (2*c)*2^k

axiom fixed_dyadic_budget (c n a Γ N : ℕ) (hc : 0 < c) (hN : c*2^(n+2) ≤ N) :
    ∃ k t : ℕ, n+2 ≤ k ∧ 2*t = 2^k ∧ c*2^k ≤ N ∧
      (((4 : ℝ)^(2*t)*(1/(2 : ℝ)^(2^n*(2+a+Γ*(2*c)+1)))^(2^(k-n))+
        1/(2 : ℝ)^((4*2^n*(a+Γ*(2*c)+1))*2^(k-(n+2))))/(1/(2 : ℝ)^a)^(2*t)) ≤
          1/(2 : ℝ)^(Γ*N)

axiom dyadic_budget_with_fixed_parameters (c n a Γ P h N : ℕ) (hc : 0 < c)
    (hN : c*2^(n+2) ≤ N) (hP : 2^n*(2+a+Γ*(2*c)+1) ≤ P)
    (hh : 4*2^n*(a+Γ*(2*c)+1) ≤ h) :
    ∃ k t : ℕ, n+2 ≤ k ∧ 2*t = 2^k ∧ c*2^k ≤ N ∧
      (((4 : ℝ)^(2*t)*(1/(2 : ℝ)^P)^(2^(k-n))+
        1/(2 : ℝ)^(h*2^(k-(n+2))))/(1/(2 : ℝ)^a)^(2*t)) ≤
          1/(2 : ℝ)^(Γ*N)

end Lax342547.DyadicMoments
