import Lax342547.NoCoverMoments

/-!
---
title: Explicit no-cover moment parameter margins
type: lemma
---
Natural-number power identities prove the finite exponential moment budget and fixed dyadic parameter choices, retaining the ambient sample-size margin.
-/

namespace Lax342547.MomentBudgets



axiom power_ratio_bound (a b c : ℕ) (h : a+c ≤ b) :
    (2 : ℝ)^a/(2 : ℝ)^b ≤ 1/(2 : ℝ)^c

axiom no_cover_budget (s q R a P h Γ N : ℕ)
    (hP : (2+a)*s+Γ*N+1 ≤ P*q) (hh : a*s+Γ*N+1 ≤ h*R) :
    ((4 : ℝ)^s*(1/(2 : ℝ)^P)^q+1/(2 : ℝ)^(h*R))/(1/(2 : ℝ)^a)^s ≤
      1/(2 : ℝ)^(Γ*N)

axiom dyadic_budget_margins (n k a P h Γ N C : ℕ) (hk : n+2 ≤ k)
    (hN : N ≤ C*2^k) (hP : 2^n*(2+a+Γ*C+1) ≤ P)
    (hh : 4*2^n*(a+Γ*C+1) ≤ h) :
    (2+a)*2^k+Γ*N+1 ≤ P*2^(k-n) ∧
      a*2^k+Γ*N+1 ≤ h*2^(k-(n+2))

end Lax342547.MomentBudgets
