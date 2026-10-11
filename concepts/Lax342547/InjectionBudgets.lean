import Lax342547.MomentBudgets

/-!
---
title: Early channel choice and injection exponent budgets
type: lemma
---
The channel dimension chosen before unit laws pays the accepting-family union, while actual conditioned primal avoidance retains an exponential margin.
-/

namespace Lax342547.InjectionBudgets



axiom amplified_ratio_budget (h K ℓ t m c N : ℕ) (L gap count : ℝ)
    (hL : 0 ≤ L) (hg : 1/(2 : ℝ)^t ≤ gap)
    (hLc : L ≤ (2 : ℝ)^m) (hc : count ≤ (2 : ℝ)^c) (hcount : 0 ≤ count)
    (hb : m+c+h*K+(2*K+t)*ℓ+N ≤ h*ℓ) :
    count*((L*((2 : ℝ)^(h*K+2*K*ℓ)/(2 : ℝ)^(h*ℓ)))/gap^ℓ) ≤ 1/(2 : ℝ)^N

axiom quotient_probe_length (K N : ℕ) (hN : 20*(K+1) ≤ N) :
    N ≤ 20*(K+1)*(N/(10*(K+1)))

axiom early_channel_margin (K t Cs m h N : ℕ)
    (hh : 2*K+t+20*(K+1)*(Cs+3) ≤ h)
    (hN : 20*(K+1) ≤ N) (hm : m+h*K ≤ N) :
    (m+N)+Cs*N+h*K+(2*K+t)*(N/(10*(K+1)))+N ≤ h*(N/(10*(K+1)))

axiom accepting_family_exponential_budget (K t Cs m h N : ℕ) (L gap count : ℝ)
    (hL : 0 ≤ L) (hcount : 0 ≤ count) (hg : 1/(2 : ℝ)^t ≤ gap)
    (hLc : L ≤ (2 : ℝ)^(m+N)) (hc : count ≤ (2 : ℝ)^(Cs*N))
    (hh : 2*K+t+20*(K+1)*(Cs+3) ≤ h)
    (hN : 20*(K+1) ≤ N) (hm : m+h*K ≤ N) :
    count*((L*((2 : ℝ)^(h*K+2*K*(N/(10*(K+1))))/(2 : ℝ)^(h*(N/(10*(K+1))))))/gap^(N/(10*(K+1)))) ≤
      1/(2 : ℝ)^N

axiom primal_avoidance_exponent (K b h m N : ℕ)
    (hb : b ≤ N/8) (hm : m+h+1 ≤ N/10) :
    m+N/100+b+h+K*(N/(10*(K+1)))+1+N/2 ≤ N

axiom conditioned_avoidance_budget (K b h m N : ℕ) (M : ℝ)
    (hM : 0 ≤ M) (hMc : M ≤ (2 : ℝ)^m)
    (hb : b ≤ N/8) (hm : m+h+1 ≤ N/10) :
    (M/(1/(2 : ℝ)^(N/100)))*(2*((2 : ℝ)^(b+h+K*(N/(10*(K+1))))/(2 : ℝ)^N)) ≤
      1/(2 : ℝ)^(N/2)

end Lax342547.InjectionBudgets
