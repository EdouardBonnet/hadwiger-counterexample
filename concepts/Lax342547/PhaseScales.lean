import Lax342547.MomentBudgets

/-!
---
title: The numerical no-cover phase margin
type: lemma
---
Explicit density, rank-count and channel constants are absorbed at a proved ambient threshold, yielding the paper phase tolerance below one over two hundred.
-/

namespace Lax342547.PhaseScales



axiom phase_density_budget (r h m N Γ E : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hcap : L ≤ (2 : ℝ)^(m+N)) (hΓ : 2*r+10 ≤ Γ)
    (hN : m+r*E+E*(h*h+2) ≤ N) :
    L*((r+1 : ℝ)^E*(2 : ℝ)^(2*N*r)*(2 : ℝ)^(E*(h*h+2))/(2 : ℝ)^(Γ*N)) ≤
      1/(2 : ℝ)^(8*N)

axiom phase_numerical_margin (a N : ℕ) (ha : 14 ≤ a) (hN : 1 ≤ N) :
    1/(2 : ℝ)^a+1/(2 : ℝ)^(8*N) < 1/200

end Lax342547.PhaseScales
