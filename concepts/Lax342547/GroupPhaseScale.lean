import Lax342547.MomentBudgets

/-!
---
title: Phase density budgets for selected channel groups
type: definition and theorem
---
Original target counting and selected endpoint-channel density costs are paid separately in the explicit phase margin.
-/

namespace Lax342547.GroupPhaseScale



axiom group_phase_density_budget (r h m N Γ E G : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hcap : L ≤ (2 : ℝ)^(m+N)) (hΓ : 2*r+10 ≤ Γ)
    (hN : m+r*E+G*(h*h+2) ≤ N) :
    L*((r+1 : ℝ)^E*(2 : ℝ)^(2*N*r)*(2 : ℝ)^(G*(h*h+2))/(2 : ℝ)^(Γ*N)) ≤
      1/(2 : ℝ)^(8*N)

end Lax342547.GroupPhaseScale
