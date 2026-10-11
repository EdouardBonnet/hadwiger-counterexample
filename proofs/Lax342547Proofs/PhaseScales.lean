import Lax342547.PhaseScales
import Lax342547.MomentBudgets

namespace Lax342547Proofs.PhaseScales
open Lax342547.PhaseScales

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.PhaseScales.phase_density_budget
---
-/
theorem phase_density_budget (r h m N Γ E : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hcap : L ≤ (2 : ℝ)^(m+N)) (hΓ : 2*r+10 ≤ Γ)
    (hN : m+r*E+E*(h*h+2) ≤ N) :
    L*((r+1 : ℝ)^E*(2 : ℝ)^(2*N*r)*(2 : ℝ)^(E*(h*h+2))/(2 : ℝ)^(Γ*N)) ≤
      1/(2 : ℝ)^(8*N) := by
  have hr : r+1 ≤ 2^r := Nat.succ_le_of_lt r.lt_two_pow_self
  have hcr : (r+1 : ℝ)^E ≤ (2 : ℝ)^(r*E) := by
    have hh : (r+1 : ℝ) ≤ (2 : ℝ)^r := by exact_mod_cast hr
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity) hh E
  have hh : L*((r+1 : ℝ)^E*(2 : ℝ)^(2*N*r)*(2 : ℝ)^(E*(h*h+2))/(2 : ℝ)^(Γ*N)) ≤
      (2 : ℝ)^((m+N)+r*E+2*N*r+E*(h*h+2))/(2 : ℝ)^(Γ*N) := by
    have ht : (r+1 : ℝ)^E*(2 : ℝ)^(2*N*r)*(2 : ℝ)^(E*(h*h+2)) ≤
        (2 : ℝ)^(r*E)*(2 : ℝ)^(2*N*r)*(2 : ℝ)^(E*(h*h+2)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcr (by positivity)) (by positivity)
    have hs := mul_le_mul hcap ht (by positivity) (by positivity)
    rw [← mul_div_assoc]
    apply (div_le_div_of_nonneg_right hs (by positivity)).trans_eq
    simp only [← pow_add]
    congr 2
    ring
  apply hh.trans
  apply Lax342547.MomentBudgets.power_ratio_bound
  have hg := Nat.mul_le_mul_right N hΓ
  have he : (m+N)+r*E+2*N*r+E*(h*h+2)+8*N ≤ (2*r+10)*N := by nlinarith
  exact he.trans hg

/--
---
conclusion: Lax342547.PhaseScales.phase_numerical_margin
---
-/
theorem phase_numerical_margin (a N : ℕ) (ha : 14 ≤ a) (hN : 1 ≤ N) :
    1/(2 : ℝ)^a+1/(2 : ℝ)^(8*N) < 1/200 := by
  have h1 : 1/(2 : ℝ)^a ≤ 1/2^14 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) ha)
  have h2 : 1/(2 : ℝ)^(8*N) ≤ 1/2^8 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  norm_num at h1 h2 ⊢
  linarith

end Lax342547Proofs.PhaseScales
