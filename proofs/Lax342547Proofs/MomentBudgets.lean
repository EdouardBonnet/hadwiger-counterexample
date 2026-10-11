import Lax342547.MomentBudgets

namespace Lax342547Proofs.MomentBudgets
open Lax342547.MomentBudgets

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.MomentBudgets.power_ratio_bound
---
-/
theorem power_ratio_bound (a b c : ℕ) (h : a+c ≤ b) :
    (2 : ℝ)^a/(2 : ℝ)^b ≤ 1/(2 : ℝ)^c := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul,← pow_add]
  exact pow_le_pow_right₀ (by norm_num) h

/--
---
conclusion: Lax342547.MomentBudgets.no_cover_budget
---
-/
theorem no_cover_budget (s q R a P h Γ N : ℕ)
    (hP : (2+a)*s+Γ*N+1 ≤ P*q) (hh : a*s+Γ*N+1 ≤ h*R) :
    ((4 : ℝ)^s*(1/(2 : ℝ)^P)^q+1/(2 : ℝ)^(h*R))/(1/(2 : ℝ)^a)^s ≤
      1/(2 : ℝ)^(Γ*N) := by
  have h4 : (4 : ℝ)^s = 2^(2*s) := by rw [pow_mul]; norm_num
  have he : ((4 : ℝ)^s*(1/(2 : ℝ)^P)^q+1/(2 : ℝ)^(h*R))/(1/(2 : ℝ)^a)^s =
      (2 : ℝ)^((2+a)*s)/(2 : ℝ)^(P*q)+(2 : ℝ)^(a*s)/(2 : ℝ)^(h*R) := by
    rw [h4,div_pow,div_pow,one_pow,one_pow,← pow_mul,← pow_mul,add_div]
    field_simp
    simp only [← pow_add]
    congr 1 <;> congr 1 <;> ring
  rw [he]
  have h1 := Lax342547.MomentBudgets.power_ratio_bound ((2+a)*s) (P*q) (Γ*N+1) hP
  have h2 := Lax342547.MomentBudgets.power_ratio_bound (a*s) (h*R) (Γ*N+1) hh
  have he2 : 1/(2 : ℝ)^(Γ*N+1)+1/(2 : ℝ)^(Γ*N+1) = 1/(2 : ℝ)^(Γ*N) := by
    rw [pow_succ]
    ring
  exact (add_le_add h1 h2).trans_eq he2

/--
---
conclusion: Lax342547.MomentBudgets.dyadic_budget_margins
---
-/
theorem dyadic_budget_margins (n k a P h Γ N C : ℕ) (hk : n+2 ≤ k)
    (hN : N ≤ C*2^k) (hP : 2^n*(2+a+Γ*C+1) ≤ P)
    (hh : 4*2^n*(a+Γ*C+1) ≤ h) :
    (2+a)*2^k+Γ*N+1 ≤ P*2^(k-n) ∧
      a*2^k+Γ*N+1 ≤ h*2^(k-(n+2)) := by
  have hpow : 2^n*2^(k-n) = 2^k := by rw [← pow_add,Nat.add_sub_of_le (by omega)]
  have hpow2 : 4*2^n*2^(k-(n+2)) = 2^k := by
    have he : n+2+(k-(n+2)) = k := Nat.add_sub_of_le hk
    calc
      _ = 2^(n+2)*2^(k-(n+2)) := by rw [pow_add]; ring
      _ = _ := by rw [← pow_add,he]
  have hone : 1 ≤ 2^k := Nat.one_le_pow _ _ (by omega)
  have hPN := Nat.mul_le_mul_left Γ hN
  constructor
  · have hm := Nat.mul_le_mul_right (2^(k-n)) hP
    have he : 2^n*(2+a+Γ*C+1)*2^(k-n) = (2+a)*2^k+Γ*(C*2^k)+2^k := by
      calc
        _ = (2^n*2^(k-n))*(2+a+Γ*C+1) := by ring
        _ = _ := by rw [hpow]; ring
    rw [he] at hm
    omega
  · have hm := Nat.mul_le_mul_right (2^(k-(n+2))) hh
    have he : 4*2^n*(a+Γ*C+1)*2^(k-(n+2)) = a*2^k+Γ*(C*2^k)+2^k := by
      calc
        _ = (4*2^n*2^(k-(n+2)))*(a+Γ*C+1) := by ring
        _ = _ := by rw [hpow2]; ring
    rw [he] at hm
    omega

end Lax342547Proofs.MomentBudgets
