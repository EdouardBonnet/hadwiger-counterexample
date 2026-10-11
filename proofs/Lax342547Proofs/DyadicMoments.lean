import Lax342547.DyadicMoments
import Lax342547Proofs.MomentBudgets
import Mathlib.Data.Nat.Log

namespace Lax342547Proofs.DyadicMoments
open Lax342547.DyadicMoments

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.DyadicMoments.exists_dyadic_moment_order
---
-/
theorem exists_dyadic_moment_order (c n N : ℕ) (hc : 0 < c) (hN : c*2^(n+2) ≤ N) :
    ∃ k t : ℕ, n+2 ≤ k ∧ 2*t = 2^k ∧ c*2^k ≤ N ∧ N ≤ (2*c)*2^k := by
  let d := N/c
  let k := Nat.log 2 d
  have hd : 2^(n+2) ≤ d := by
    apply (Nat.le_div_iff_mul_le hc).mpr
    simpa only [Nat.mul_comm] using hN
  have hd0 : d ≠ 0 := by
    have hh : 0 < 2^(n+2) := by positivity
    omega
  have hk : n+2 ≤ k := Nat.le_log_of_pow_le (by omega) hd
  have hs : 2^k ≤ d := Nat.pow_log_le_self 2 hd0
  have hup : d < 2*2^k := by
    simpa only [pow_succ,Nat.mul_comm] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) d
  have hlo : c*2^k ≤ N := by
    have hh := (Nat.le_div_iff_mul_le hc).mp hs
    simpa only [Nat.mul_comm] using hh
  have hhigh : N ≤ (2*c)*2^k := by
    have hr : N%c < c := Nat.mod_lt N hc
    have hdecomp : N = c*d+N%c := (Nat.div_add_mod N c).symm
    have he : d+1 ≤ 2*2^k := by omega
    have hm := Nat.mul_le_mul_left c he
    nlinarith
  have heven : 2*2^(k-1) = 2^k := by
    have he : k-1+1 = k := by omega
    rw [Nat.mul_comm 2,← pow_succ,he]
  exact ⟨k,2^(k-1),hk,heven,hlo,hhigh⟩

/--
---
conclusion: Lax342547.DyadicMoments.fixed_dyadic_budget
---
-/
theorem fixed_dyadic_budget (c n a Γ N : ℕ) (hc : 0 < c) (hN : c*2^(n+2) ≤ N) :
    ∃ k t : ℕ, n+2 ≤ k ∧ 2*t = 2^k ∧ c*2^k ≤ N ∧
      (((4 : ℝ)^(2*t)*(1/(2 : ℝ)^(2^n*(2+a+Γ*(2*c)+1)))^(2^(k-n))+
        1/(2 : ℝ)^((4*2^n*(a+Γ*(2*c)+1))*2^(k-(n+2))))/(1/(2 : ℝ)^a)^(2*t)) ≤
          1/(2 : ℝ)^(Γ*N) := by
  obtain ⟨k,t,hk,hsize,hlo,hhi⟩ := exists_dyadic_moment_order c n N hc hN
  have hm := Lax342547Proofs.MomentBudgets.dyadic_budget_margins n k a
    (2^n*(2+a+Γ*(2*c)+1)) (4*2^n*(a+Γ*(2*c)+1)) Γ N (2*c) hk hhi le_rfl le_rfl
  refine ⟨k,t,hk,hsize,hlo,?_⟩
  rw [hsize]
  exact Lax342547Proofs.MomentBudgets.no_cover_budget _ _ _ _ _ _ _ _ hm.1 hm.2

/--
---
conclusion: Lax342547.DyadicMoments.dyadic_budget_with_fixed_parameters
---
-/
theorem dyadic_budget_with_fixed_parameters (c n a Γ P h N : ℕ) (hc : 0 < c)
    (hN : c*2^(n+2) ≤ N) (hP : 2^n*(2+a+Γ*(2*c)+1) ≤ P)
    (hh : 4*2^n*(a+Γ*(2*c)+1) ≤ h) :
    ∃ k t : ℕ, n+2 ≤ k ∧ 2*t = 2^k ∧ c*2^k ≤ N ∧
      (((4 : ℝ)^(2*t)*(1/(2 : ℝ)^P)^(2^(k-n))+
        1/(2 : ℝ)^(h*2^(k-(n+2))))/(1/(2 : ℝ)^a)^(2*t)) ≤
          1/(2 : ℝ)^(Γ*N) := by
  obtain ⟨k,t,hk,hsize,hlo,hhi⟩ := exists_dyadic_moment_order c n N hc hN
  have hm := Lax342547Proofs.MomentBudgets.dyadic_budget_margins n k a P h Γ N (2*c) hk hhi hP hh
  refine ⟨k,t,hk,hsize,hlo,?_⟩
  rw [hsize]
  exact Lax342547Proofs.MomentBudgets.no_cover_budget _ _ _ _ _ _ _ _ hm.1 hm.2

end Lax342547Proofs.DyadicMoments
