import Lax342547.ContainerAsymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace Lax342547Proofs.ContainerAsymptotics
open Lax342547.ContainerAsymptotics

set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics

/--
---
conclusion: Lax342547.ContainerAsymptotics.container_exponent_little_o
---
-/
theorem container_exponent_little_o (A g : ℕ) (hg : 0 < g) :
    (fun N : ℕ => (exponentBudget A g N : ℝ)) =o[atTop] fun N => (2 : ℝ)^(1000*g*N) := by
  have hbase : ‖(2 : ℝ)^(100*g)‖ < (2 : ℝ)^(1000*g) := by
    rw [Real.norm_eq_abs,abs_of_pos (by positivity)]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have hlarge : 1 < (2 : ℝ)^(1000*g) := one_lt_pow₀ (by norm_num) (by positivity)
  have h₃ := (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt 3 hbase).const_mul_left (8000*(A : ℝ)*g)
  have h₁ := (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt 1 hbase).const_mul_left (4000*(g : ℝ))
  have h₂ := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 2 hlarge).const_mul_left (4*(A : ℝ))
  have h₀ := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 0 hlarge).const_mul_left (2 : ℝ)
  apply (h₃.add h₁ |>.add h₂ |>.add h₀).congr
  · intro N
    simp only [exponentBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_one,pow_zero,← pow_mul]
    ring
  · intro N
    rw [← pow_mul]

/--
---
conclusion: Lax342547.ContainerAsymptotics.eventually_container_exponent
---
-/
theorem eventually_container_exponent (A g : ℕ) (hg : 0 < g) :
    ∀ᶠ N : ℕ in atTop, exponentBudget A g N+2 < 2^(1000*g*N) := by
  have hbound := (Lax342547.ContainerAsymptotics.container_exponent_little_o A g hg).bound (show (0 : ℝ) < 1/4 by norm_num)
  filter_upwards [hbound,eventually_ge_atTop 1] with N hb hN
  have hn : (0 : ℝ) ≤ exponentBudget A g N := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (2 : ℝ)^(1000*g*N) := by positivity
  simp only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_nonneg hp] at hb
  have hbig : (8 : ℕ) ≤ 2^(1000*g*N) := by
    have he : 3 ≤ 1000*g*N := by nlinarith [Nat.mul_pos hg (show 0 < N by omega)]
    exact (show 8 = 2^3 by norm_num).le.trans (Nat.pow_le_pow_right (by norm_num) he)
  have hbigR : (8 : ℝ) ≤ (2 : ℝ)^(1000*g*N) := by exact_mod_cast hbig
  have hh : (exponentBudget A g N : ℝ)+2 < (2 : ℝ)^(1000*g*N) := by linarith
  exact_mod_cast hh

end Lax342547Proofs.ContainerAsymptotics
