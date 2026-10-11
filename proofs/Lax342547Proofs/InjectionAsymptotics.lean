import Lax342547.InjectionAsymptotics
import Mathlib.Analysis.SpecificLimits.Normed

namespace Lax342547Proofs.InjectionAsymptotics
open Lax342547.InjectionAsymptotics

set_option backward.isDefEq.respectTransparency false
open Filter

/--
---
conclusion: Lax342547.InjectionAsymptotics.polynomial_dyadic_floor_tends_zero
---
-/
theorem polynomial_dyadic_floor_tends_zero (c d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (N : ℝ)^c/(2 : ℝ)^(N/d)) atTop (nhds 0) := by
  have hdiv : Tendsto (fun N : ℕ => N/d) atTop atTop := by
    change Filter.map (fun N : ℕ => N/d) atTop ≤ atTop
    rw [Filter.map_div_atTop_eq_nat d hd]
  have hplus : Tendsto (fun N : ℕ => N/d+1) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_add_right (N/d) 1) hdiv
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt c (by norm_num : (1 : ℝ) < 2)).comp hplus
  have hu : Tendsto (fun N : ℕ => (2*(d : ℝ)^c)*(((N/d+1 : ℕ) : ℝ)^c/(2 : ℝ)^(N/d+1))) atTop (nhds 0) := by
    simpa using ht.const_mul (2*(d : ℝ)^c)
  apply squeeze_zero (fun N => by positivity) ?_ hu
  intro N
  have hr := Nat.mod_lt N hd
  have he := Nat.mod_add_div N d
  have hn : N ≤ d*(N/d+1) := by nlinarith
  have hc : (N : ℝ)^c ≤ ((d : ℝ)*((N/d+1 : ℕ) : ℝ))^c :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hn) c
  have hb := div_le_div_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ 2^(N/d))
  have hrewrite : ((d : ℝ)*((N/d+1 : ℕ) : ℝ))^c/(2 : ℝ)^(N/d) =
      (2*(d : ℝ)^c)*(((N/d+1 : ℕ) : ℝ)^c/(2 : ℝ)^(N/d+1)) := by
    rw [mul_pow,pow_succ]
    ring
  exact hb.trans_eq hrewrite

/--
---
conclusion: Lax342547.InjectionAsymptotics.eventually_relative_exception
---
-/
theorem eventually_relative_exception (c d : ℕ) (hd : 0 < d) (J ε : ℝ)
    (hJ : 0 ≤ J) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,J*(1/(2 : ℝ)^(N/d)+1/(2 : ℝ)^N) ≤ ε/(N : ℝ)^c := by
  have ht := (Lax342547.InjectionAsymptotics.polynomial_dyadic_floor_tends_zero c d hd).const_mul (2*J)
  have he : ∀ᶠ N : ℕ in atTop, (2*J)*((N : ℝ)^c/(2 : ℝ)^(N/d)) < ε := by
    apply (tendsto_order.1 (by simpa using ht)).2 ε hε
  filter_upwards [he,eventually_ge_atTop 1] with N he hN
  have hpow : 1/(2 : ℝ)^N ≤ 1/(2 : ℝ)^(N/d) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (Nat.div_le_self _ _)
  have htail : J*(1/(2 : ℝ)^(N/d)+1/(2 : ℝ)^N) ≤ 2*J/(2 : ℝ)^(N/d) := by
    calc
      _ ≤ J*(1/(2 : ℝ)^(N/d)+1/(2 : ℝ)^(N/d)) := mul_le_mul_of_nonneg_left (by linarith) hJ
      _ = 2*J/(2 : ℝ)^(N/d) := by ring
  have hp : (0 : ℝ) < (N : ℝ)^c := pow_pos (by exact_mod_cast hN) _
  have hb : 2*J/(2 : ℝ)^(N/d) ≤ ε/(N : ℝ)^c := by
    apply (le_div_iff₀ hp).mpr
    have hre : (2*J/(2 : ℝ)^(N/d))*(N : ℝ)^c = (2*J)*((N : ℝ)^c/(2 : ℝ)^(N/d)) := by ring
    rw [hre]
    exact he.le
  exact htail.trans hb

/--
---
conclusion: Lax342547.InjectionAsymptotics.relative_union_budget
---
-/
theorem relative_union_budget (J : ℕ) (ε a τ bad : ℝ) (hJ : 0 < J) (hε : 0 ≤ ε)
    (ha : 0 ≤ a) (hbad : bad ≤ J*((ε/(2*J))*a+τ)) (htail : J*τ ≤ (ε/2)*a) :
    bad ≤ ε*a := by
  have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have he : (J : ℝ)*((ε/(2*J))*a+τ) = (ε/2)*a+J*τ := by field_simp
  rw [he] at hbad
  linarith

end Lax342547Proofs.InjectionAsymptotics
