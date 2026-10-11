import Lax342547.InjectionBudgets
import Lax342547Proofs.MomentBudgets

namespace Lax342547Proofs.InjectionBudgets
open Lax342547.InjectionBudgets

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.InjectionBudgets.amplified_ratio_budget
---
-/
theorem amplified_ratio_budget (h K ℓ t m c N : ℕ) (L gap count : ℝ)
    (hL : 0 ≤ L) (hg : 1/(2 : ℝ)^t ≤ gap)
    (hLc : L ≤ (2 : ℝ)^m) (hc : count ≤ (2 : ℝ)^c) (hcount : 0 ≤ count)
    (hb : m+c+h*K+(2*K+t)*ℓ+N ≤ h*ℓ) :
    count*((L*((2 : ℝ)^(h*K+2*K*ℓ)/(2 : ℝ)^(h*ℓ)))/gap^ℓ) ≤ 1/(2 : ℝ)^N := by
  have hgp : 0 < gap := lt_of_lt_of_le (by positivity) hg
  have hpow : (1/(2 : ℝ)^t)^ℓ ≤ gap^ℓ := pow_le_pow_left₀ (by positivity) hg ℓ
  have hnum : 0 ≤ L*((2 : ℝ)^(h*K+2*K*ℓ)/(2 : ℝ)^(h*ℓ)) := by positivity
  have h₁ := div_le_div_of_nonneg_left hnum (by positivity : 0 < (1/(2 : ℝ)^t)^ℓ) hpow
  have h₂ := mul_le_mul_of_nonneg_left h₁ hcount
  have h₃ : count*((L*((2 : ℝ)^(h*K+2*K*ℓ)/(2 : ℝ)^(h*ℓ)))/(1/(2 : ℝ)^t)^ℓ) ≤
      (2 : ℝ)^c*(((2 : ℝ)^m*((2 : ℝ)^(h*K+2*K*ℓ)/(2 : ℝ)^(h*ℓ)))/(1/(2 : ℝ)^t)^ℓ) := by
    apply mul_le_mul hc
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hLc (by positivity)) (by positivity)
    · positivity
    · positivity
  have he : (2 : ℝ)^c*(((2 : ℝ)^m*((2 : ℝ)^(h*K+2*K*ℓ)/(2 : ℝ)^(h*ℓ)))/(1/(2 : ℝ)^t)^ℓ) =
      (2 : ℝ)^(m+c+h*K+(2*K+t)*ℓ)/(2 : ℝ)^(h*ℓ) := by
    rw [div_pow,one_pow,← pow_mul]
    field_simp
    simp only [← pow_add]
    congr 1
    ring
  exact (h₂.trans h₃).trans (he ▸ Lax342547Proofs.MomentBudgets.power_ratio_bound _ _ _ hb)

/--
---
conclusion: Lax342547.InjectionBudgets.quotient_probe_length
---
-/
theorem quotient_probe_length (K N : ℕ) (hN : 20*(K+1) ≤ N) :
    N ≤ 20*(K+1)*(N/(10*(K+1))) := by
  have hd : 0 < 10*(K+1) := by positivity
  have hr := Nat.mod_lt N hd
  have he := Nat.mod_add_div N (10*(K+1))
  have hq : 2 ≤ N/(10*(K+1)) := (Nat.le_div_iff_mul_le hd).mpr (by nlinarith)
  nlinarith

/--
---
conclusion: Lax342547.InjectionBudgets.early_channel_margin
---
-/
theorem early_channel_margin (K t Cs m h N : ℕ)
    (hh : 2*K+t+20*(K+1)*(Cs+3) ≤ h)
    (hN : 20*(K+1) ≤ N) (hm : m+h*K ≤ N) :
    (m+N)+Cs*N+h*K+(2*K+t)*(N/(10*(K+1)))+N ≤ h*(N/(10*(K+1))) := by
  have hlen := quotient_probe_length K N hN
  have hmul := Nat.mul_le_mul_right (N/(10*(K+1))) hh
  have hp := Nat.mul_le_mul_left (Cs+3) hlen
  nlinarith

/--
---
conclusion: Lax342547.InjectionBudgets.accepting_family_exponential_budget
---
-/
theorem accepting_family_exponential_budget (K t Cs m h N : ℕ) (L gap count : ℝ)
    (hL : 0 ≤ L) (hcount : 0 ≤ count) (hg : 1/(2 : ℝ)^t ≤ gap)
    (hLc : L ≤ (2 : ℝ)^(m+N)) (hc : count ≤ (2 : ℝ)^(Cs*N))
    (hh : 2*K+t+20*(K+1)*(Cs+3) ≤ h)
    (hN : 20*(K+1) ≤ N) (hm : m+h*K ≤ N) :
    count*((L*((2 : ℝ)^(h*K+2*K*(N/(10*(K+1))))/(2 : ℝ)^(h*(N/(10*(K+1))))))/gap^(N/(10*(K+1)))) ≤
      1/(2 : ℝ)^N := by
  exact amplified_ratio_budget h K (N/(10*(K+1))) t (m+N) (Cs*N) N L gap count
    hL hg hLc hc hcount (early_channel_margin K t Cs m h N hh hN hm)

/--
---
conclusion: Lax342547.InjectionBudgets.primal_avoidance_exponent
---
-/
theorem primal_avoidance_exponent (K b h m N : ℕ)
    (hb : b ≤ N/8) (hm : m+h+1 ≤ N/10) :
    m+N/100+b+h+K*(N/(10*(K+1)))+1+N/2 ≤ N := by
  have h₁ := Nat.mul_div_le N 8
  have h₂ := Nat.mul_div_le N 10
  have h₃ := Nat.mul_div_le N 100
  have h₄ := Nat.mul_div_le N 2
  have h₅ := Nat.mul_div_le N (10*(K+1))
  nlinarith

/--
---
conclusion: Lax342547.InjectionBudgets.conditioned_avoidance_budget
---
-/
theorem conditioned_avoidance_budget (K b h m N : ℕ) (M : ℝ)
    (hM : 0 ≤ M) (hMc : M ≤ (2 : ℝ)^m)
    (hb : b ≤ N/8) (hm : m+h+1 ≤ N/10) :
    (M/(1/(2 : ℝ)^(N/100)))*(2*((2 : ℝ)^(b+h+K*(N/(10*(K+1))))/(2 : ℝ)^N)) ≤
      1/(2 : ℝ)^(N/2) := by
  have hmono : (M/(1/(2 : ℝ)^(N/100)))*(2*((2 : ℝ)^(b+h+K*(N/(10*(K+1))))/(2 : ℝ)^N)) ≤
      ((2 : ℝ)^m/(1/(2 : ℝ)^(N/100)))*(2*((2 : ℝ)^(b+h+K*(N/(10*(K+1))))/(2 : ℝ)^N)) := by
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hMc (by positivity)) (by positivity)
  have he : ((2 : ℝ)^m/(1/(2 : ℝ)^(N/100)))*(2*((2 : ℝ)^(b+h+K*(N/(10*(K+1))))/(2 : ℝ)^N)) =
      (2 : ℝ)^(m+N/100+b+h+K*(N/(10*(K+1)))+1)/(2 : ℝ)^N := by
    field_simp
    rw [pow_succ]
    simp only [← pow_add]
    ring
  exact hmono.trans (he ▸ Lax342547Proofs.MomentBudgets.power_ratio_bound _ _ _
    (primal_avoidance_exponent K b h m N hb hm))

end Lax342547Proofs.InjectionBudgets
