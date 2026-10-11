import Lax342547.PreparedInjectionScale
import Lax342547.InjectionAsymptotics
import Lax342547.InjectionThresholds

namespace Lax342547Proofs.PreparedInjectionScale

open Lax342547.PreparedInjection Filter

/--
---
conclusion: Lax342547.PreparedInjectionScale.exists_prepared_parameters
---
-/
theorem exists_prepared_parameters (K Cs J : ℕ) (ε : ℝ) (hJ : 0 < J) (hε : 0 < ε) :
    ∃ t h : ℕ,∀ c : ℕ,∃ N₀ : ℕ,∀ N : ℕ,N₀ ≤ N → ∀ p m : ℕ,
      p ≤ N/8 → m ≤ N/100 →
      Budget K m t Cs p h N (ε/(2*J)) ∧
      (J : ℝ)*(1/(2 : ℝ)^(N/100)+1/(2 : ℝ)^N) ≤ (ε/2)/(N : ℝ)^c := by
  have hJr : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  obtain ⟨t,h,hgap,hchannel,hrest⟩ := Lax342547.InjectionThresholds.exists_early_parameters
    K Cs (ε/(2*J)) (by positivity)
  refine ⟨t,h,?_⟩
  intro c
  have htail := Lax342547.InjectionAsymptotics.eventually_relative_exception
    c 100 (by norm_num) (J : ℝ) (ε/2) (by positivity) (by positivity)
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp htail
  obtain ⟨N₂,hN₂⟩ := hrest 0
  refine ⟨max N₁ (max N₂ (100*(h*K+h+1))),?_⟩
  intro N hN p m hp hm
  have h₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have h₂ : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have h₃ : 100*(h*K+h+1) ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hprobes,hconstant,hdensity,hsmall⟩ := hN₂ N h₂
  refine ⟨⟨hgap,by omega,hp,by omega,hchannel,hprobes,by omega,hsmall⟩,hN₁ N h₁⟩

end Lax342547Proofs.PreparedInjectionScale
