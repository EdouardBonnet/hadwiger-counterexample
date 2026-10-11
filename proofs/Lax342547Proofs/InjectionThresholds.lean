import Lax342547.InjectionThresholds

namespace Lax342547Proofs.InjectionThresholds
open Lax342547.InjectionThresholds

set_option backward.isDefEq.respectTransparency false
open Filter

/--
---
conclusion: Lax342547.InjectionThresholds.exists_dyadic_gap
---
-/
theorem exists_dyadic_gap (η : ℝ) (hη : 0 < η) : ∃ t : ℕ,1/(2 : ℝ)^t ≤ η/2 := by
  have ht : Tendsto (fun n : ℕ => 1/(2 : ℝ)^n) atTop (nhds 0) := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_div_atTop 1
  have he : ∀ᶠ n : ℕ in atTop,1/(2 : ℝ)^n < η/2 :=
    (tendsto_order.1 ht).2 _ (by linarith)
  obtain ⟨t,ht⟩ := he.exists
  exact ⟨t,ht.le⟩

/--
---
conclusion: Lax342547.InjectionThresholds.exists_early_parameters
---
-/
theorem exists_early_parameters (K Cs : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ t h : ℕ,1/(2 : ℝ)^t ≤ η/2 ∧ 2*K+t+20*(K+1)*(Cs+3) ≤ h ∧
      ∀ m : ℕ,∃ N₀ : ℕ,∀ N : ℕ,N₀ ≤ N →
        20*(K+1) ≤ N ∧ m+h*K ≤ N ∧ m+h+1 ≤ N/10 ∧
        1/(2 : ℝ)^(N/2) ≤ η/2 := by
  obtain ⟨t,ht⟩ := Lax342547.InjectionThresholds.exists_dyadic_gap η hη
  let h := 2*K+t+20*(K+1)*(Cs+3)
  refine ⟨t,h,ht,le_rfl,?_⟩
  intro m
  refine ⟨20*(K+1)+(m+h*K)+10*(m+h+1)+2*t,?_⟩
  intro N hN
  refine ⟨by omega,by omega,by omega,?_⟩
  have hex : t ≤ N/2 := by omega
  exact (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hex)).trans ht

end Lax342547Proofs.InjectionThresholds
