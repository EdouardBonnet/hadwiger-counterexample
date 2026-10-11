import Lax342547.ProbabilityScales
import Lax342547.ContainerAsymptotics
import Lax342547.FingerprintScales
import Lax342547.RawToGraph
import Lax342547.SampleScales

namespace Lax342547Proofs.ProbabilityScales
open Lax342547.ProbabilityScales

set_option backward.isDefEq.respectTransparency false
open Lax342547.RawToGraph Lax342547.FingerprintScales Lax342547.ContainerAsymptotics
open Filter

/--
---
conclusion: Lax342547.ProbabilityScales.paper_failure_exponential_budget
---
-/
theorem paper_failure_exponential_budget (v A g N : ℕ) (hg : 0 < g) (hN : 0 < N)
    (hv : v ≤ 2^(A*N^2)) (he : 2*exponentBudget A g N+4 ≤ sampleSize g N) :
    (((v^2+1)^fingerprintLength g N : ℕ) : ℝ)*
      exceptionBudget (sampleSize g N) ((sampleSize g N+199)/200) ((2 : ℝ)^1000) ((2 : ℝ)^(4000*g*N)) ≤
        1/(2 : ℝ)^(sampleSize g N/2) := by
  let m := sampleSize g N
  let k := (m+199)/200
  have hk : m ≤ 200*k := by omega
  have hb₁ := Lax342547.FingerprintScales.vertex_exception_power m k hk
  have hb₂ := Lax342547.FingerprintScales.pair_exception_power g N k hg hN hk
  have hb : exceptionBudget m k ((2 : ℝ)^1000) ((2 : ℝ)^(4000*g*N)) ≤ 2/(2 : ℝ)^m := by
    unfold exceptionBudget
    calc
      _ ≤ 1/(2 : ℝ)^m+1/(2 : ℝ)^m := add_le_add hb₁ hb₂
      _ = _ := by ring
  have hc : (((v^2+1)^fingerprintLength g N : ℕ) : ℝ) ≤ (2 : ℝ)^(exponentBudget A g N) := by
    exact_mod_cast Lax342547.SampleScales.raw_fingerprint_count_bound v A g N hv
  have hbudget := mul_le_mul hc hb
    (Lax342547.RawToGraph.exception_budget_nonneg m k _ _ (by positivity) (by positivity)) (by positivity)
  have hsmall : (2 : ℝ)^(exponentBudget A g N)*(2/(2 : ℝ)^m) ≤ 1/(2 : ℝ)^(m/2) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [one_mul,← pow_succ,← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  exact hbudget.trans hsmall

/--
---
conclusion: Lax342547.ProbabilityScales.eventually_paper_failure_budget
---
-/
theorem eventually_paper_failure_budget (A g : ℕ) (hg : 0 < g) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℕ, v ≤ 2^(A*N^2) →
      (((v^2+1)^fingerprintLength g N : ℕ) : ℝ)*
        exceptionBudget (sampleSize g N) ((sampleSize g N+199)/200)
          ((2 : ℝ)^1000) ((2 : ℝ)^(4000*g*N)) ≤ 1/(2 : ℝ)^(sampleSize g N/2) := by
  have hb := (Lax342547.ContainerAsymptotics.container_exponent_little_o A g hg).bound
    (show (0 : ℝ) < 1/4 by norm_num)
  filter_upwards [hb,eventually_ge_atTop 1] with N hb hN v hv
  have hn : (0 : ℝ) ≤ exponentBudget A g N := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (2 : ℝ)^(1000*g*N) := by positivity
  simp only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_nonneg hp] at hb
  have hbig : (8 : ℕ) ≤ 2^(1000*g*N) := by
    have he : 3 ≤ 1000*g*N := by nlinarith [Nat.mul_pos hg (show 0 < N by omega)]
    exact (show 8 = 2^3 by norm_num).le.trans (Nat.pow_le_pow_right (by norm_num) he)
  have hbigR : (8 : ℝ) ≤ (2 : ℝ)^(1000*g*N) := by exact_mod_cast hbig
  have heR : 2*(exponentBudget A g N : ℝ)+4 ≤ (2 : ℝ)^(1000*g*N) := by linarith
  have he : 2*exponentBudget A g N+4 ≤ sampleSize g N := by exact_mod_cast heR
  exact Lax342547.ProbabilityScales.paper_failure_exponential_budget v A g N hg (by omega) hv he

end Lax342547Proofs.ProbabilityScales
