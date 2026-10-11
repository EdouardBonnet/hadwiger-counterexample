import Lax342547.SampleScales
import Lax342547.ContainerAsymptotics
import Lax342547.FingerprintScales
import Lax342547.RawToGraph

namespace Lax342547Proofs.SampleScales
open Lax342547.SampleScales

set_option backward.isDefEq.respectTransparency false
open Lax342547.RawToGraph Lax342547.FingerprintScales Lax342547.ContainerAsymptotics
open Filter

/--
---
conclusion: Lax342547.SampleScales.raw_alphabet_bound
---
-/
theorem raw_alphabet_bound (v A N : ℕ) (hv : v ≤ 2^(A*N^2)) :
    v^2+1 ≤ 2^(2*A*N^2+1) := by
  have hh := Nat.pow_le_pow_left hv 2
  have hpow : (2^(A*N^2))^2 = 2^(2*A*N^2) := by rw [← pow_mul]; congr 1; ring
  rw [hpow] at hh
  have hone : 1 ≤ 2^(2*A*N^2) := Nat.one_le_pow _ _ (by omega)
  rw [pow_add,pow_one]
  omega

/--
---
conclusion: Lax342547.SampleScales.raw_fingerprint_count_bound
---
-/
theorem raw_fingerprint_count_bound (v A g N : ℕ) (hv : v ≤ 2^(A*N^2)) :
    (v^2+1)^fingerprintLength g N ≤ 2^(exponentBudget A g N) := by
  have hh := Nat.pow_le_pow_left (Lax342547.SampleScales.raw_alphabet_bound v A N hv) (fingerprintLength g N)
  simpa only [← pow_mul,exponentBudget,fingerprintLength] using hh

/--
---
conclusion: Lax342547.SampleScales.paper_sampling_budget
---
-/
theorem paper_sampling_budget (v A g N : ℕ) (hg : 0 < g) (hN : 0 < N)
    (hv : v ≤ 2^(A*N^2)) (he : exponentBudget A g N+2 < sampleSize g N) :
    (((v^2+1)^fingerprintLength g N : ℕ) : ℝ)*
      exceptionBudget (sampleSize g N) ((sampleSize g N+199)/200) ((2 : ℝ)^1000) ((2 : ℝ)^(4000*g*N)) < 1 := by
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
  have hsmall : (2 : ℝ)^(exponentBudget A g N)*(2/(2 : ℝ)^m) < 1 := by
    rw [← mul_div_assoc]
    apply (div_lt_one (by positivity)).mpr
    rw [← pow_succ]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  exact hbudget.trans_lt hsmall

/--
---
conclusion: Lax342547.SampleScales.eventually_paper_sampling_budget
---
-/
theorem eventually_paper_sampling_budget (A g : ℕ) (hg : 0 < g) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℕ, v ≤ 2^(A*N^2) →
      (((v^2+1)^fingerprintLength g N : ℕ) : ℝ)*
        exceptionBudget (sampleSize g N) ((sampleSize g N+199)/200)
          ((2 : ℝ)^1000) ((2 : ℝ)^(4000*g*N)) < 1 := by
  filter_upwards [Lax342547.ContainerAsymptotics.eventually_container_exponent A g hg,
    eventually_ge_atTop 1] with N he hN v hv
  exact Lax342547.SampleScales.paper_sampling_budget v A g N hg (by omega) hv he

end Lax342547Proofs.SampleScales
