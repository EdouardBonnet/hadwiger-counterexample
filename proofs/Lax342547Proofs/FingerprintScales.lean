import Lax342547.FingerprintScales
import Lax342547Proofs.RawToGraph
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecificLimits.Normed

namespace Lax342547Proofs.FingerprintScales
open Lax342547.FingerprintScales

set_option backward.isDefEq.respectTransparency false
open Lax342547.RawToGraph
open Filter

/--
---
conclusion: Lax342547.FingerprintScales.logarithmic_progress
---
-/
theorem logarithmic_progress (ε : ℝ) (_hε : 0 < ε) (hε1 : ε < 1) : ε ≤ -Real.log (1-ε) := by
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1-ε)
  linarith

/--
---
conclusion: Lax342547.FingerprintScales.paper_fingerprint_length
---
-/
theorem paper_fingerprint_length (g N : ℕ) (hg : 0 < g) (hN : 0 < N) :
    Real.log ((2 : ℝ)^(4000*g*N))/(-Real.log (1-1/(2 : ℝ)^(100*g*N)))+1 ≤
      fingerprintLength g N := by
  have he : 0 < 1/(2 : ℝ)^(100*g*N) := by positivity
  have he1 : 1/(2 : ℝ)^(100*g*N) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by positivity)
  have hp := logarithmic_progress _ he he1
  have hlog : 0 ≤ Real.log ((2 : ℝ)^(4000*g*N)) := by
    rw [Real.log_pow]
    positivity
  have hdiv := div_le_div_of_nonneg_left hlog he hp
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hn : (0 : ℝ) ≤ (4000*g*N : ℕ) := Nat.cast_nonneg _
  have hbound : Real.log ((2 : ℝ)^(4000*g*N))/(1/(2 : ℝ)^(100*g*N)) ≤
      (4000*g*N : ℝ)*(2 : ℝ)^(100*g*N) := by
    rw [Real.log_pow,div_div_eq_mul_div,div_one]
    have hh := mul_le_mul_of_nonneg_left hlog2 hn
    rw [mul_one] at hh
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hh) (by positivity)
  have hh := hdiv.trans hbound
  simp only [fingerprintLength,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  linarith

/--
---
conclusion: Lax342547.FingerprintScales.paper_sample_ceiling
---
-/
theorem paper_sample_ceiling (m : ℕ) : 200*((m+199)/200-1) < m ∨ m = 0 := by
  omega

/--
---
conclusion: Lax342547.FingerprintScales.vertex_exception_power
---
-/
theorem vertex_exception_power (m k : ℕ) (hk : m ≤ 200*k) :
    (m.choose k : ℝ)*(1/(2 : ℝ)^1000)^k ≤ 1/(2 : ℝ)^m := by
  have hchoose : (m.choose k : ℝ) ≤ (2 : ℝ)^m := by
    exact_mod_cast Nat.choose_le_two_pow m k
  have hp : (2 : ℝ)^(2*m) ≤ (2 : ℝ)^(1000*k) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h : (m.choose k : ℝ)*(2 : ℝ)^m ≤ (2 : ℝ)^(1000*k) := by
    calc
      _ ≤ (2 : ℝ)^m*(2 : ℝ)^m := mul_le_mul_of_nonneg_right hchoose (by positivity)
      _ = (2 : ℝ)^(2*m) := by rw [two_mul,pow_add]
      _ ≤ _ := hp
  rw [one_div_pow,← pow_mul,mul_one_div]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using h)

/--
---
conclusion: Lax342547.FingerprintScales.pair_exception_power
---
-/
theorem pair_exception_power (g N k : ℕ) (hg : 0 < g) (hN : 0 < N)
    (hk : sampleSize g N ≤ 200*k) :
    (sampleSize g N : ℝ)^(2*k)*(1/(2 : ℝ)^(4000*g*N))^k ≤ 1/(2 : ℝ)^(sampleSize g N) := by
  have hgN : 1 ≤ g*N := Nat.mul_pos hg hN
  have hsmall : 200*k ≤ 2000*g*N*k := by
    apply Nat.mul_le_mul_right k
    nlinarith
  have hexp : 2000*g*N*k+sampleSize g N ≤ 4000*g*N*k := by nlinarith [hk.trans hsmall]
  have hp : (2 : ℝ)^(2000*g*N*k+sampleSize g N) ≤ (2 : ℝ)^(4000*g*N*k) :=
    pow_le_pow_right₀ (by norm_num) hexp
  simp only [sampleSize,Nat.cast_pow,Nat.cast_ofNat,one_div_pow,← pow_mul,mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul,← pow_add]
  convert hp using 1
  congr 1
  simp only [sampleSize]
  ring

end Lax342547Proofs.FingerprintScales
