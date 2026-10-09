import Lax342547.PeelingBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Lax342547Proofs.PeelingBudget

open scoped ENNReal

theorem rpow_strict_exponent {a b : ℝ} (h : (2 : ℝ≥0∞) ^ a < (2 : ℝ≥0∞) ^ b) : a < b := by
  by_contra hn
  exact not_lt_of_ge (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_not_gt hn)) h

/--
---
conclusion: Lax342547.PeelingBudget.rank_comparison
---
Combine powers of two in the strict lower and weak upper mass bounds.
Monotonicity of the exponential and positivity of N give the exact
comparison (zeta-epsilon)u < D+zeta.
-/
theorem rank_comparison (D ζ ε : ℝ) (N u : ℕ) (hN : 0 < N) (m : ℝ≥0∞)
    (hlower : (2 : ℝ≥0∞) ^ (-(ζ * N)) * ((2 : ℝ≥0∞) ^ (-((1 - ζ) * N))) ^ u < m)
    (hupper : m ≤ (2 : ℝ≥0∞) ^ (D * N) * ((2 : ℝ≥0∞) ^ (-((1 - ε) * N))) ^ u) :
    (ζ - ε) * u < D + ζ := by
  have h := hlower.trans_le hupper
  rw [← ENNReal.rpow_mul_natCast, ← ENNReal.rpow_mul_natCast,
    ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num),
    ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)] at h
  have he := rpow_strict_exponent h
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : ((ζ - ε) * u) * N < (D + ζ) * N := by nlinarith
  exact (mul_lt_mul_iff_left₀ hN').mp hc

/--
---
conclusion: Lax342547.PeelingBudget.conservative_rank_bound
---
When epsilon is at most a quarter of zeta, the exact comparison gives
the paper's conservative 4(D+1)/zeta bound on cumulative new rank.
-/
theorem conservative_rank_bound (D ζ ε : ℝ) (u : ℕ)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hε : ε ≤ ζ / 4)
    (h : (ζ - ε) * u < D + ζ) : (u : ℝ) < 4 * (D + 1) / ζ := by
  apply (lt_div_iff₀ hζ).mpr
  have hu : (0 : ℝ) ≤ u := by positivity
  have hm := mul_le_mul_of_nonneg_right hε hu
  nlinarith

/--
---
conclusion: Lax342547.PeelingBudget.density_cost
---
The strict leaf mass lower bound is at least 2^(-(K+1)N) when u is at
most K. Division by the retained mass therefore costs at most the stated
uniform exponential density factor.
-/
theorem density_cost (D ζ : ℝ) (N u K : ℕ) (hζ : 0 ≤ ζ) (hζ₁ : ζ ≤ 1)
    (hu : u ≤ K) (m : ℝ≥0∞)
    (hm : (2 : ℝ≥0∞) ^ (-(ζ * N)) * ((2 : ℝ≥0∞) ^ (-((1 - ζ) * N))) ^ u ≤ m) :
    (2 : ℝ≥0∞) ^ (D * N) / m ≤ (2 : ℝ≥0∞) ^ ((D + K + 1) * N) := by
  have hu' : (u : ℝ) ≤ K := by exact_mod_cast hu
  have hn : (0 : ℝ) ≤ N := by positivity
  have hcost : ζ + (1 - ζ) * u ≤ (K : ℝ) + 1 := by
    have hu0 : (0 : ℝ) ≤ u := by positivity
    nlinarith
  rw [← ENNReal.rpow_mul_natCast, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)] at hm
  calc
    _ ≤ (2 : ℝ≥0∞) ^ (D * N) /
        (2 : ℝ≥0∞) ^ (-(ζ * N) + -((1 - ζ) * N) * u) :=
      mul_le_mul_of_nonneg_left (ENNReal.inv_le_inv.mpr hm) zero_le
    _ = (2 : ℝ≥0∞) ^ (D * N - (-(ζ * N) + -((1 - ζ) * N) * u)) := by
      rw [ENNReal.rpow_sub _ _ (by norm_num) (by norm_num)]
    _ ≤ _ := ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have hc := mul_le_mul_of_nonneg_right hcost hn
      nlinarith)

end Lax342547Proofs.PeelingBudget
