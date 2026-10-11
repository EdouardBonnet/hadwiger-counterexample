import Lax342547.MomentTails
import Lax342547Proofs.FiniteMoments

namespace Lax342547Proofs.MomentTails
open Lax342547.MomentTails

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.MomentTails.finite_moment_markov
---
-/
theorem finite_moment_markov {C : Type} [Fintype C] (ν : C → ℝ) (f : C → ℝ)
    (a : ℝ) (n : ℕ) (hν : ∀ c, 0 ≤ ν c) (ha : 0 < a) :
    cellMass ν (fun c => a ≤ |f c|) ≤ (∑ c, ν c*|f c|^n)/a^n := by
  classical
  have hp : 0 < a^n := pow_pos ha n
  apply (le_div_iff₀ hp).mpr
  unfold cellMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : a ≤ |f c|
  · simp only [hc,ite_true]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hc n) (hν c)
  · simp only [hc,ite_false,zero_mul]
    exact mul_nonneg (hν c) (pow_nonneg (abs_nonneg _) n)

/--
---
conclusion: Lax342547.MomentTails.rank_moment_split
---
-/
theorem rank_moment_split {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (rank : Ω → ℕ) (h R : ℕ) (hμ : Probability μ) :
    (∑ x, μ x/(2 : ℝ)^(h*rank x)) ≤
      cellMass μ (fun x => rank x < R)+1/(2 : ℝ)^(h*R) := by
  classical
  have hs : (∑ x, μ x/(2 : ℝ)^(h*rank x)) ≤
      ∑ x, ((if rank x < R then μ x else 0)+μ x/(2 : ℝ)^(h*R)) := by
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : rank x < R
    · simp only [hx,ite_true]
      have hone : (1 : ℝ) ≤ 2^(h*rank x) := one_le_pow₀ (by norm_num)
      have hle : μ x/(2 : ℝ)^(h*rank x) ≤ μ x := div_le_self (hμ.1 x) hone
      exact hle.trans (le_add_of_nonneg_right (div_nonneg (hμ.1 x) (by positivity)))
    · simp only [hx,ite_false,zero_add]
      apply div_le_div_of_nonneg_left (hμ.1 x) (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left h (by omega))
  calc
    _ ≤ _ := hs
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.sum_div,hμ.2]
      congr 1
      unfold cellMass
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : rank x < R <;> simp [hx]

end Lax342547Proofs.MomentTails
