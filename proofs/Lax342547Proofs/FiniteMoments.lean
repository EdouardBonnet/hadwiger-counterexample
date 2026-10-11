import Lax342547.FiniteMoments
import Lax342547Proofs.FiniteSampling
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Lax342547Proofs.FiniteMoments
open Lax342547.FiniteMoments

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.FiniteMoments.finite_even_moment
---
-/
theorem finite_even_moment {Ω C : Type} [Fintype Ω] [Fintype C]
    (μ : Ω → ℝ) (ν : C → ℝ) (ψ : Ω → ℝ) (χ : Ω → C → ℝ) (t : ℕ) :
    (∑ c, ν c*|∑ x, μ x*ψ x*χ x c|^(2*t)) =
      ∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample*
        (∏ i, ψ (sample i))*(∑ c, ν c*∏ i, χ (sample i) c) := by
  classical
  simp_rw [Even.pow_abs (even_two_mul t),Fintype.sum_pow,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sample _
  apply Finset.sum_congr rfl
  intro c _
  simp only [Finset.prod_mul_distrib,productLaw]
  ring

/--
---
conclusion: Lax342547.FiniteMoments.weighted_character_moment_bound
---
-/
theorem weighted_character_moment_bound {Ω C : Type} [Fintype Ω] [Fintype C]
    (μ : Ω → ℝ) (ν : C → ℝ) (ψ : Ω → ℝ) (χ : Ω → C → ℝ) (t : ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hψ : ∀ x, |ψ x| ≤ 1)
    (hχ : ∀ sample : Fin (2*t) → Ω, 0 ≤ ∑ c, ν c*∏ i, χ (sample i) c) :
    (∑ c, ν c*|∑ x, μ x*ψ x*χ x c|^(2*t)) ≤
      ∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample*
        (∑ c, ν c*∏ i, χ (sample i) c) := by
  classical
  rw [finite_even_moment]
  apply Finset.sum_le_sum
  intro sample _
  have hp : (∏ i, ψ (sample i)) ≤ 1 := by
    calc
      _ ≤ |∏ i, ψ (sample i)| := le_abs_self _
      _ = ∏ i, |ψ (sample i)| := Finset.abs_prod _ _
      _ ≤ ∏ i : Fin (2*t), (1 : ℝ) := Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hψ _)
      _ = 1 := by simp
  have hm : 0 ≤ productLaw (fun _ : Fin (2*t) => μ) sample := Finset.prod_nonneg (fun i _ => hμ _)
  nlinarith [hχ sample,mul_nonneg hm (hχ sample)]

end Lax342547Proofs.FiniteMoments
