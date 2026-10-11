import Lax342547.CommonTestTransfer
import Lax342547Proofs.EmpiricalVariance

namespace Lax342547Proofs.CommonTestTransfer
open Lax342547.RelativeEntropy
open scoped BigOperators

 theorem probability_mean_square {Ω : Type} [Fintype Ω] (σ : Ω → ℝ)
    (hσ : Probability σ) (f : Ω → ℝ) :
    (∑ o,σ o*f o)^2 ≤ ∑ o,σ o*(f o)^2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun o => Real.sqrt (σ o)) (fun o => Real.sqrt (σ o)*f o)
  have he (o : Ω) : Real.sqrt (σ o)*(Real.sqrt (σ o)*f o) = σ o*f o := by
    rw [← mul_assoc,← pow_two,Real.sq_sqrt (hσ.1 o)]
  simp_rw [he,mul_pow,Real.sq_sqrt (hσ.1 _)] at hc
  simpa only [hσ.2,one_mul] using hc

/--
---
conclusion: Lax342547.CommonTestTransfer.mean_comparison
---
-/
theorem mean_comparison {Ω : Type} [Fintype Ω] (ρ σ F : Ω → ℝ)
    (hσ : Probability σ) (L ε m : ℝ) (hL : 0 ≤ L)
    (hcap : ∀ o,σ o ≤ L*ρ o)
    (hvar : (∑ o,ρ o*(F o-m)^2) ≤ ε) :
    |(∑ o,σ o*F o)-m| ≤ Real.sqrt (L*ε) := by
  have hc := probability_mean_square σ hσ (fun o => F o-m)
  have he : (∑ o,σ o*(F o-m)) = (∑ o,σ o*F o)-m := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hσ.2,one_mul]
  rw [he] at hc
  have hv : (∑ o,σ o*(F o-m)^2) ≤ L*ε := by
    calc
      _ ≤ ∑ o,(L*ρ o)*(F o-m)^2 := by
        exact Finset.sum_le_sum (fun o _ => mul_le_mul_of_nonneg_right (hcap o) (sq_nonneg _))
      _ = L*(∑ o,ρ o*(F o-m)^2) := by simp only [Finset.mul_sum,mul_assoc]
      _ ≤ L*ε := mul_le_mul_of_nonneg_left hvar hL
  exact Real.abs_le_sqrt (hc.trans hv)

/--
---
conclusion: Lax342547.CommonTestTransfer.success_transfer
---
-/
theorem success_transfer {Ω : Type} [Fintype Ω] (ρ σ F : Ω → ℝ)
    (hσ : Probability σ) (L ε m η : ℝ) (hL : 0 ≤ L)
    (hcap : ∀ o,σ o ≤ L*ρ o)
    (hvar : (∑ o,ρ o*(F o-m)^2) ≤ ε)
    (hsuccess : 1-η ≤ ∑ o,σ o*F o) :
    1-η-Real.sqrt (L*ε) ≤ m := by
  have hh := (le_abs_self _).trans (mean_comparison ρ σ F hσ L ε m hL hcap hvar)
  linarith

end Lax342547Proofs.CommonTestTransfer
